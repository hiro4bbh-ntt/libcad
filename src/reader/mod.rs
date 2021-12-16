//! The reader module.

use std::fmt;

/// A position in a file.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FilePos<'a> {
    pub filename: &'a str,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for FilePos<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.filename, self.line, self.column)
    }
}

/// A reader on a string.
pub struct StringReader<'a> {
    source: &'a str,
    pos: FilePos<'a>,
    ptr: usize,
}

impl<'a> StringReader<'a> {
    /// Returns a new reader on the given source text and the file name.
    pub fn new(source: &'a str, filename: &'a str) -> StringReader<'a> {
        StringReader {
            source,
            pos: FilePos {
                filename,
                line: 1,
                column: 1,
            },
            ptr: 0,
        }
    }
    /// Returns the source text.
    pub fn source(&self) -> &'a str {
        self.source
    }
    /// Returns the current file position.
    pub fn pos(&self) -> &FilePos<'a> {
        &self.pos
    }
    /// Returns the current pointer in the source text.
    pub fn ptr(&self) -> usize {
        self.ptr
    }
    /// Peeks a character from the current pointer.
    pub fn peek_char(&mut self) -> Option<char> {
        self.source[self.ptr..].chars().next()
    }
    /// Returns a read character from the current pointer, and advances the pointer.
    pub fn read_char(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.pos.column += 1;
        if c == '\n' {
            self.pos.line += 1;
            self.pos.column = 1;
        }
        self.ptr += c.len_utf8();
        Some(c)
    }
}

pub mod sexpr;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn string_reader() {
        let source = "abc\nあいう";
        let filename = "source.txt";
        let mut reader = StringReader::new(source, filename);
        assert_eq!(reader.source(), source);
        let expected_actions = vec![
            ((None, 1, 1, 0), "none"),
            ((Some('a'), 1, 2, 1), "read"),
            ((Some('b'), 1, 2, 1), "peek"),
            ((Some('b'), 1, 3, 2), "read"),
            ((Some('c'), 1, 4, 3), "read"),
            ((Some('\n'), 2, 1, 4), "read"),
            ((Some('あ'), 2, 1, 4), "peek"),
            ((Some('あ'), 2, 2, 7), "read"),
            ((Some('い'), 2, 3, 10), "read"),
            ((Some('う'), 2, 4, 13), "read"),
            ((None, 2, 4, 13), "read"),
            ((None, 2, 4, 13), "read"),
        ];
        for (i, (expected, action)) in expected_actions.into_iter().enumerate() {
            match action {
                "none" => {}
                "peek" => {
                    assert_eq!(expected.0, reader.peek_char(), "#{}", i);
                }
                "read" => {
                    assert_eq!(expected.0, reader.read_char(), "#{}", i);
                }
                _ => unreachable!("{}", action),
            }
            let pos = FilePos {
                filename: filename,
                line: expected.1,
                column: expected.2,
            };
            assert_eq!(reader.pos(), &pos, "#{}", i);
            assert_eq!(reader.ptr(), expected.3, "#{}", i);
        }
    }
}
