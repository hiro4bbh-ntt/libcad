//! The S-expression module.

use crate::fmt::DisplayIter;
use crate::reader::StringReader;
use crate::symbol::Ident;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Deref, DerefMut};

/// A S-expression.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SExpr {
    /// A 64-bit integer.
    I64(i64),
    /// A 64-bit unsigned integer.
    U64(u64),
    /// A string.
    String(String),
    /// A identifier symbol.
    Symbol(Ident),
    /// A list of S-expressions.
    List(Vec<SExpr>),
}

impl SExpr {
    /// Returns a parsed S-expression from the given source text.
    pub fn try_parse(source: &str) -> Result<SExpr, String> {
        let mut parser = Parser::new(source, "input")?;
        match parser.parse()? {
            Some(sexpr) => Ok(sexpr),
            None => Err("expected sexpr".to_string()),
        }
    }
    /// Returns a parsed S-expression from the given source text.
    /// If any error happens, this panics.
    pub fn parse(source: &str) -> SExpr {
        SExpr::try_parse(source).unwrap()
    }
    /// Returns the command name and arguments.
    pub fn try_to_cmd(&self) -> Option<(Ident, &[SExpr])> {
        if let SExpr::List(list) = self {
            if let Some(SExpr::Symbol(name)) = list.get(0) {
                return Some((*name, &list[1..]));
            }
        }
        None
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            SExpr::I64(n) => write!(f, "{:+}", n),
            SExpr::U64(n) => write!(f, "{:#x}", n),
            SExpr::String(s) => write!(f, "{:?}", s),
            SExpr::Symbol(s) => write!(f, "{}", s),
            SExpr::List(l) => write!(f, "{}", DisplayIter("(", l.iter(), " ", ")")),
        }
    }
}

/// The macro environment.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MacroEnv(BTreeMap<Ident, (Vec<Ident>, SExpr)>);

impl MacroEnv {
    /// Returns a new empty macro environment.
    pub fn empty() -> MacroEnv {
        MacroEnv(BTreeMap::new())
    }
    /// Returns the length.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Returns `true` if containing the given key.
    pub fn contains_key(&self, name: &Ident) -> bool {
        self.0.contains_key(name)
    }
    /// Returns the macro arguments and body by name.
    pub fn get(&self, name: &Ident) -> Option<&(Vec<Ident>, SExpr)> {
        self.0.get(name)
    }
    /// Inserts the given macro name, arguments and body.
    pub fn insert(&mut self, name: Ident, args: Vec<Ident>, body: SExpr) -> Result<(), String> {
        if self.contains_key(&name) {
            return Err(format!("{} is already defined", name));
        }
        self.0.insert(name, (args, body));
        Ok(())
    }
    /// Inserts a parsed macro.
    pub fn parse_insert(&mut self, expr: &SExpr) -> Result<bool, String> {
        if let Some((ident!("define"), args)) = expr.try_to_cmd() {
            if args.len() < 3 {
                return Err(format!("define: takes 3 args, but got {} args", args.len()));
            }
            let name = match &args[0] {
                SExpr::Symbol(name) => *name,
                _ => return Err("define: #1 arg must be symbol".to_string()),
            };
            let arg0 = match &args[1] {
                SExpr::List(list) => list,
                _ => return Err("define: #2 arg must be list".to_string()),
            };
            let mut fargs = Vec::with_capacity(arg0.len());
            for arg in arg0 {
                match arg {
                    SExpr::Symbol(name) => {
                        if fargs.contains(name) {
                            return Err(format!("define: formal argument {} is redefined", name));
                        }
                        fargs.push(*name);
                    }
                    _ => return Err(format!("define: formal argument {} must be symbol", arg)),
                }
            }
            self.insert(name, fargs, args[2].clone())?;
            return Ok(true);
        }
        Ok(false)
    }
    fn do_apply(&self, expr: &SExpr, ctx: &BTreeMap<Ident, SExpr>) -> SExpr {
        match expr {
            SExpr::Symbol(name) => match ctx.get(name) {
                Some(expr) => expr.clone(),
                None => expr.clone(),
            },
            SExpr::List(list) if !list.is_empty() => {
                if let SExpr::Symbol(name) = &list[0] {
                    if let Some((fargs, body)) = self.get(name) {
                        if fargs.len() == list.len() - 1 {
                            let mut newctx = BTreeMap::new();
                            for (i, farg) in fargs.iter().enumerate() {
                                let arg = self.do_apply(&list[1 + i], ctx);
                                newctx.insert(*farg, arg);
                            }
                            return self.do_apply(body, &newctx);
                        }
                    }
                }
                let mut newlist = Vec::with_capacity(list.len());
                for elem in list {
                    newlist.push(self.do_apply(elem, ctx));
                }
                SExpr::List(newlist)
            }
            _ => expr.clone(),
        }
    }
    /// Returns a S-expression applied by the macros.
    pub fn apply(&self, expr: &SExpr) -> SExpr {
        self.do_apply(expr, &BTreeMap::new())
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    None,
    I64(i64),
    U64(u64),
    String(String),
    Symbol(Ident),
    LParen,
    RParen,
}

/// A S-expression parser.
pub struct Parser<'a> {
    reader: StringReader<'a>,
    tk: Token,
}

impl<'a> Parser<'a> {
    /// Returns a new S-expression parser on the given source text and the file name.
    pub fn new(source: &'a str, filename: &'a str) -> Result<Parser<'a>, String> {
        let mut parser = Parser {
            reader: StringReader::new(source, filename),
            tk: Token::None,
        };
        match parser.read_token() {
            Ok(_) => Ok(parser),
            Err(err) => Err(format!("{}: {}", parser.pos(), err)),
        }
    }
    fn read_number(&mut self) -> Result<&Token, String> {
        let start = self.ptr();
        let (with_sign, is_hex) = match self.peek_char() {
            Some('+') | Some('-') => {
                self.read_char();
                (true, false)
            }
            Some('0') => {
                self.read_char();
                match self.peek_char() {
                    Some('x') => {
                        self.read_char();
                        (false, true)
                    }
                    _ => (false, false),
                }
            }
            _ => (false, false),
        };
        while let Some(c) = self.peek_char() {
            match c {
                '0'..='9' => {
                    self.read_char();
                }
                'A'..='F' | 'a'..='f' => match is_hex {
                    true => {
                        self.read_char();
                    }
                    false => break,
                },
                _ => break,
            }
        }
        let s = &self.source()[start..self.ptr()];
        match s {
            "+" | "-" => {
                self.tk = Token::Symbol(Ident::from(s));
                return Ok(&self.tk);
            }
            _ => {}
        }
        self.tk = match with_sign {
            true => match (&s[0..]).parse::<i64>() {
                Ok(n) => Token::I64(n),
                Err(err) => return Err(format!("cannot parse i64 {:?}: {}", s, err)),
            },
            false => match is_hex {
                true => match u64::from_str_radix(&s[2..], 16) {
                    Ok(n) => Token::U64(n),
                    Err(err) => return Err(format!("cannot parse u64 {:?}: {}", s, err)),
                },
                false => match (&s[0..]).parse::<u64>() {
                    Ok(n) => Token::U64(n),
                    Err(err) => return Err(format!("cannot parse u64 {:?}: {}", s, err)),
                },
            },
        };
        Ok(&self.tk)
    }
    fn read_string(&mut self) -> Result<&Token, String> {
        let mut s = String::new();
        self.read_char();
        loop {
            match self.peek_char() {
                Some('"') => {
                    self.read_char();
                    break;
                }
                Some('\\') => {
                    self.read_char();
                    match self.peek_char() {
                        Some('"') => {
                            s.push('"');
                            self.read_char();
                        }
                        Some('\\') => {
                            s.push('\\');
                            self.read_char();
                        }
                        Some(c) => return Err(format!("illegal escape char {:?}", c)),
                        None => return Err("unexpected end of escape char".to_string()),
                    }
                }
                Some(c) => {
                    s.push(c);
                    self.read_char();
                }
                None => return Err("unexpected end of string".to_string()),
            }
        }
        self.tk = Token::String(s);
        Ok(&self.tk)
    }
    fn read_symbol(&mut self) -> Result<&Token, String> {
        let start = self.ptr();
        self.read_char();
        while let Some(c) = self.peek_char() {
            match c {
                '!' | '$' | '+' | '-' | '0'..='9' | '<' | '=' | '>' | 'A'..='Z' | 'a'..='z' => {
                    self.read_char();
                }
                _ => break,
            }
        }
        let s = &self.source()[start..self.ptr()];
        self.tk = Token::Symbol(Ident::from(s));
        Ok(&self.tk)
    }
    fn read_token(&mut self) -> Result<&Token, String> {
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() {
                self.read_char();
                continue;
            }
            match c {
                '!' | '$' | '<' | '=' | '>' | 'A'..='Z' | '_' | 'a'..='z' => {
                    return self.read_symbol()
                }
                '"' => return self.read_string(),
                '+' | '-' | '0'..='9' => return self.read_number(),
                '(' => {
                    self.tk = Token::LParen;
                    self.read_char();
                    return Ok(&self.tk);
                }
                ')' => {
                    self.tk = Token::RParen;
                    self.read_char();
                    return Ok(&self.tk);
                }
                ';' => {
                    while let Some(c) = self.peek_char() {
                        match c {
                            '\n' => break,
                            _ => {
                                self.read_char();
                            }
                        }
                    }
                }
                _ => return Err(format!("unexpected char {:?}", c)),
            }
        }
        self.tk = Token::None;
        Ok(&self.tk)
    }
    fn peek_token(&mut self) -> Result<&Token, String> {
        if self.tk == Token::None {
            return self.read_token();
        }
        Ok(&self.tk)
    }
    fn expect_token(&mut self, expected: &Token) -> Result<(), String> {
        let got = self.peek_token()?;
        if got != expected {
            return Err(format!("expected token {:?}, but got {:?}", expected, got));
        }
        self.read_token()?;
        Ok(())
    }
    fn parse_sexpr(&mut self) -> Result<Option<SExpr>, String> {
        match self.peek_token()? {
            Token::None => Ok(None),
            Token::I64(n) => {
                let sexpr = SExpr::I64(*n);
                self.read_token()?;
                Ok(Some(sexpr))
            }
            Token::U64(n) => {
                let sexpr = SExpr::U64(*n);
                self.read_token()?;
                Ok(Some(sexpr))
            }
            Token::String(s) => {
                let sexpr = SExpr::String(s.clone());
                self.read_token()?;
                Ok(Some(sexpr))
            }
            Token::Symbol(s) => {
                let sexpr = SExpr::Symbol(*s);
                self.read_token()?;
                Ok(Some(sexpr))
            }
            Token::LParen => {
                self.read_token()?;
                let mut list = Vec::new();
                while self.peek_token()? != &Token::RParen {
                    list.push(match self.parse_sexpr()? {
                        Some(sexpr) => sexpr,
                        None => return Err("unexpected end of list".to_string()),
                    });
                }
                self.expect_token(&Token::RParen)?;
                Ok(Some(SExpr::List(list)))
            }
            tk => return Err(format!("unexpected token {:?}", tk)),
        }
    }
    /// Returns a parsed S-expression.
    pub fn parse(&mut self) -> Result<Option<SExpr>, String> {
        match self.parse_sexpr() {
            Ok(res) => Ok(res),
            Err(err) => Err(format!("{}: {}", self.pos(), err)),
        }
    }
}

impl<'a> Deref for Parser<'a> {
    type Target = StringReader<'a>;
    fn deref(&self) -> &Self::Target {
        &self.reader
    }
}

impl<'a> DerefMut for Parser<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.reader
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sexpr_to_string() {
        for (expected, input) in vec![
            (r#"+1"#, SExpr::I64(1)),
            (r#"-1"#, SExpr::I64(-1)),
            (r#"0x1"#, SExpr::U64(1)),
            (r#""\"ABC\"""#, SExpr::String(String::from("\"ABC\""))),
            (r#"=="#, SExpr::Symbol(Ident::from("=="))),
            (r#"()"#, SExpr::List(vec![])),
            (r#"(0x1)"#, SExpr::List(vec![SExpr::U64(1)])),
            (
                r#"(0x1 (0x2 0x3))"#,
                SExpr::List(vec![
                    SExpr::U64(1),
                    SExpr::List(vec![SExpr::U64(2), SExpr::U64(3)]),
                ]),
            ),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn sexpr_try_to_cmd() {
        for (expected, input) in vec![
            ("None", "symbol"),
            ("Some((cmdname, [arg1, arg2]))", "(cmdname arg1 arg2)"),
            ("None", "(1 2 3)"),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match sexpr.try_to_cmd() {
                Some((name, args)) => {
                    format!(
                        "Some(({}, {}))",
                        name,
                        DisplayIter("[", args.iter(), ", ", "]")
                    )
                }
                None => format!("None"),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn macro_env() {
        let mut env = MacroEnv::empty();
        for (expected, input) in vec![
            ("Ok(true)", "(define f () c)"),
            ("Ok(true)", "(define g (x) (x x))"),
            ("Ok(true)", "(define h (x y) ((g x) (g y)))"),
            ("Ok(false)", "(g 1)"),
            ("Err(define: #1 arg must be symbol)", "(define 1 (x) (x x))"),
            ("Err(define: #2 arg must be list)", "(define f 2 (x x))"),
            (
                "Err(define: formal argument x is redefined)",
                "(define f (x x) (x x))",
            ),
            (
                "Err(define: formal argument 0x1 must be symbol)",
                "(define f (x 1) (x x))",
            ),
            ("Err(f is already defined)", "(define f (x) (x x))"),
        ] {
            let sexpr = SExpr::parse(input);
            let got = match env.parse_insert(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
        assert_eq!(3, env.len());
        for (expected, replaced) in vec![
            ("0x1", "1"),
            ("f", "f"),
            ("c", "(f)"),
            ("(a a)", "(g a)"),
            ("(g a b)", "(g a b)"),
            ("((a a) (b b))", "(h a b)"),
        ] {
            let result = env.apply(&SExpr::parse(replaced));
            assert_eq!(expected, result.to_string(), "{}", replaced);
        }
    }
    #[test]
    fn parser_parse() {
        let expected_input_list = vec![
            ("Ok(None)", r#""#),
            ("Ok(Some(+1))", r#"+1"#),
            ("Ok(Some(-1))", r#"-1"#),
            ("Ok(Some(-1))", r#"-1a"#),
            ("Ok(Some(0x7b))", r#"123"#),
            ("Ok(Some(0xff))", r#"0xff"#),
            ("Ok(Some(0xff))", r#"0xFF"#),
            ("Ok(Some(0xff))", r#"0xffg"#),
            ("Ok(Some(+))", r#"+"#),
            ("Ok(Some(-))", r#"-"#),
            ("Ok(Some(abc123))", r#"abc123"#),
            ("Ok(Some(!=))", r#"!="#),
            ("Ok(Some($var))", r#"$var"#),
            ("Ok(Some(<))", r#"<"#),
            ("Ok(Some(=))", r#"="#),
            ("Ok(Some(>))", r#">"#),
            ("Ok(Some(_))", r#"_"#),
            ("Ok(Some(\"\\\"\\\\ABC\\\"\"))", r#""\"\\ABC\"""#),
            ("Err(input:1:2: unexpected end of string)", r#"""#),
            ("Err(input:1:3: unexpected end of escape char)", r#""\"#),
            ("Err(input:1:3: illegal escape char 'x')", r#""\x"#),
            ("Ok(Some(()))", r#"()"#),
            ("Ok(Some((0x1)))", r#"( 1 )"#),
            ("Ok(Some((0x1 (0x2 0x3))))", r#"( 1 (2 3) )"#),
            ("Err(input:1:10: unexpected end of list)", r#"( 1 (2 3)"#),
            ("Err(input:1:2: unexpected token RParen)", r#")"#),
            ("Ok(Some(0x7b))", "; comment\n 123"),
        ];
        for (expected, input) in expected_input_list {
            let result = match Parser::new(input, "input") {
                Ok(mut parser) => match parser.parse() {
                    Ok(Some(sexpr)) => format!("Ok(Some({}))", sexpr),
                    Ok(None) => format!("Ok(None)"),
                    Err(err) => format!("Err({})", err),
                },
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
}
