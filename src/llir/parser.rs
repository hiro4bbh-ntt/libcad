//! The parser of the LLIR text representations.

use super::syntax::*;
use crate::fmt::DisplayIter;
use crate::reader::StringReader;
use std::collections::BTreeMap;
use std::ops::{Deref, DerefMut};

struct BlocksBuilder<I: ExtIdent> {
    id: usize,
    block: Block<I>,
    blocks: Blocks<I>,
    predlinks: BTreeMap<Label, Vec<Label>>,
}

impl<I: ExtIdent> BlocksBuilder<I> {
    fn new(id: usize) -> BlocksBuilder<I> {
        BlocksBuilder {
            id: id + 1,
            block: Block::new(id),
            blocks: Blocks::empty(),
            predlinks: BTreeMap::new(),
        }
    }
    fn set_label(&mut self, name: Label) {
        self.block.name = name;
    }
    fn push_insn(&mut self, insn: Insn<I>, mdlist: MetadataList, update_id: bool) {
        self.block.insns.push(insn);
        self.block.mdlists.push(mdlist);
        if update_id {
            self.id += 1;
        }
    }
    fn set_pred(&mut self, src: Label, dst: Label) {
        match self.predlinks.get_mut(&dst) {
            Some(predlinks) => predlinks.push(src),
            None => {
                self.predlinks.insert(dst, vec![src]);
            }
        }
    }
    fn set_br(&mut self, mut labels: Vec<Label>) {
        for label in &labels {
            self.set_pred(self.block.name, *label);
        }
        self.block.succs.append(&mut labels);
        self.blocks.push(self.block.clone());
        self.block = Block::new(self.id);
        self.id += 1;
    }
    fn finish(mut self) -> Result<Blocks<I>, String> {
        if !self.block.insns.is_empty() {
            self.blocks.push(self.block);
        }
        for block in self.blocks.iter_mut() {
            if let Some(preds) = self.predlinks.remove(&block.name) {
                block.preds = preds;
            }
        }
        if !self.predlinks.is_empty() {
            let predlinks = self
                .predlinks
                .iter()
                .map(|(k, v)| format!("{}: {}", k, DisplayIter("[", v.iter(), ",", "]")))
                .collect::<Vec<_>>();
            return Err(format!(
                "cannot resolve predlinks {}",
                DisplayIter("(", predlinks.iter(), ", ", ")"),
            ));
        }
        Ok(self.blocks)
    }
}

const RESERVED_KEYWORDS: &[&str] = &[
    "add",
    "alloca",
    "and",
    "ashr",
    "asm",
    "attributes",
    "bitcast",
    "blockaddress",
    "br",
    "call",
    "catch",
    "constant",
    "datalayout",
    "declare",
    "define",
    "double",
    "eq",
    "extractelement",
    "extractvalue",
    "fadd",
    "false",
    "fcmp",
    "fdiv",
    "filter",
    "float",
    "fmul",
    "fneg",
    "fpext",
    "fptosi",
    "fptoui",
    "fptrunc",
    "frem",
    "fsub",
    "getelementptr",
    "global",
    "i1",
    "i16",
    "i32",
    "i64",
    "i8",
    "icmp",
    "indirectbr",
    "insertelement",
    "insertvalue",
    "inttoptr",
    "invoke",
    "landingpad",
    "load",
    "lshr",
    "metadata",
    "mul",
    "musttail",
    "ne",
    "notail",
    "nsw",
    "null",
    "nuw",
    "oeq",
    "oge",
    "ogt",
    "ole",
    "olt",
    "one",
    "opaque",
    "or",
    "ord",
    "personality",
    "phi",
    "ptrtoint",
    "resume",
    "ret",
    "sdiv",
    "select",
    "sext",
    "sge",
    "sgt",
    "shl",
    "shufflevector",
    "sitofp",
    "sle",
    "slt",
    "source_filename",
    "srem",
    "store",
    "sub",
    "switch",
    "tail",
    "target",
    "to",
    "triple",
    "trunc",
    "true",
    "type",
    "udiv",
    "ueq",
    "uge",
    "ugt",
    "ule",
    "ult",
    "uitofp",
    "une",
    "uno",
    "unreachable",
    "urem",
    "undef",
    "unwind",
    "void",
    "x86_fp80",
    "xor",
    "zeroinitializer",
    "zext",
];

#[derive(Clone, Debug, PartialEq)]
enum Token<'a> {
    None,
    ReservedKeyword(&'a str),
    Keyword(&'a str),
    LocalIdent(&'a str),
    GlobalIdent(&'a str),
    Label(&'a str),
    String(&'a str),
    Number(&'a str),
    ArrayConst(String),
    AttrRef(u32),
    MetadataRef(&'a str),
    Exclam,
    Star,
    DotDotDot,
    Comma,
    LParen,
    RParen,
    LAngleBracket,
    RAngleBracket,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Eq,
    Vline,
}

/// A parser.
pub struct Parser<'a> {
    reader: StringReader<'a>,
    tk: Token<'a>,
}

impl<'a> Parser<'a> {
    /// Returns a new parser on the given source text with the file name.
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
    /// Returns a parsed type.
    pub fn try_new_type<I: ExtIdent>(source: &str) -> Result<Type<I>, String> {
        Parser::new(source, "try_new_type")?.parse_type()
    }
    /// Returns a parsed type.
    pub fn new_type<I: ExtIdent>(source: &str) -> Type<I> {
        Parser::try_new_type(source).expect(source)
    }
    /// Returns a parsed value.
    pub fn try_new_value<I: ExtIdent>(source: &str) -> Result<Value<I>, String> {
        Parser::new(source, "try_new_value")?.parse_value(None)
    }
    /// Returns a parsed value.
    pub fn new_value<I: ExtIdent>(source: &str) -> Value<I> {
        Parser::try_new_value(source).expect(source)
    }
    /// Returns a parsed typed value.
    pub fn try_new_typed_value<I: ExtIdent>(source: &str) -> Result<TypedValue<I>, String> {
        Parser::new(source, "try_new_typed_value")?.parse_typed_value()
    }
    /// Returns a parsed typed value.
    pub fn new_typed_value<I: ExtIdent>(source: &str) -> TypedValue<I> {
        Parser::try_new_typed_value(source).expect(source)
    }
    /// Returns a parsed statement.
    pub fn try_new_stmt<I: ExtIdent>(
        source: &str,
    ) -> Result<Option<(Stmt<I>, MetadataList)>, String> {
        Parser::new(source, "try_new_stmt")?.parse_stmt()
    }
    /// Returns a parsed statement.
    pub fn new_stmt<I: ExtIdent>(source: &str) -> (Stmt<I>, MetadataList) {
        Parser::try_new_stmt(source).expect(source).expect(source)
    }
    fn read_hex(&mut self, n: usize) -> Result<&'a str, String> {
        let start = self.ptr();
        for _ in 0..n {
            match self.peek_char() {
                Some(c) => match c {
                    '0'..='9' | 'A'..='F' | 'a'..='f' => {
                        self.read_char();
                    }
                    _ => return Err(format!("illegal hex char {:?}", c)),
                },
                _ => return Err("unexpected end-of-file in hex literal".to_string()),
            }
        }
        Ok(&self.source()[start..self.ptr()])
    }
    fn read_string_body(&mut self) -> Result<&'a str, String> {
        self.read_char();
        let start = self.ptr();
        loop {
            match self.peek_char() {
                Some('\n') => return Err("unexpected newline in string literal".to_string()),
                Some('"') => {
                    self.read_char();
                    break;
                }
                Some(_) => {
                    self.read_char();
                }
                None => return Err("unexpected end-of-file in string literal".to_string()),
            }
        }
        Ok(&self.source()[start..(self.ptr() - 1)])
    }
    fn read_identifier(&mut self) -> Result<&Token<'a>, String> {
        let start = self.ptr();
        self.read_char();
        while let Some(c) = self.peek_char() {
            match c {
                '$' | '-' | '.' | '0'..='9' | 'A'..='Z' | '_' | 'a'..='z' => {}
                _ => break,
            }
            self.read_char();
        }
        let ident = &self.source()[start..self.ptr()];
        self.tk = if ident == "!" {
            Token::Exclam
        } else if ident == "%" && matches!(self.peek_char(), Some('"')) {
            Token::LocalIdent(self.read_string_body()?)
        } else if ident == "..." {
            Token::DotDotDot
        } else if ident == "@" && matches!(self.peek_char(), Some('"')) {
            Token::GlobalIdent(self.read_string_body()?)
        } else if ident == "c" && matches!(self.peek_char(), Some('"')) {
            return self.read_array_const();
        } else {
            match ident.chars().next() {
                Some('!') => Token::MetadataRef(&ident[1..]),
                Some('%') => Token::LocalIdent(&ident[1..]),
                Some('@') => Token::GlobalIdent(&ident[1..]),
                _ => {
                    if let Some(':') = self.peek_char() {
                        self.read_char();
                        Token::Label(ident)
                    } else if RESERVED_KEYWORDS.contains(&ident) {
                        Token::ReservedKeyword(ident)
                    } else {
                        Token::Keyword(ident)
                    }
                }
            }
        };
        Ok(&self.tk)
    }
    fn read_number(&mut self) -> Result<&Token<'a>, String> {
        let start = self.ptr();
        if let Some('0') = self.peek_char() {
            self.read_char();
            if let Some('x') = self.peek_char() {
                self.read_char();
                if let Some('K') = self.peek_char() {
                    self.read_char();
                }
            }
        } else {
            self.read_char();
        }
        while let Some('0'..='9') | Some('A'..='F') | Some('a'..='f') = self.peek_char() {
            self.read_char();
        }
        if let Some('.') = self.peek_char() {
            self.read_char();
            while let Some('0'..='9') = self.peek_char() {
                self.read_char();
            }
            if let Some('E') | Some('e') = self.peek_char() {
                self.read_char();
                if let Some('+') | Some('-') = self.peek_char() {
                    self.read_char();
                    while let Some('0'..='9') = self.peek_char() {
                        self.read_char();
                    }
                }
            }
        }
        let s = &self.source()[start..self.ptr()];
        self.tk = match s.chars().next() {
            Some('#') => match s[1..].parse::<u32>() {
                Ok(n) => Token::AttrRef(n),
                Err(_) => return Err(format!("illegal attribute reference {:?}", s)),
            },
            _ => {
                if let Some(':') = self.peek_char() {
                    self.read_char();
                    Token::Label(s)
                } else {
                    Token::Number(s)
                }
            }
        };
        Ok(&self.tk)
    }
    fn read_string(&mut self) -> Result<&Token<'a>, String> {
        let s = self.read_string_body()?;
        self.tk = Token::String(s);
        if let Some(':') = self.peek_char() {
            self.read_char();
            self.tk = Token::Label(s);
        }
        Ok(&self.tk)
    }
    fn read_array_const(&mut self) -> Result<&Token<'a>, String> {
        self.read_char();
        let mut s = String::from("");
        loop {
            match self.peek_char() {
                Some('\n') => return Err("unexpected newline in array constant".to_string()),
                Some('"') => {
                    self.read_char();
                    break;
                }
                Some('\\') => {
                    self.read_char();
                    match self.peek_char() {
                        Some('\\') => {
                            self.read_char();
                            s.push('\\');
                        }
                        _ => {
                            let hex = self.read_hex(2)?;
                            let n = u8::from_str_radix(hex, 16).unwrap();
                            s.push(char::from(n));
                        }
                    }
                }
                Some(c) => {
                    s.push(c);
                    self.read_char();
                }
                None => return Err("unexpected end-of-file in array constant".to_string()),
            }
        }
        self.tk = Token::ArrayConst(s);
        Ok(&self.tk)
    }
    fn read_token(&mut self) -> Result<&Token<'a>, String> {
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() {
                self.read_char();
                continue;
            }
            match c {
                '!' | '%' | '.' | '@' | 'A'..='Z' | '_' | 'a'..='z' => {
                    return self.read_identifier()
                }
                '"' => return self.read_string(),
                '#' | '-' | '0'..='9' => return self.read_number(),
                '(' => {
                    self.read_char();
                    self.tk = Token::LParen;
                    return Ok(&self.tk);
                }
                ')' => {
                    self.read_char();
                    self.tk = Token::RParen;
                    return Ok(&self.tk);
                }
                '*' => {
                    self.read_char();
                    self.tk = Token::Star;
                    return Ok(&self.tk);
                }
                ',' => {
                    self.read_char();
                    self.tk = Token::Comma;
                    return Ok(&self.tk);
                }
                ';' => loop {
                    if let Some('\n') = self.read_char() {
                        break;
                    }
                },
                '<' => {
                    self.read_char();
                    self.tk = Token::LAngleBracket;
                    return Ok(&self.tk);
                }
                '=' => {
                    self.read_char();
                    self.tk = Token::Eq;
                    return Ok(&self.tk);
                }
                '>' => {
                    self.read_char();
                    self.tk = Token::RAngleBracket;
                    return Ok(&self.tk);
                }
                '[' => {
                    self.read_char();
                    self.tk = Token::LBracket;
                    return Ok(&self.tk);
                }
                ']' => {
                    self.read_char();
                    self.tk = Token::RBracket;
                    return Ok(&self.tk);
                }
                '{' => {
                    self.read_char();
                    self.tk = Token::LBrace;
                    return Ok(&self.tk);
                }
                '|' => {
                    self.read_char();
                    self.tk = Token::Vline;
                    return Ok(&self.tk);
                }
                '}' => {
                    self.read_char();
                    self.tk = Token::RBrace;
                    return Ok(&self.tk);
                }
                c => return Err(format!("unknown char {:?}", c)),
            }
        }
        self.tk = Token::None;
        Ok(&self.tk)
    }
    fn peek_token(&mut self) -> Result<&Token<'a>, String> {
        if self.tk == Token::None {
            return self.read_token();
        }
        Ok(&self.tk)
    }
    fn may_expect_token(&mut self, expected: &Token) -> Result<bool, String> {
        if expected == self.peek_token()? {
            self.read_token()?;
            return Ok(true);
        }
        Ok(false)
    }
    fn expect_token(&mut self, expected: &Token) -> Result<(), String> {
        let got = self.peek_token()?;
        if got != expected {
            return Err(format!("expected token {:?}, but got {:?}", expected, got));
        }
        self.read_token()?;
        Ok(())
    }
    fn expect_global_ident(&mut self) -> Result<GlobalIdent, String> {
        match self.peek_token()? {
            Token::GlobalIdent(name) => {
                let name = GlobalIdent::from(*name);
                self.read_token()?;
                Ok(name)
            }
            got => Err(format!("expected global identifier, but got {:?}", got)),
        }
    }
    fn expect_label(&mut self) -> Result<Label, String> {
        match self.peek_token()? {
            Token::Label(name) => {
                let name = LocalIdent::from(*name);
                self.read_token()?;
                Ok(Label::from(name))
            }
            got => Err(format!("expected label, but got {:?}", got)),
        }
    }
    fn expect_string(&mut self) -> Result<String, String> {
        match self.peek_token()? {
            Token::String(s) => {
                let s = s.to_string();
                self.read_token()?;
                Ok(s)
            }
            got => Err(format!("expected string literal, but got {:?}", got)),
        }
    }
    fn expect_number(&mut self) -> Result<String, String> {
        match self.peek_token()? {
            Token::Number(s) => {
                let s = s.to_string();
                self.read_token()?;
                Ok(s)
            }
            got => Err(format!("expected number literal, but got {:?}", got)),
        }
    }
    fn expect_number_u32(&mut self) -> Result<u32, String> {
        let s = self.expect_number()?;
        match s.parse::<u32>() {
            Ok(n) => Ok(n),
            _ => Err(format!("expected u32 literal, but got {:?}", s)),
        }
    }
    fn expect_attr_ref(&mut self) -> Result<u32, String> {
        match self.peek_token()? {
            Token::AttrRef(id) => {
                let id = *id;
                self.read_token()?;
                Ok(id)
            }
            got => Err(format!("expected attribute reference, but got {:?}", got)),
        }
    }
    fn expect_metadata_ref(&mut self) -> Result<MetadataRef, String> {
        match self.peek_token()? {
            Token::MetadataRef(name) => {
                let name = name.to_string();
                self.read_token()?;
                Ok(MetadataRef::new(name))
            }
            got => Err(format!("expected metadata reference, but got {:?}", got)),
        }
    }
    fn parse_param_attr<I: ExtIdent>(&mut self) -> Result<Option<ParamAttr<I>>, String> {
        if let Token::Keyword(name) = self.peek_token()? {
            let name = name.to_string();
            self.read_token()?;
            let arg = if name == "align" {
                let wrapped = self.may_expect_token(&Token::LParen)?;
                let n = self.expect_number_u32()?;
                if wrapped {
                    self.expect_token(&Token::RParen)?;
                }
                Some(ParamAttrArg::U32(n))
            } else if self.may_expect_token(&Token::LParen)? {
                match &name as &str {
                    "byref" | "byval" => {
                        let ty = self.parse_type()?;
                        self.expect_token(&Token::RParen)?;
                        Some(ParamAttrArg::Type(ty))
                    }
                    _ => {
                        let n = self.expect_number_u32()?;
                        self.expect_token(&Token::RParen)?;
                        Some(ParamAttrArg::U32(n))
                    }
                }
            } else {
                None
            };
            return Ok(Some(ParamAttr(name, arg)));
        }
        Ok(None)
    }
    fn parse_param_attrs<I: ExtIdent>(&mut self) -> Result<ParamAttrs<I>, String> {
        let mut attrs = Vec::new();
        while let Some(attr) = self.parse_param_attr()? {
            attrs.push(attr);
        }
        Ok(ParamAttrs::new(attrs))
    }
    fn parse_param<I: ExtIdent>(&mut self, with_name: bool) -> Result<Param<I>, String> {
        let ty = self.parse_type()?;
        let attrs = self.parse_param_attrs()?;
        let mut name = None;
        if with_name {
            if let Token::LocalIdent(s) = self.peek_token()? {
                name = Some(LocalIdent::from(*s));
                self.read_token()?;
            }
        }
        Ok(Param { ty, attrs, name })
    }
    fn parse_arglist<I: ExtIdent>(&mut self) -> Result<(Vec<Param<I>>, bool), String> {
        self.expect_token(&Token::LParen)?;
        let mut args = Vec::new();
        let mut variadic = false;
        loop {
            self.may_expect_token(&Token::Comma)?;
            if self.may_expect_token(&Token::DotDotDot)? {
                variadic = true;
                self.expect_token(&Token::RParen)?;
                break;
            }
            if self.may_expect_token(&Token::RParen)? {
                break;
            }
            args.push(self.parse_param(true)?);
        }
        Ok((args, variadic))
    }
    fn parse_type<I: ExtIdent>(&mut self) -> Result<Type<I>, String> {
        let mut ty = match self.peek_token()? {
            Token::ReservedKeyword("void") => {
                self.read_token()?;
                Type::Void
            }
            Token::ReservedKeyword("i1") => {
                self.read_token()?;
                Type::I1
            }
            Token::ReservedKeyword("i8") => {
                self.read_token()?;
                Type::I8
            }
            Token::ReservedKeyword("i16") => {
                self.read_token()?;
                Type::I16
            }
            Token::ReservedKeyword("i32") => {
                self.read_token()?;
                Type::I32
            }
            Token::ReservedKeyword("i64") => {
                self.read_token()?;
                Type::I64
            }
            Token::ReservedKeyword("float") => {
                self.read_token()?;
                Type::Float
            }
            Token::ReservedKeyword("double") => {
                self.read_token()?;
                Type::Double
            }
            Token::ReservedKeyword("x86_fp80") => {
                self.read_token()?;
                Type::X86Fp80
            }
            Token::LAngleBracket => {
                self.read_token()?;
                if self.may_expect_token(&Token::LBrace)? {
                    let mut fields = Vec::new();
                    loop {
                        self.may_expect_token(&Token::Comma)?;
                        if self.may_expect_token(&Token::RBrace)? {
                            break;
                        }
                        fields.push(self.parse_type()?);
                    }
                    self.expect_token(&Token::RAngleBracket)?;
                    Type::Struct(true, fields)
                } else {
                    let vscale = self.may_expect_token(&Token::Keyword("vscale"))?;
                    if vscale {
                        self.expect_token(&Token::Keyword("x"))?;
                    }
                    let size = self.expect_number_u32()?;
                    self.expect_token(&Token::Keyword("x"))?;
                    let ty = self.parse_type()?;
                    self.expect_token(&Token::RAngleBracket)?;
                    Type::Vector(vscale, size, Box::new(ty))
                }
            }
            Token::LBrace => {
                self.read_token()?;
                let mut fields = Vec::new();
                loop {
                    self.may_expect_token(&Token::Comma)?;
                    if self.may_expect_token(&Token::RBrace)? {
                        break;
                    }
                    fields.push(self.parse_type()?);
                }
                Type::Struct(false, fields)
            }
            Token::LBracket => {
                self.read_token()?;
                let size = self.expect_number_u32()?;
                self.expect_token(&Token::Keyword("x"))?;
                let ty = self.parse_type()?;
                self.expect_token(&Token::RBracket)?;
                Type::Array(size, Box::new(ty))
            }
            Token::ReservedKeyword("opaque") => {
                self.read_token()?;
                Type::Opaque
            }
            Token::LocalIdent(name) => {
                let name = LocalIdent::from(*name);
                self.read_token()?;
                Type::Name(name)
            }
            Token::ReservedKeyword("metadata") => {
                self.read_token()?;
                Type::Metadata
            }
            tk => return Err(format!("unexpected {:?} in type", tk)),
        };
        loop {
            match self.peek_token()? {
                Token::Star => {
                    self.read_token()?;
                    ty = Type::Ptr(Box::new(ty));
                }
                Token::LParen => {
                    let (args, variadic) = self.parse_arglist()?;
                    ty = Type::Func(FuncSig {
                        ret: Box::new(RetParam {
                            attrs: ParamAttrs::new(Vec::new()),
                            ty,
                        }),
                        name: None,
                        args,
                        variadic,
                    });
                }
                _ => return Ok(ty),
            }
        }
    }
    fn parse_aggop<I: ExtIdent>(&mut self) -> Result<Option<AggOpArgs<I>>, String> {
        match self.peek_token()? {
            Token::ReservedKeyword("extractvalue") => {
                self.read_token()?;
                let inline = self.may_expect_token(&Token::LParen)?;
                let tyval = self.parse_typed_value()?;
                let mut indices = Vec::new();
                while self.may_expect_token(&Token::Comma)? {
                    if !inline {
                        if let Token::MetadataRef("dbg") = self.peek_token()? {
                            break;
                        }
                    }
                    indices.push(self.expect_number_u32()?);
                }
                if inline {
                    self.expect_token(&Token::RParen)?;
                }
                Ok(Some(AggOpArgs::Extractvalue(tyval, indices)))
            }
            Token::ReservedKeyword("insertvalue") => {
                self.read_token()?;
                let inline = self.may_expect_token(&Token::LParen)?;
                let dst = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let src = self.parse_typed_value()?;
                let mut indices = Vec::new();
                while self.may_expect_token(&Token::Comma)? {
                    if !inline {
                        if let Token::MetadataRef("dbg") = self.peek_token()? {
                            break;
                        }
                    }
                    indices.push(self.expect_number_u32()?);
                }
                if inline {
                    self.expect_token(&Token::RParen)?;
                }
                Ok(Some(AggOpArgs::Insertvalue(dst, src, indices)))
            }
            _ => Ok(None),
        }
    }
    fn parse_wrap_mode(&mut self) -> Result<Option<WrapMode>, String> {
        let nuw = self.may_expect_token(&Token::ReservedKeyword("nuw"))?;
        let nsw = self.may_expect_token(&Token::ReservedKeyword("nsw"))?;
        if nuw {
            if nsw {
                return Ok(Some(WrapMode::NuwNsw));
            }
            return Ok(Some(WrapMode::Nuw));
        }
        if nsw {
            return Ok(Some(WrapMode::Nsw));
        }
        Ok(None)
    }
    fn parse_binop_args<I: ExtIdent>(&mut self) -> Result<(TypedValue<I>, TypedValue<I>), String> {
        if self.may_expect_token(&Token::LParen)? {
            let left = self.parse_typed_value()?;
            self.expect_token(&Token::Comma)?;
            let right = self.parse_typed_value()?;
            self.expect_token(&Token::RParen)?;
            Ok((left, right))
        } else {
            let ty = self.parse_type()?;
            let left = self.parse_value(Some(&ty))?;
            self.expect_token(&Token::Comma)?;
            let right = self.parse_value(Some(&ty))?;
            Ok((TypedValue(ty.clone(), left), TypedValue(ty, right)))
        }
    }
    fn parse_binop<I: ExtIdent>(&mut self) -> Result<Option<BinOpArgs<I>>, String> {
        let opcode = match self.peek_token()? {
            Token::ReservedKeyword("add") => {
                self.read_token()?;
                BinOpcode::Add(self.parse_wrap_mode()?)
            }
            Token::ReservedKeyword("and") => {
                self.read_token()?;
                BinOpcode::And
            }
            Token::ReservedKeyword("ashr") => {
                self.read_token()?;
                BinOpcode::Ashr(self.may_expect_token(&Token::Keyword("exact"))?)
            }
            Token::ReservedKeyword("fadd") => {
                self.read_token()?;
                BinOpcode::Fadd
            }
            Token::ReservedKeyword("fdiv") => {
                self.read_token()?;
                BinOpcode::Fdiv
            }
            Token::ReservedKeyword("fmul") => {
                self.read_token()?;
                BinOpcode::Fmul
            }
            Token::ReservedKeyword("frem") => {
                self.read_token()?;
                BinOpcode::Frem
            }
            Token::ReservedKeyword("fsub") => {
                self.read_token()?;
                BinOpcode::Fsub
            }
            Token::ReservedKeyword("lshr") => {
                self.read_token()?;
                BinOpcode::Lshr(self.may_expect_token(&Token::Keyword("exact"))?)
            }
            Token::ReservedKeyword("mul") => {
                self.read_token()?;
                BinOpcode::Mul(self.parse_wrap_mode()?)
            }
            Token::ReservedKeyword("or") => {
                self.read_token()?;
                BinOpcode::Or
            }
            Token::ReservedKeyword("sdiv") => {
                self.read_token()?;
                BinOpcode::Sdiv(self.may_expect_token(&Token::Keyword("exact"))?)
            }
            Token::ReservedKeyword("shl") => {
                self.read_token()?;
                BinOpcode::Shl(self.parse_wrap_mode()?)
            }
            Token::ReservedKeyword("srem") => {
                self.read_token()?;
                BinOpcode::Srem
            }
            Token::ReservedKeyword("sub") => {
                self.read_token()?;
                BinOpcode::Sub(self.parse_wrap_mode()?)
            }
            Token::ReservedKeyword("udiv") => {
                self.read_token()?;
                BinOpcode::Udiv(self.may_expect_token(&Token::Keyword("exact"))?)
            }
            Token::ReservedKeyword("urem") => {
                self.read_token()?;
                BinOpcode::Urem
            }
            Token::ReservedKeyword("xor") => {
                self.read_token()?;
                BinOpcode::Xor
            }
            _ => return Ok(None),
        };
        let (left, right) = self.parse_binop_args()?;
        Ok(Some(BinOpArgs {
            opcode,
            left,
            right,
        }))
    }
    fn parse_fcmp_cond(&mut self) -> Result<FcmpCond, String> {
        let cond = match self.peek_token()? {
            Token::ReservedKeyword("false") => FcmpCond::False,
            Token::ReservedKeyword("oeq") => FcmpCond::Oeq,
            Token::ReservedKeyword("ogt") => FcmpCond::Ogt,
            Token::ReservedKeyword("oge") => FcmpCond::Oge,
            Token::ReservedKeyword("olt") => FcmpCond::Olt,
            Token::ReservedKeyword("ole") => FcmpCond::Ole,
            Token::ReservedKeyword("one") => FcmpCond::One,
            Token::ReservedKeyword("ord") => FcmpCond::Ord,
            Token::ReservedKeyword("ueq") => FcmpCond::Ueq,
            Token::ReservedKeyword("ugt") => FcmpCond::Ugt,
            Token::ReservedKeyword("uge") => FcmpCond::Uge,
            Token::ReservedKeyword("ult") => FcmpCond::Ult,
            Token::ReservedKeyword("ule") => FcmpCond::Ule,
            Token::ReservedKeyword("une") => FcmpCond::Une,
            Token::ReservedKeyword("uno") => FcmpCond::Uno,
            Token::ReservedKeyword("true") => FcmpCond::True,
            tk => return Err(format!("illegal fcmp condition {:?}", tk)),
        };
        self.read_token()?;
        Ok(cond)
    }
    fn parse_icmp_cond(&mut self) -> Result<IcmpCond, String> {
        let cond = match self.peek_token()? {
            Token::ReservedKeyword("eq") => IcmpCond::Eq,
            Token::ReservedKeyword("ne") => IcmpCond::Ne,
            Token::ReservedKeyword("ugt") => IcmpCond::Ugt,
            Token::ReservedKeyword("uge") => IcmpCond::Uge,
            Token::ReservedKeyword("ult") => IcmpCond::Ult,
            Token::ReservedKeyword("ule") => IcmpCond::Ule,
            Token::ReservedKeyword("sgt") => IcmpCond::Sgt,
            Token::ReservedKeyword("sge") => IcmpCond::Sge,
            Token::ReservedKeyword("slt") => IcmpCond::Slt,
            Token::ReservedKeyword("sle") => IcmpCond::Sle,
            tk => return Err(format!("illegal icmp condition {:?}", tk)),
        };
        self.read_token()?;
        Ok(cond)
    }
    fn parse_cmpop<I: ExtIdent>(&mut self) -> Result<Option<CmpOpArgs<I>>, String> {
        let opcode = match self.peek_token()? {
            Token::ReservedKeyword("fcmp") => {
                self.read_token()?;
                CmpOpcode::Fcmp(self.parse_fcmp_cond()?)
            }
            Token::ReservedKeyword("icmp") => {
                self.read_token()?;
                CmpOpcode::Icmp(self.parse_icmp_cond()?)
            }
            _ => return Ok(None),
        };
        let (left, right) = self.parse_binop_args()?;
        Ok(Some(CmpOpArgs {
            opcode,
            left,
            right,
        }))
    }
    fn parse_convop<I: ExtIdent>(&mut self) -> Result<Option<ConvOpArgs<I>>, String> {
        let opcode = match self.peek_token()? {
            Token::ReservedKeyword("bitcast") => ConvOpcode::Bitcast,
            Token::ReservedKeyword("fpext") => ConvOpcode::Fpext,
            Token::ReservedKeyword("fptosi") => ConvOpcode::Fptosi,
            Token::ReservedKeyword("fptoui") => ConvOpcode::Fptoui,
            Token::ReservedKeyword("fptrunc") => ConvOpcode::Fptrunc,
            Token::ReservedKeyword("inttoptr") => ConvOpcode::Inttoptr,
            Token::ReservedKeyword("ptrtoint") => ConvOpcode::Ptrtoint,
            Token::ReservedKeyword("sext") => ConvOpcode::Sext,
            Token::ReservedKeyword("sitofp") => ConvOpcode::Sitofp,
            Token::ReservedKeyword("trunc") => ConvOpcode::Trunc,
            Token::ReservedKeyword("uitofp") => ConvOpcode::Uitofp,
            Token::ReservedKeyword("zext") => ConvOpcode::Zext,
            _ => return Ok(None),
        };
        self.read_token()?;
        let inline = self.may_expect_token(&Token::LParen)?;
        let srctyval = self.parse_typed_value()?;
        self.expect_token(&Token::ReservedKeyword("to"))?;
        let dstty = self.parse_type()?;
        if inline {
            self.expect_token(&Token::RParen)?;
        }
        Ok(Some(ConvOpArgs {
            opcode,
            srctyval,
            dstty,
        }))
    }
    fn parse_getelementptr<I: ExtIdent>(&mut self) -> Result<GetelementptrArgs<I>, String> {
        self.read_token()?;
        let inbounds = self.may_expect_token(&Token::Keyword("inbounds"))?;
        let inline = self.may_expect_token(&Token::LParen)?;
        let base_ty = self.parse_type()?;
        self.expect_token(&Token::Comma)?;
        let base_ptr = self.parse_typed_value()?;
        let mut indices = Vec::new();
        loop {
            match self.peek_token()? {
                Token::RParen => {
                    if inline {
                        self.read_token()?;
                        break;
                    }
                    return Err("unexpected `)`".to_string());
                }
                Token::Comma => {
                    self.read_token()?;
                    if !inline {
                        if let Token::MetadataRef("dbg") = self.peek_token()? {
                            break;
                        }
                    }
                    let inrange = self.may_expect_token(&Token::Keyword("inrange"))?;
                    indices.push((inrange, self.parse_typed_value()?));
                }
                tk => {
                    if inline {
                        return Err(format!("expected `)`, but got {:?}", tk));
                    }
                    break;
                }
            }
        }
        Ok(GetelementptrArgs {
            inbounds,
            base_ty,
            base_ptr,
            indices,
        })
    }
    fn parse_unop_args<I: ExtIdent>(&mut self) -> Result<TypedValue<I>, String> {
        if self.may_expect_token(&Token::LParen)? {
            let opr = self.parse_typed_value()?;
            self.expect_token(&Token::RParen)?;
            Ok(opr)
        } else {
            let ty = self.parse_type()?;
            let opr = self.parse_value(Some(&ty))?;
            Ok(TypedValue(ty, opr))
        }
    }
    fn parse_unop<I: ExtIdent>(&mut self) -> Result<Option<UnOpArgs<I>>, String> {
        let opcode = match self.peek_token()? {
            Token::ReservedKeyword("fneg") => {
                self.read_token()?;
                UnOpcode::Fneg
            }
            _ => return Ok(None),
        };
        let tyval = self.parse_unop_args()?;
        Ok(Some(UnOpArgs { opcode, tyval }))
    }
    fn parse_vecop<I: ExtIdent>(&mut self) -> Result<Option<VecOpArgs<I>>, String> {
        match self.peek_token()? {
            Token::ReservedKeyword("extractelement") => {
                self.read_token()?;
                let inline = self.may_expect_token(&Token::LParen)?;
                let val = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let idx = self.parse_typed_value()?;
                if inline {
                    self.expect_token(&Token::RParen)?;
                }
                Ok(Some(VecOpArgs::Extractelement(val, idx)))
            }
            Token::ReservedKeyword("insertelement") => {
                self.read_token()?;
                let inline = self.may_expect_token(&Token::LParen)?;
                let val = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let elt = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let idx = self.parse_typed_value()?;
                if inline {
                    self.expect_token(&Token::RParen)?;
                }
                Ok(Some(VecOpArgs::Insertelement(val, elt, idx)))
            }
            Token::ReservedKeyword("shufflevector") => {
                self.read_token()?;
                let inline = self.may_expect_token(&Token::LParen)?;
                let v1 = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let v2 = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let mask = self.parse_typed_value()?;
                if inline {
                    self.expect_token(&Token::RParen)?;
                }
                Ok(Some(VecOpArgs::Shufflevector(v1, v2, mask)))
            }
            _ => Ok(None),
        }
    }
    fn parse_value<I: ExtIdent>(&mut self, ty: Option<&Type<I>>) -> Result<Value<I>, String> {
        if let Some(Type::Metadata) = ty {
            return Ok(Value::Metadata(Box::new(self.parse_metadata()?)));
        }
        if let Some(args) = self.parse_aggop()? {
            return Ok(Value::AggOp(Box::new(args)));
        } else if let Some(args) = self.parse_binop()? {
            return Ok(Value::BinOp(Box::new(args)));
        } else if let Some(args) = self.parse_cmpop()? {
            return Ok(Value::CmpOp(Box::new(args)));
        } else if let Some(args) = self.parse_convop()? {
            return Ok(Value::ConvOp(Box::new(args)));
        } else if let Some(args) = self.parse_unop()? {
            return Ok(Value::UnOp(Box::new(args)));
        } else if let Some(args) = self.parse_vecop()? {
            return Ok(Value::VecOp(Box::new(args)));
        }
        match self.peek_token()? {
            Token::ReservedKeyword("null") => {
                self.read_token()?;
                Ok(Value::Null)
            }
            Token::ReservedKeyword("undef") => {
                self.read_token()?;
                Ok(Value::Undef)
            }
            Token::ReservedKeyword("false") => {
                self.read_token()?;
                Ok(Value::False)
            }
            Token::ReservedKeyword("true") => {
                self.read_token()?;
                Ok(Value::True)
            }
            Token::Number(s) => match ty {
                Some(Type::I8) => match s.parse::<i8>() {
                    Ok(n) => {
                        self.read_token()?;
                        Ok(Value::I8(n))
                    }
                    Err(_) => Err(format!("malformed i8 constant: {}", s)),
                },
                Some(Type::I16) => match s.parse::<i16>() {
                    Ok(n) => {
                        self.read_token()?;
                        Ok(Value::I16(n))
                    }
                    Err(_) => Err(format!("malformed i16 constant: {}", s)),
                },
                Some(Type::I32) => match s.parse::<i32>() {
                    Ok(n) => {
                        self.read_token()?;
                        Ok(Value::I32(n))
                    }
                    Err(_) => Err(format!("malformed i32 constant: {}", s)),
                },
                Some(Type::I64) => match s.parse::<i64>() {
                    Ok(n) => {
                        self.read_token()?;
                        Ok(Value::I64(n))
                    }
                    Err(_) => Err(format!("malformed i64 constant: {}", s)),
                },
                Some(Type::Float) => {
                    let s = s.to_string();
                    self.read_token()?;
                    Ok(Value::Float(s))
                }
                Some(Type::Double) => {
                    let s = s.to_string();
                    self.read_token()?;
                    Ok(Value::Double(s))
                }
                Some(Type::X86Fp80) => {
                    let s = s.to_string();
                    self.read_token()?;
                    Ok(Value::X86Fp80(s))
                }
                Some(ty) => Err(format!("cannot cast number {} to type {}", s, ty)),
                None => unimplemented!("{}", s),
            },
            Token::ArrayConst(c) => {
                let c = c.clone();
                self.read_token()?;
                Ok(Value::ArrayConst(c))
            }
            Token::LAngleBracket => {
                self.read_token()?;
                if self.may_expect_token(&Token::LBrace)? {
                    let values = self.parse_typed_value_list(&Token::RBrace)?;
                    self.expect_token(&Token::RAngleBracket)?;
                    Ok(Value::Struct(true, values))
                } else {
                    let values = self.parse_typed_value_list(&Token::RAngleBracket)?;
                    Ok(Value::Vector(values))
                }
            }
            Token::LBrace => {
                self.read_token()?;
                let values = self.parse_typed_value_list(&Token::RBrace)?;
                Ok(Value::Struct(false, values))
            }
            Token::LBracket => {
                self.read_token()?;
                let values = self.parse_typed_value_list(&Token::RBracket)?;
                Ok(Value::Array(values))
            }
            Token::LocalIdent(name) => {
                let name = LocalIdent::from(*name);
                self.read_token()?;
                Ok(Value::LocalRef(name))
            }
            Token::GlobalIdent(name) => {
                let name = GlobalIdent::from(*name);
                self.read_token()?;
                Ok(Value::GlobalRef(name))
            }
            Token::ReservedKeyword("getelementptr") => {
                Ok(Value::Getelementptr(Box::new(self.parse_getelementptr()?)))
            }
            Token::ReservedKeyword("zeroinitializer") => {
                self.read_token()?;
                Ok(Value::Zeroinitializer)
            }
            Token::ReservedKeyword("blockaddress") => {
                self.read_token()?;
                self.expect_token(&Token::LParen)?;
                let name = self.expect_global_ident()?;
                self.expect_token(&Token::Comma)?;
                let label = match self.peek_token()? {
                    Token::LocalIdent(name) => {
                        let name = <&str>::clone(name);
                        self.read_token()?;
                        Label::from(LocalIdent::from(name))
                    }
                    tk => return Err(format!("expected local identifier, but got {:?}", tk)),
                };
                self.expect_token(&Token::RParen)?;
                Ok(Value::Blockaddress(name, label))
            }
            tk => match ty {
                Some(ty) => Err(format!("unexpected {:?} in value after {}", tk, ty)),
                None => Err(format!("unexpected {:?} in value", tk)),
            },
        }
    }
    fn parse_label(&mut self) -> Result<Label, String> {
        self.expect_token(&Token::Keyword("label"))?;
        match self.peek_token()? {
            Token::LocalIdent(name) => {
                let name = LocalIdent::from(*name);
                self.read_token()?;
                Ok(Label::from(name))
            }
            tk => Err(format!("malformed label {:?}", tk)),
        }
    }
    fn parse_typed_value<I: ExtIdent>(&mut self) -> Result<TypedValue<I>, String> {
        let ty = self.parse_type()?;
        let value = self.parse_value(Some(&ty))?;
        Ok(TypedValue(ty, value))
    }
    fn parse_param_value<I: ExtIdent>(&mut self) -> Result<ParamValue<I>, String> {
        let param = self.parse_param(false)?;
        let value = self.parse_value(Some(&param.ty))?;
        Ok(ParamValue(param, value))
    }
    fn parse_typed_value_list<I: ExtIdent>(
        &mut self,
        encloser: &Token,
    ) -> Result<Vec<TypedValue<I>>, String> {
        let mut values = Vec::new();
        loop {
            self.may_expect_token(&Token::Comma)?;
            if encloser == self.peek_token()? {
                self.read_token()?;
                break;
            }
            values.push(self.parse_typed_value()?);
        }
        Ok(values)
    }
    fn parse_param_value_list<I: ExtIdent>(
        &mut self,
        encloser: &Token,
    ) -> Result<Vec<ParamValue<I>>, String> {
        let mut values = Vec::new();
        loop {
            self.may_expect_token(&Token::Comma)?;
            if encloser == self.peek_token()? {
                self.read_token()?;
                break;
            }
            values.push(self.parse_param_value()?);
        }
        Ok(values)
    }
    fn may_parse_align(&mut self) -> Result<Option<u32>, String> {
        if self.may_expect_token(&Token::Keyword("align"))? {
            let s = self.expect_number()?;
            return match s.parse::<u32>() {
                Ok(n) => Ok(Some(n)),
                Err(_) => Err(format!("malformed align {}", s)),
            };
        }
        Ok(None)
    }
    fn may_parse_optional_align(&mut self) -> Result<Option<u32>, String> {
        if self.may_expect_token(&Token::Comma)? {
            return self.may_parse_align();
        }
        Ok(None)
    }
    fn parse_attrs<I: ExtIdent>(&mut self) -> Result<Vec<Attr<I>>, String> {
        let mut attrs = Vec::new();
        loop {
            if let Some(attr) = self.parse_param_attr()? {
                attrs.push(Attr::ParamAttr(attr));
                continue;
            }
            match self.peek_token()? {
                Token::Keyword(key) | Token::String(key) => {
                    let key = key.to_string();
                    self.read_token()?;
                    if self.may_expect_token(&Token::Eq)? {
                        let value = self.expect_string()?;
                        attrs.push(Attr::KeyValue(key, value));
                    } else {
                        attrs.push(Attr::Key(key));
                    }
                }
                Token::AttrRef(id) => {
                    attrs.push(Attr::Ref(*id));
                    self.read_token()?;
                }
                _ => break,
            }
        }
        Ok(attrs)
    }
    fn parse_call_conv(&mut self) -> Result<Option<CallConv>, String> {
        match self.peek_token()? {
            Token::Keyword("fastcc") => {
                self.read_token()?;
                Ok(Some(CallConv::Fastcc))
            }
            _ => Ok(None),
        }
    }
    fn parse_call_body<I: ExtIdent>(&mut self) -> Result<CallBody<I>, String> {
        self.read_token()?;
        let call_conv = self.parse_call_conv()?;
        let ret = RetParam {
            attrs: self.parse_param_attrs()?,
            ty: self.parse_type()?,
        };
        let callee = match self.peek_token()? {
            Token::ReservedKeyword("asm") => {
                self.read_token()?;
                let tmpl = self.expect_string()?;
                self.expect_token(&Token::Comma)?;
                let constr = self.expect_string()?;
                Callee::Asm(tmpl, constr)
            }
            _ => Callee::Value(self.parse_value(None)?),
        };
        self.expect_token(&Token::LParen)?;
        let args = self.parse_param_value_list(&Token::RParen)?;
        let attrs = self.parse_attrs()?;
        Ok(CallBody {
            call_conv,
            ret,
            callee,
            args,
            attrs,
        })
    }
    fn parse_call<I: ExtIdent>(&mut self, res: Option<LocalIdent>) -> Result<Insn<I>, String> {
        let tail_mode = match self.peek_token()? {
            Token::ReservedKeyword("musttail") => {
                self.read_token()?;
                Some(TailMode::Musttail)
            }
            Token::ReservedKeyword("notail") => {
                self.read_token()?;
                Some(TailMode::Notail)
            }
            Token::ReservedKeyword("tail") => {
                self.read_token()?;
                Some(TailMode::Tail)
            }
            _ => None,
        };
        let body = self.parse_call_body()?;
        let mut range = None;
        while self.may_expect_token(&Token::Comma)? {
            if self.may_expect_token(&Token::MetadataRef("range"))? {
                range = Some(self.expect_metadata_ref()?);
            } else {
                break;
            }
        }
        Ok(Insn::Call {
            res,
            tail_mode,
            body,
            range,
        })
    }
    fn parse_invoke<I: ExtIdent>(&mut self, res: Option<LocalIdent>) -> Result<Insn<I>, String> {
        let body = self.parse_call_body()?;
        self.expect_token(&Token::ReservedKeyword("to"))?;
        let to = self.parse_label()?;
        self.expect_token(&Token::ReservedKeyword("unwind"))?;
        let unwind = self.parse_label()?;
        Ok(Insn::Invoke {
            res,
            body,
            to,
            unwind,
        })
    }
    fn parse_linkage(&mut self) -> Result<Option<Linkage>, String> {
        let linkage = match self.peek_token()? {
            Token::Keyword("common") => Linkage::Common,
            Token::Keyword("external") => Linkage::External,
            Token::Keyword("internal") => Linkage::Internal,
            Token::Keyword("linkonce_odr") => Linkage::LinkonceOdr,
            Token::Keyword("private") => Linkage::Private,
            _ => return Ok(None),
        };
        self.read_token()?;
        Ok(Some(linkage))
    }
    fn parse_linkages(&mut self) -> Result<Vec<Linkage>, String> {
        let mut linkages = Vec::new();
        while let Some(linkage) = self.parse_linkage()? {
            linkages.push(linkage);
        }
        Ok(linkages)
    }
    fn parse_visibility(&mut self) -> Result<Visibility, String> {
        if self.may_expect_token(&Token::Keyword("default"))? {
            return Ok(Visibility::Default);
        } else if self.may_expect_token(&Token::Keyword("hidden"))? {
            return Ok(Visibility::Hidden);
        } else if self.may_expect_token(&Token::Keyword("protected"))? {
            return Ok(Visibility::Protected);
        }
        Ok(Visibility::Default)
    }
    fn parse_unnamed_addr(&mut self) -> Result<UnnamedAddr, String> {
        if self.may_expect_token(&Token::Keyword("local_unnamed_addr"))? {
            return Ok(UnnamedAddr::Local);
        } else if self.may_expect_token(&Token::Keyword("unnamed_addr"))? {
            return Ok(UnnamedAddr::Normal);
        }
        Ok(UnnamedAddr::None)
    }
    fn parse_func_decl<I: ExtIdent>(&mut self) -> Result<FuncDecl<I>, String> {
        let linkages = self.parse_linkages()?;
        let visibility = self.parse_visibility()?;
        let call_conv = self.parse_call_conv()?;
        let ret = RetParam {
            attrs: self.parse_param_attrs()?,
            ty: self.parse_type()?,
        };
        let name = self.expect_global_ident()?;
        let (args, variadic) = self.parse_arglist()?;
        let unnamed_addr = self.parse_unnamed_addr()?;
        let attrs = self.parse_attrs()?;
        let personality = if self.may_expect_token(&Token::ReservedKeyword("personality"))? {
            Some(self.parse_typed_value()?)
        } else {
            None
        };
        Ok(FuncDecl {
            sig: FuncSig {
                ret: Box::new(ret),
                name: Some(name),
                args,
                variadic,
            },
            attrs,
            linkages,
            visibility,
            call_conv,
            unnamed_addr,
            personality,
        })
    }
    /// Returns a parsed instruction.
    pub fn parse_insn_body<I: ExtIdent>(&mut self) -> Result<Option<Insn<I>>, String> {
        match self.peek_token()? {
            Token::ReservedKeyword("br") => {
                self.read_token()?;
                if self.may_expect_token(&Token::ReservedKeyword("i1"))? {
                    let cond = self.parse_value(None)?;
                    self.expect_token(&Token::Comma)?;
                    let label1 = self.parse_label()?;
                    self.expect_token(&Token::Comma)?;
                    let label2 = self.parse_label()?;
                    Ok(Some(Insn::BrI1(cond, label1, label2)))
                } else {
                    let label = self.parse_label()?;
                    Ok(Some(Insn::Br(label)))
                }
            }
            Token::ReservedKeyword("call")
            | Token::ReservedKeyword("musttail")
            | Token::ReservedKeyword("notail")
            | Token::ReservedKeyword("tail") => Ok(Some(self.parse_call(None)?)),
            Token::ReservedKeyword("indirectbr") => {
                self.read_token()?;
                let tyval = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                self.expect_token(&Token::LBracket)?;
                let mut labels = Vec::new();
                loop {
                    self.may_expect_token(&Token::Comma)?;
                    if let Token::RBracket = self.peek_token()? {
                        break;
                    }
                    labels.push(self.parse_label()?);
                }
                self.expect_token(&Token::RBracket)?;
                Ok(Some(Insn::Indirectbr(tyval, labels)))
            }
            Token::ReservedKeyword("invoke") => Ok(Some(self.parse_invoke(None)?)),
            Token::ReservedKeyword("resume") => {
                self.read_token()?;
                Ok(Some(Insn::Resume(self.parse_typed_value()?)))
            }
            Token::ReservedKeyword("ret") => {
                self.read_token()?;
                let ty = self.parse_type()?;
                if let Type::Void = ty {
                    Ok(Some(Insn::Ret(None)))
                } else {
                    let val = self.parse_value(Some(&ty))?;
                    Ok(Some(Insn::Ret(Some(TypedValue(ty, val)))))
                }
            }
            Token::ReservedKeyword("store") => {
                self.read_token()?;
                let volatile = self.may_expect_token(&Token::Keyword("volatile"))?;
                let src = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let dst = self.parse_typed_value()?;
                let align = self.may_parse_optional_align()?;
                Ok(Some(Insn::Store {
                    volatile,
                    src,
                    dst,
                    align,
                }))
            }
            Token::ReservedKeyword("switch") => {
                self.read_token()?;
                let value = self.parse_typed_value()?;
                self.expect_token(&Token::Comma)?;
                let default = self.parse_label()?;
                let mut cases = Vec::new();
                self.expect_token(&Token::LBracket)?;
                while !self.may_expect_token(&Token::RBracket)? {
                    let value = self.parse_typed_value()?;
                    self.expect_token(&Token::Comma)?;
                    let label = self.parse_label()?;
                    cases.push((value, label));
                }
                Ok(Some(Insn::Switch(value, default, cases)))
            }
            Token::ReservedKeyword("unreachable") => {
                self.read_token()?;
                Ok(Some(Insn::Unreachable))
            }
            Token::LocalIdent(name) => {
                let name = LocalIdent::from(*name);
                self.read_token()?;
                self.expect_token(&Token::Eq)?;
                if let Some(args) = self.parse_aggop()? {
                    return Ok(Some(Insn::Value(name, Value::AggOp(Box::new(args)))));
                } else if let Some(args) = self.parse_binop()? {
                    return Ok(Some(Insn::Value(name, Value::BinOp(Box::new(args)))));
                } else if let Some(args) = self.parse_cmpop()? {
                    return Ok(Some(Insn::Value(name, Value::CmpOp(Box::new(args)))));
                } else if let Some(args) = self.parse_convop()? {
                    return Ok(Some(Insn::Value(name, Value::ConvOp(Box::new(args)))));
                } else if let Some(args) = self.parse_unop()? {
                    return Ok(Some(Insn::Value(name, Value::UnOp(Box::new(args)))));
                } else if let Some(args) = self.parse_vecop()? {
                    return Ok(Some(Insn::Value(name, Value::VecOp(Box::new(args)))));
                }
                match self.peek_token()? {
                    Token::ReservedKeyword("alloca") => {
                        self.read_token()?;
                        let ty = self.parse_type()?;
                        let align = self.may_parse_optional_align()?;
                        Ok(Some(Insn::Alloca {
                            res: name,
                            ty,
                            align,
                        }))
                    }
                    Token::ReservedKeyword("call")
                    | Token::ReservedKeyword("musttail")
                    | Token::ReservedKeyword("notail")
                    | Token::ReservedKeyword("tail") => Ok(Some(self.parse_call(Some(name))?)),
                    Token::ReservedKeyword("getelementptr") => {
                        let args = self.parse_getelementptr()?;
                        let val = Value::Getelementptr(Box::new(args));
                        Ok(Some(Insn::Value(name, val)))
                    }
                    Token::ReservedKeyword("invoke") => Ok(Some(self.parse_invoke(Some(name))?)),
                    Token::ReservedKeyword("landingpad") => {
                        self.read_token()?;
                        let ty = self.parse_type()?;
                        let cleanup = self.may_expect_token(&Token::Keyword("cleanup"))?;
                        let mut clauses = Vec::new();
                        while let Token::ReservedKeyword(kind @ "catch")
                        | Token::ReservedKeyword(kind @ "filter") = self.peek_token()?
                        {
                            let kind = <&str>::clone(kind);
                            self.read_token()?;
                            let tyval = self.parse_typed_value()?;
                            clauses.push(match kind {
                                "catch" => LandingpadClause::Catch(tyval),
                                "filter" => LandingpadClause::Filter(tyval),
                                kind => unreachable!("{}", kind),
                            });
                        }
                        Ok(Some(Insn::Landingpad {
                            res: name,
                            ty,
                            cleanup,
                            clauses,
                        }))
                    }
                    Token::ReservedKeyword("load") => {
                        self.read_token()?;
                        let volatile = self.may_expect_token(&Token::Keyword("volatile"))?;
                        let ty = self.parse_type()?;
                        self.expect_token(&Token::Comma)?;
                        let src = self.parse_typed_value()?;
                        let align = self.may_parse_optional_align()?;
                        Ok(Some(Insn::Load {
                            res: name,
                            volatile,
                            ty,
                            src,
                            align,
                        }))
                    }
                    Token::ReservedKeyword("phi") => {
                        self.read_token()?;
                        let ty = self.parse_type()?;
                        let mut val_labels = Vec::new();
                        loop {
                            match self.peek_token()? {
                                Token::Comma => {
                                    self.read_token()?;
                                }
                                Token::LBracket => {
                                    self.read_token()?;
                                    let val = self.parse_value(Some(&ty))?;
                                    self.expect_token(&Token::Comma)?;
                                    let label = match self.peek_token()? {
                                        Token::LocalIdent(name) => {
                                            let name = LocalIdent::from(*name);
                                            self.read_token()?;
                                            Label::from(name)
                                        }
                                        tk => {
                                            return Err(format!(
                                                "expected label, but got {:?}",
                                                tk
                                            ));
                                        }
                                    };
                                    self.expect_token(&Token::RBracket)?;
                                    val_labels.push((val, label));
                                }
                                _ => break,
                            }
                        }
                        Ok(Some(Insn::Phi {
                            res: name,
                            ty,
                            val_labels,
                        }))
                    }
                    Token::ReservedKeyword("select") => {
                        self.read_token()?;
                        let cond = self.parse_typed_value()?;
                        self.expect_token(&Token::Comma)?;
                        let tyval0 = self.parse_typed_value()?;
                        self.expect_token(&Token::Comma)?;
                        let tyval1 = self.parse_typed_value()?;
                        Ok(Some(Insn::Select(name, cond, tyval0, tyval1)))
                    }
                    tk => return Err(format!("unknown opcode {:?}", tk)),
                }
            }
            _ => Ok(None),
        }
    }
    fn parse_metadata_entry<I: ExtIdent>(&mut self) -> Result<Metadata<I>, String> {
        match self.peek_token()? {
            Token::ReservedKeyword("null") => {
                self.read_token()?;
                Ok(Metadata::Null)
            }
            Token::ReservedKeyword("false") => {
                self.read_token()?;
                Ok(Metadata::Bool(false))
            }
            Token::ReservedKeyword("true") => {
                self.read_token()?;
                Ok(Metadata::Bool(true))
            }
            Token::Keyword(key) => {
                let key = key.to_string();
                self.read_token()?;
                Ok(Metadata::Keyword(key))
            }
            Token::String(s) => {
                let s = s.to_string();
                self.read_token()?;
                Ok(Metadata::String(s))
            }
            Token::Number(_) => Ok(Metadata::Number(self.expect_number()?)),
            Token::MetadataRef(name) => {
                let name = MetadataRef::new(name.to_string());
                self.read_token()?;
                if let Token::LParen = self.peek_token()? {
                    self.read_token()?;
                    if let Token::Label(_) = self.peek_token()? {
                        let mut kvs = BTreeMap::new();
                        loop {
                            self.may_expect_token(&Token::Comma)?;
                            if self.may_expect_token(&Token::RParen)? {
                                break;
                            }
                            let key = self.expect_label()?;
                            let value = self.parse_metadata()?;
                            if kvs.contains_key(&key) {
                                return Err(format!("key {} is redefined", key));
                            }
                            kvs.insert(key, value);
                        }
                        return Ok(Metadata::KeyValues(name, kvs));
                    } else {
                        let mut fields = Vec::new();
                        loop {
                            self.may_expect_token(&Token::Comma)?;
                            if self.may_expect_token(&Token::RParen)? {
                                break;
                            }
                            let value = self.parse_metadata()?;
                            fields.push(value);
                        }
                        return Ok(Metadata::Values(name, fields));
                    }
                }
                Ok(Metadata::Ref(name))
            }
            Token::Exclam => match self.read_token()? {
                Token::String(s) => {
                    let s = s.to_string();
                    self.read_token()?;
                    Ok(Metadata::Keyword(s))
                }
                Token::LBrace => {
                    self.read_token()?;
                    let mut values = Vec::new();
                    loop {
                        self.may_expect_token(&Token::Comma)?;
                        if self.may_expect_token(&Token::RBrace)? {
                            break;
                        }
                        values.push(self.parse_metadata()?);
                    }
                    Ok(Metadata::Struct(values))
                }
                tk => Err(format!("unexpected {:?} after `!`", tk)),
            },
            _ => Ok(Metadata::TypedValue(self.parse_typed_value()?)),
        }
    }
    fn parse_metadata<I: ExtIdent>(&mut self) -> Result<Metadata<I>, String> {
        let value = self.parse_metadata_entry()?;
        if self.may_expect_token(&Token::Vline)? {
            let mut values = vec![value];
            loop {
                values.push(self.parse_metadata_entry()?);
                if !self.may_expect_token(&Token::Vline)? {
                    break;
                }
            }
            return Ok(Metadata::Or(values));
        }
        Ok(value)
    }
    fn parse_metadata_list_in(&mut self, mdlist: &mut MetadataList) -> Result<(), String> {
        self.may_expect_token(&Token::Comma)?;
        while let Token::MetadataRef(name) = self.peek_token()? {
            let name = name.to_string();
            self.read_token()?;
            let metadata = self.expect_metadata_ref()?;
            mdlist.insert(name, metadata);
            if !self.may_expect_token(&Token::Comma)? {
                break;
            }
        }
        Ok(())
    }
    /// Returns a parsed instruction with metadata.
    pub fn parse_insn<I: ExtIdent>(&mut self) -> Result<Option<(Insn<I>, MetadataList)>, String> {
        let insn = match self.parse_insn_body()? {
            Some(insn) => insn,
            None => return Ok(None),
        };
        let mut mdlist = MetadataList::empty();
        self.parse_metadata_list_in(&mut mdlist)?;
        Ok(Some((insn, mdlist)))
    }
    /// Returns a parsed statement with metadata.
    pub fn parse_stmt<I: ExtIdent>(&mut self) -> Result<Option<(Stmt<I>, MetadataList)>, String> {
        let mut mdlist = MetadataList::empty();
        let stmt = match self.peek_token()? {
            Token::None => return Ok(None),
            Token::ReservedKeyword("source_filename") => {
                self.read_token()?;
                self.expect_token(&Token::Eq)?;
                Stmt::SourceFilename(self.expect_string()?)
            }
            Token::ReservedKeyword("target") => match self.read_token()? {
                Token::ReservedKeyword("triple") => {
                    self.read_token()?;
                    self.expect_token(&Token::Eq)?;
                    Stmt::TargetTriple(self.expect_string()?)
                }
                Token::ReservedKeyword("datalayout") => {
                    self.read_token()?;
                    self.expect_token(&Token::Eq)?;
                    Stmt::TargetDatalayout(self.expect_string()?)
                }
                tk => return Err(format!("unexpected {:?} after `target`", tk)),
            },
            Token::LocalIdent(name) => {
                let name = LocalIdent::from(*name);
                self.read_token()?;
                self.expect_token(&Token::Eq)?;
                match self.peek_token()? {
                    Token::ReservedKeyword("type") => {
                        self.read_token()?;
                        let ty = self.parse_type()?;
                        Stmt::Typedef(name, ty)
                    }
                    tk => return Err(format!("unknown opcode {:?}", tk)),
                }
            }
            Token::GlobalIdent(name) => {
                let name = GlobalIdent::from(*name);
                self.read_token()?;
                self.expect_token(&Token::Eq)?;
                let linkages = self.parse_linkages()?;
                let visibility = self.parse_visibility()?;
                let unnamed_addr = self.parse_unnamed_addr()?;
                let is_const = match self.peek_token()? {
                    Token::ReservedKeyword("constant") => true,
                    Token::ReservedKeyword("global") => false,
                    tk => {
                        return Err(format!("expected constant or global, but got {:?}", tk));
                    }
                };
                self.read_token()?;
                let ty = self.parse_type()?;
                let value = match linkages.contains(&Linkage::External) {
                    true => None,
                    false => Some(self.parse_value(Some(&ty))?),
                };
                let align = self.may_parse_optional_align()?;
                Stmt::Global {
                    name,
                    is_const,
                    ty,
                    value,
                    linkages,
                    visibility,
                    unnamed_addr,
                    align,
                }
            }
            Token::ReservedKeyword("declare") => {
                self.read_token()?;
                self.parse_metadata_list_in(&mut mdlist)?;
                Stmt::Func(self.parse_func_decl()?, Blocks::empty())
            }
            Token::ReservedKeyword("define") => {
                self.read_token()?;
                let decl = self.parse_func_decl()?;
                let mut mdlist = MetadataList::empty();
                if self.may_expect_token(&Token::MetadataRef("dbg"))? {
                    mdlist.insert(String::from("dbg"), self.expect_metadata_ref()?);
                }
                let mut builder = BlocksBuilder::new(decl.sig.args.len());
                self.expect_token(&Token::LBrace)?;
                loop {
                    if self.may_expect_token(&Token::RBrace)? {
                        break;
                    }
                    if let Token::Label(name) = self.peek_token()? {
                        let name = Label::from(LocalIdent::from(*name));
                        self.read_token()?;
                        builder.set_label(name);
                        continue;
                    }
                    match self.parse_insn()? {
                        Some((insn, mdlist)) => match &insn {
                            Insn::Br(label) => {
                                let label = *label;
                                builder.push_insn(insn, mdlist, false);
                                builder.set_br(vec![label]);
                            }
                            Insn::BrI1(_, label1, label2) => {
                                let label1 = *label1;
                                let label2 = *label2;
                                builder.push_insn(insn, mdlist, false);
                                builder.set_br(vec![label1, label2]);
                            }
                            Insn::Indirectbr(_, labels) => {
                                let labels = labels.clone();
                                builder.push_insn(insn, mdlist, false);
                                builder.set_br(labels);
                            }
                            Insn::Invoke {
                                res, to, unwind, ..
                            } => {
                                let has_result = res.is_some();
                                let label1 = *to;
                                let label2 = *unwind;
                                builder.push_insn(insn, mdlist, has_result);
                                builder.set_br(vec![label1, label2]);
                            }
                            Insn::Resume(_) | Insn::Ret(_) | Insn::Unreachable => {
                                builder.push_insn(insn, mdlist, false);
                                builder.set_br(vec![]);
                            }
                            Insn::Switch(_, default, cases) => {
                                let mut labels = vec![*default];
                                for (_, label) in cases {
                                    labels.push(*label);
                                }
                                builder.push_insn(insn, mdlist, false);
                                builder.set_br(labels);
                            }
                            _ => {
                                let has_result = insn.res().is_some();
                                builder.push_insn(insn, mdlist, has_result);
                            }
                        },
                        None => return Err("unexpected termination of function".to_string()),
                    }
                }
                return Ok(Some((Stmt::Func(decl, builder.finish()?), mdlist)));
            }
            Token::ReservedKeyword("attributes") => {
                self.read_token()?;
                let id = self.expect_attr_ref()?;
                self.expect_token(&Token::Eq)?;
                self.expect_token(&Token::LBrace)?;
                let attrs = self.parse_attrs()?;
                self.expect_token(&Token::RBrace)?;
                Stmt::Attrs(id, attrs)
            }
            Token::MetadataRef(name) => {
                let name = name.to_string();
                self.read_token()?;
                self.expect_token(&Token::Eq)?;
                let distinct = self.may_expect_token(&Token::Keyword("distinct"))?;
                let metadata = self.parse_metadata()?;
                Stmt::Metadata(MetadataRef::new(name), distinct, metadata)
            }
            tk => return Err(format!("unexpected {:?} in statement", tk)),
        };
        if let Token::Comma = self.peek_token()? {
            self.parse_metadata_list_in(&mut mdlist)?;
        }
        Ok(Some((stmt, mdlist)))
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
    use crate::fmt::DisplayMapIter;
    use crate::llir::abi::DataLayout;
    macro_rules! trim_spaces_from_string {
        ($s:expr) => {
            $s.split_whitespace().collect::<Vec<_>>().join(" ")
        };
    }
    macro_rules! new_metadata_list {
        ($name:expr, $metadata:expr) => {{
            let mut mdlist = MetadataList::empty();
            mdlist.insert($name, $metadata);
            mdlist
        }};
    }
    #[test]
    fn parse_param_attr() {
        let source_expected_list = vec![
            (
                "align 8",
                ParamAttr(String::from("align"), Some(ParamAttrArg::U32(8))),
            ),
            (
                "byref(i32)",
                ParamAttr(
                    String::from("byref"),
                    Some(ParamAttrArg::<ExtIdentUnit>::Type(Type::I32)),
                ),
            ),
            (
                "byval(i8)",
                ParamAttr(
                    String::from("byval"),
                    Some(ParamAttrArg::<ExtIdentUnit>::Type(Type::I8)),
                ),
            ),
            (
                "dereferenceable(8)",
                ParamAttr(String::from("dereferenceable"), Some(ParamAttrArg::U32(8))),
            ),
            ("noalias", ParamAttr(String::from("noalias"), None)),
        ];
        for (source, expected) in source_expected_list {
            let mut parser = Parser::new(source, "input").expect(source);
            let attr = parser
                .parse_param_attr::<ExtIdentUnit>()
                .expect(source)
                .expect(source);
            assert_eq!(expected.to_string(), attr.to_string(), "{}", source);
        }
    }
    #[test]
    fn parse_type() {
        for ty in vec![
            "void",
            "i1",
            "i8",
            "i16",
            "i32",
            "i64",
            "float",
            "double",
            "x86_fp80",
            "<4 x i32>",
            "<vscale x 4 x i32>",
            "[4 x i32]",
            "{  }",
            "{ i32 }",
            "{ i32, i16 }",
            "<{ i32, i16 }>",
            "opaque",
            "%struct.Tuple2",
        ] {
            assert_eq!(ty, Parser::new_type::<ExtIdentUnit>(&ty).to_string());
        }
    }
    #[test]
    fn parse_typed_value() {
        for tyval in vec![
            "i8* null",
            "i32 undef",
            "i1 false",
            "i1 true",
            "i8 8",
            "i16 16",
            "i32 32",
            "i64 64",
            "float 3.2",
            "double 6.4",
            "double 6.400000e+64",
            "double 0x46AF8DEF80000000",
            "x86_fp80 0xK7FFF8000000000000000",
            "<4 x i32> <i32 1, i32 2, i32 3, i32 4>",
            r#"[5 x i8] c"HELLO""#,
            "[4 x i32] [i32 1, i32 2, i32 3, i32 4]",
            "{  } {  }",
            "{ i64 } { i64 1 }",
            "{ i64, i16 } { i64 1, i16 2 }",
            "i32 %1",
            "i8* @str",
            "i32 extractvalue ({ i8*, i32 } %1, 0)",
            "{ i8*, i32 } insertvalue ({ i8*, i32 } undef, i8* %1, 0)",
            "i64 add (i64 %1, i64 %2)",
            "i64 add nuw (i64 %1, i64 %2)",
            "i64 add nsw (i64 %1, i64 %2)",
            "i64 add nuw nsw (i64 %1, i64 %2)",
            "i64 and (i64 %1, i64 %2)",
            "i64 ashr (i64 %1, i64 %2)",
            "i64 ashr exact (i64 %1, i64 %2)",
            "double fadd (double %1, double %2)",
            "double fdiv (double %1, double %2)",
            "double fmul (double %1, double %2)",
            "double frem (double %1, double %2)",
            "double fsub (double %1, double %2)",
            "i64 lshr (i64 %1, i64 %2)",
            "i64 lshr exact (i64 %1, i64 %2)",
            "i64 mul (i64 %1, i64 %2)",
            "i64 mul nuw (i64 %1, i64 %2)",
            "i64 mul nsw (i64 %1, i64 %2)",
            "i64 mul nuw nsw (i64 %1, i64 %2)",
            "i64 or (i64 %1, i64 %2)",
            "i64 sdiv (i64 %1, i64 %2)",
            "i64 sdiv exact (i64 %1, i64 %2)",
            "i64 shl (i64 %1, i64 %2)",
            "i64 shl nuw (i64 %1, i64 %2)",
            "i64 shl nsw (i64 %1, i64 %2)",
            "i64 shl nuw nsw (i64 %1, i64 %2)",
            "i64 srem (i64 %1, i64 %2)",
            "i64 sub (i64 %1, i64 %2)",
            "i64 sub nuw (i64 %1, i64 %2)",
            "i64 sub nsw (i64 %1, i64 %2)",
            "i64 sub nuw nsw (i64 %1, i64 %2)",
            "i64 udiv (i64 %1, i64 %2)",
            "i64 udiv exact (i64 %1, i64 %2)",
            "i64 urem (i64 %1, i64 %2)",
            "i64 xor (i64 %1, i64 %2)",
            "i1 fcmp false (float %1, float %2)",
            "i1 fcmp oeq (float %1, float %2)",
            "i1 fcmp ogt (float %1, float %2)",
            "i1 fcmp oge (float %1, float %2)",
            "i1 fcmp olt (float %1, float %2)",
            "i1 fcmp ole (float %1, float %2)",
            "i1 fcmp one (float %1, float %2)",
            "i1 fcmp ord (float %1, float %2)",
            "i1 fcmp ueq (float %1, float %2)",
            "i1 fcmp ugt (float %1, float %2)",
            "i1 fcmp uge (float %1, float %2)",
            "i1 fcmp ult (float %1, float %2)",
            "i1 fcmp ule (float %1, float %2)",
            "i1 fcmp une (float %1, float %2)",
            "i1 fcmp uno (float %1, float %2)",
            "i1 fcmp true (float %1, float %2)",
            "i1 icmp eq (i32 %1, i32 %2)",
            "i1 icmp ne (i32 %1, i32 %2)",
            "i1 icmp ugt (i32 %1, i32 %2)",
            "i1 icmp uge (i32 %1, i32 %2)",
            "i1 icmp ult (i32 %1, i32 %2)",
            "i1 icmp ule (i32 %1, i32 %2)",
            "i1 icmp sgt (i32 %1, i32 %2)",
            "i1 icmp sge (i32 %1, i32 %2)",
            "i1 icmp slt (i32 %1, i32 %2)",
            "i1 icmp sle (i32 %1, i32 %2)",
            "i8* bitcast (i32* %1 to i8*)",
            "double fpext (float %1 to double)",
            "i64 fptosi (float %1 to i64)",
            "i64 fptoui (float %1 to i64)",
            "float fptrunc (double %12 to float)",
            "i64 ptrtoint (i32* %1 to i64)",
            "i8* inttoptr (i64 %1 to i8*)",
            "i64 sext (i32 %1 to i64)",
            "double sitofp (i64 %1 to double)",
            "i32 trunc (i64 %1 to i32)",
            "double uitofp (i64 %1 to double)",
            "i64 zext (i32 %1 to i64)",
            "i32 getelementptr (%struct.A, %struct.A* %1, i32 0, i32 1)",
            "i8* getelementptr inbounds ({ [3 x i8*] }, { [3 x i8*] }* @var, i32 0, inrange i32 0, i32 2)",
            "i8* getelementptr inbounds (i8, i8* %25, i64 -8)",
            "i32 extractelement (<4 x i32> %1, i32 0)",
            "double fneg (double %1)",
            "<4 x i32> insertelement (<4 x i32> %1, i32 1, i32 0)",
            "<4 x i32> shufflevector (<4 x i32> %1, <4 x i32> %2, <1 x i32> <i32 0>)",
            "[4 x i32] zeroinitializer",
            "i8* blockaddress(@execute, %42)",
            "metadata !1",
        ] {
            assert_eq!(tyval, Parser::new_typed_value::<ExtIdentUnit>(&tyval).to_string());
        }
    }
    #[test]
    fn parse_linkages() {
        let mut parser =
            Parser::new("common external internal linkonce_odr private", "input").unwrap();
        assert_eq!(
            vec![
                Linkage::Common,
                Linkage::External,
                Linkage::Internal,
                Linkage::LinkonceOdr,
                Linkage::Private
            ],
            parser.parse_linkages().unwrap()
        );
    }
    #[test]
    fn parse_visibility() {
        for (expected, input) in vec![
            (Visibility::Default, "default"),
            (Visibility::Hidden, "hidden"),
            (Visibility::Protected, "protected"),
            (Visibility::Default, ""),
        ] {
            let mut parser = Parser::new(input, "input").expect(input);
            let got = parser.parse_visibility().expect(input);
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn parse_unnamed_addr() {
        for (expected, input) in vec![
            (UnnamedAddr::Local, "local_unnamed_addr"),
            (UnnamedAddr::Normal, "unnamed_addr"),
            (UnnamedAddr::None, ""),
        ] {
            let mut parser = Parser::new(input, "input").expect(input);
            let got = parser.parse_unnamed_addr().expect(input);
            assert_eq!(expected, got, "{}", input);
        }
    }
    fn run_parse_insn(source: &str, expected: (&str, &MetadataList)) -> Result<(), String> {
        let mut parser = Parser::new(source, "input")?;
        let (insn, mdlist) = match parser.parse_insn::<ExtIdentUnit>()? {
            Some(res) => res,
            None => return Err(format!("unexpected None from parse_insn")),
        };
        let expected_insnstr = trim_spaces_from_string!(expected.0);
        let insnstr = trim_spaces_from_string!(insn.to_string());
        if expected_insnstr != insnstr {
            return Err(format!(
                "insn not matched: {} <> {}",
                expected_insnstr, insnstr
            ));
        }
        if expected.1 != &mdlist {
            return Err(format!(
                "mdlist not matched: {} <> {}",
                DisplayMapIter("{", expected.1.iter(), ": ", ", ", "}"),
                DisplayMapIter("{", mdlist.iter(), ": ", ", ", "}"),
            ));
        }
        Ok(())
    }
    #[test]
    fn parse_insn() {
        let source_expected_list = vec![
            // aggop
            (
                "%2 = extractvalue { i8*, i32 } %1, 0",
                Some("%2 = extractvalue ({ i8*, i32 } %1, 0)")
            ),
            (
                "%2 = insertvalue { i8*, i32 } undef, i8* %1, 0",
                Some("%2 = insertvalue ({ i8*, i32 } undef, i8* %1, 0)")
            ),
            // alloca
            ("%1 = alloca i32", None),
            ("%1 = alloca i32, align 4", None),
            // binop: all patterns are tested in parse_typed_value.
            ("%2 = add i64 %1, 1", Some("%2 = add (i64 %1, i64 1)")),
            // br
            ("br label %1", None),
            ("br i1 %1, label %2, label %3", None),
            // call
            ("call void @func(i64 %1) #4", None),
            ("musttail call void %1(i64 %2, i32 %3)", None),
            ("notail call void @func(i64 %1)", None),
            ("tail call void @func()", None),
            ("%2 = call void @func(i64 %1)", None),
            ("%4 = musttail call void %1(i64 %2, i32 %3)", None),
            ("%2 = notail call void @func(i64 %1)", None),
            ("%1 = tail call void @func()", None),
            ("call void @func(i64 %1) #4, !range !8", None),
            ("%2 = call nonull i8* @func(i64* align(1) %1) #4, !range !8", None),
            ("%2 = call zeroext i1 @func(i64* dereferenceable(8) %1) #4, !range !8", None),
            ("%3 = call i32 (i8*, ...) @printf(i8* @.str.1, i64 %1, i64 %2)", None),
            (r#"%2 = call i32 asm "bswap $0", "=r,0,~{dirflag},~{fpsr},~{flags}"(i32 %1)"#, None),
            ("call void @llvm.dbg.declare(metadata i32* %1, metadata !2, metadata !DIExpression())", None),
            // cmpop: all patterns are tested in parse_typed_value.
            (
                "%3 = fcmp oeq float %1, %2",
                Some("%3 = fcmp oeq (float %1, float %2)")
            ),
            (
                "%3 = icmp eq i32 %1, %2",
                Some("%3 = icmp eq (i32 %1, i32 %2)")
            ),
            // convop: all patterns are tested in parse_typed_value.
            (
                "%2 = bitcast i32* %1 to i8*",
                Some("%2 = bitcast (i32* %1 to i8*)")
            ),
            // getelementptr: all patterns are tested in parse_typed_value.
            (
                "%2 = getelementptr %struct.A, %struct.A* %1, i32 0, i32 1",
                Some("%2 = getelementptr (%struct.A, %struct.A* %1, i32 0, i32 1)")
            ),
            // indirectbr
            ("indirectbr i8* %1, [label %2, label %3]", None),
            // invoke
            ("invoke void @func(i64 %1) to label %2 unwind label %3", None),
            ("%2 = invoke i32 @func(i8* %1) #14 to label %3 unwind label %4", None),
            ("%2 = invoke dereferenceable(8) i8* @func(i8* %1) to label %3 unwind label %4", None),
            // landingpad
            ("%1 = landingpad { i8*, i32 }", None),
            ("%1 = landingpad { i8*, i32 } cleanup", None),
            ("%1 = landingpad { i8*, i32 } catch i8* null", None),
            ("%1 = landingpad { i8*, i32 } filter [0 x i8*] zeroinitializer", None),
            // load
            ("%2 = load i8*, i8** %1", None),
            ("%2 = load volatile i8*, i8** %1, align 8", None),
            // phi
            ("%4 = phi %class.Derived1* [ %2, %1 ], [ null, %3 ]", None),
            // resume
            ("resume { i8*, i32 } %1", None),
            // ret
            ("ret void", None),
            ("ret i32 1", None),
            // select
            ("%2 = select i1 %1, i64 0, i64 1", None),
            // store
            ("store i32 0, i32* %1", None),
            ("store volatile i32* bitcast (i64 %1 to i32*), i32** %2, align 8", None),
            // switch
            (r#"
            switch i32 %34, label %235 [
              i32 1, label %39
              i32 2, label %54
            ]
            "#, None),
            // unreachable
            ("unreachable", None),
            // vecop
            (
                "%2 = extractelement <4 x i32> %1, i32 0",
                Some("%2 = extractelement (<4 x i32> %1, i32 0)")
            ),
            (
                "%2 = insertelement <4 x i32> %1, i32 1, i32 0",
                Some("%2 = insertelement (<4 x i32> %1, i32 1, i32 0)")
            ),
            (
                "%3 = shufflevector <4 x i32> %1, <4 x i32> %2, <1 x i32> <i32 0>",
                Some("%3 = shufflevector (<4 x i32> %1, <4 x i32> %2, <1 x i32> <i32 0>)")
            ),
        ];
        for (source, expected) in source_expected_list {
            let expected = expected.unwrap_or(source);
            let mdlist = MetadataList::empty();
            run_parse_insn(source, (expected, &mdlist)).expect(&source);
            let source = format!("{}, !dbg !0", source);
            let mdlist =
                new_metadata_list!(String::from("dbg"), MetadataRef::new(String::from("0")));
            run_parse_insn(&source, (expected, &mdlist)).expect(&source);
        }
    }
    #[test]
    fn parse_source_filename() {
        let source = r#"
            ; ModuleID = 'main.cpp'
            source_filename = "main.cpp"
            "#;
        let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>(source);
        assert_eq!(Stmt::SourceFilename(String::from("main.cpp")), stmt);
        assert_eq!(MetadataList::empty(), mdlist);
    }
    #[test]
    fn parse_target() {
        let expected_source_list = vec![
            (
                Stmt::TargetTriple(String::from("x86_64-apple-macosx10.15.0")),
                r#"target triple = "x86_64-apple-macosx10.15.0""#,
            ),
            (
                Stmt::TargetDatalayout(String::from("e-m:o-i64:64-f80:128-n8:16:32:64-S128")),
                r#"target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128""#,
            ),
        ];
        for (expected, source) in expected_source_list {
            let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>(source);
            assert_eq!(expected, stmt);
            assert_eq!(MetadataList::empty(), mdlist);
        }
    }
    #[test]
    fn parse_typedef() {
        let (expected_name, expected_ty) = ("%struct.X", "{ i8, i16, i32, i64 }");
        let source = format!("{} = type {}", expected_name, expected_ty);
        let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>(&source);
        match stmt {
            Stmt::Typedef(name, ty) => {
                assert_eq!(expected_name, name.to_string());
                assert_eq!(expected_ty, ty.to_string());
            }
            _ => panic!("unexpected stmt {:?}", stmt),
        }
        assert_eq!(MetadataList::empty(), mdlist);
    }
    #[test]
    fn parse_global() {
        for (
            expected_name,
            expected_is_const,
            expected_ty,
            expected_value,
            expected_linkages,
            expected_visibility,
            expected_unnamed_addr,
            expected_align,
            input,
        ) in vec![
            (
                "@.str",
                true,
                "[17 x i8]",
                r#"Some(c"Class0(x=%lld)\\\n\u{0}")"#,
                vec![Linkage::Private],
                Visibility::Default,
                UnnamedAddr::Normal,
                Some(1),
                r#"@.str = private unnamed_addr constant [17 x i8] c"Class0(x=%lld)\\\0A\00", align 1"#,
            ),
            (
                "@data",
                false,
                "i8*",
                r#"Some(null)"#,
                vec![],
                Visibility::Default,
                UnnamedAddr::None,
                None,
                r#"@data = global i8* null"#,
            ),
            (
                "@_ZTISt12length_error",
                true,
                "i8*",
                r#"None"#,
                vec![Linkage::External],
                Visibility::Default,
                UnnamedAddr::None,
                None,
                r#"@_ZTISt12length_error = external constant i8*"#,
            ),
        ] {
            let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>(input);
            match stmt {
                Stmt::Global {
                    name,
                    is_const,
                    ty,
                    value,
                    linkages,
                    visibility,
                    unnamed_addr,
                    align,
                } => {
                    assert_eq!(expected_name, name.to_string(), "{}", input);
                    assert_eq!(expected_is_const, is_const, "{}", input);
                    assert_eq!(expected_ty, ty.to_string(), "{}", input);
                    let value = match value {
                        Some(val) => format!("Some({})", val),
                        None => format!("None"),
                    };
                    assert_eq!(expected_value, value.to_string(), "{}", input);
                    assert_eq!(expected_linkages, linkages, "{}", input);
                    assert_eq!(expected_visibility, visibility, "{}", input);
                    assert_eq!(expected_unnamed_addr, unnamed_addr, "{}", input);
                    assert_eq!(expected_align, align, "{}", input);
                }
                _ => panic!("expected global stmt, but got {:?}: {}", stmt, input),
            }
            assert_eq!(mdlist, MetadataList::empty(), "{}", input);
        }
    }
    macro_rules! assert_parse_stmt_func {
        ($source:expr, $expected_sig:expr, $expected_attrs:expr, $expected_linkages:expr, $expected_visibility:expr, $expected_call_conv:expr, $expected_unnamed_addr:expr, $expected_personality:expr, $expected_mdlist:expr) => {{
            let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>($source);
            let blocks = match stmt {
                Stmt::Func(
                    FuncDecl {
                        sig,
                        attrs,
                        linkages,
                        visibility,
                        call_conv,
                        unnamed_addr,
                        personality,
                    },
                    blocks,
                ) => {
                    assert_eq!($expected_sig, sig.to_string(), "sig not matched");
                    assert_eq!(
                        $expected_attrs as &[Attr<ExtIdentUnit>], &attrs as &[Attr<ExtIdentUnit>],
                        "attrs not matched"
                    );
                    assert_eq!(
                        $expected_linkages as &[Linkage], &linkages as &[Linkage],
                        "linkages not matched"
                    );
                    assert_eq!($expected_visibility, visibility, "visibility not matched");
                    assert_eq!($expected_call_conv, call_conv, "call_conv not matched");
                    assert_eq!(
                        $expected_unnamed_addr, unnamed_addr,
                        "unnamed_addr not matched"
                    );
                    assert_eq!(
                        $expected_personality,
                        personality.and_then(|p| Some(p.to_string())),
                        "personality not matched"
                    );
                    blocks
                }
                _ => panic!("expected func stmt, but got {:?}", stmt),
            };
            assert_eq!($expected_mdlist, mdlist, "mdlist not matched");
            blocks
        }};
    }
    #[test]
    fn parse_declare() {
        let blocks1 = assert_parse_stmt_func!(
            r#"declare !dbg !1 i32 @printf(i8*, ...) #3"#,
            r#"i32 @printf(i8*, ...)"#,
            &[Attr::Ref(3)],
            &[],
            Visibility::Default,
            None,
            UnnamedAddr::None,
            None,
            new_metadata_list!(String::from("dbg"), MetadataRef::new(String::from("1")))
        );
        assert_eq!(0, blocks1.len());
        let blocks2 = assert_parse_stmt_func!(
            r#"declare fastcc noalias i8* @_Znwm(i64) #3"#,
            r#"noalias i8* @_Znwm(i64)"#,
            &[Attr::Ref(3)],
            &[],
            Visibility::Default,
            Some(CallConv::Fastcc),
            UnnamedAddr::None,
            None,
            MetadataList::empty()
        );
        assert_eq!(0, blocks2.len());
        let blocks3 = assert_parse_stmt_func!(
            r#"declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1 immarg) #3"#,
            r#"void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1 immarg)"#,
            &[Attr::Ref(3)],
            &[],
            Visibility::Default,
            None,
            UnnamedAddr::None,
            None,
            MetadataList::empty()
        );
        assert_eq!(0, blocks3.len());
    }
    #[test]
    fn parse_define() {
        let blocks1 = assert_parse_stmt_func!(
            r#"
            define i32 @main() #0 !dbg !9 {
              %1 = alloca i32, align 4
              store i32 0, i32* %1, align 4, !tbaa !4
              ret i32 0, !dbg !13
            }
            "#,
            r#"i32 @main()"#,
            &[Attr::Ref(0)],
            &[],
            Visibility::Default,
            None,
            UnnamedAddr::None,
            None,
            new_metadata_list!(String::from("dbg"), MetadataRef::new(String::from("9")))
        );
        assert_eq!(1, blocks1.len());
        assert_eq!("label %0", blocks1.get(0).unwrap().name.to_string());
        assert_eq!(0, blocks1.get(0).unwrap().preds.len());
        assert_eq!(0, blocks1.get(0).unwrap().succs.len());
        assert_eq!(3, blocks1.get(0).unwrap().insns.len());
        assert_eq!(
            "%1 = alloca i32, align 4",
            blocks1.get(0).unwrap().insns[0].to_string()
        );
        assert_eq!(
            "store i32 0, i32* %1, align 4",
            blocks1.get(0).unwrap().insns[1].to_string()
        );
        assert_eq!("ret i32 0", blocks1.get(0).unwrap().insns[2].to_string());
        assert_eq!(
            vec![
                MetadataList::empty(),
                new_metadata_list!(String::from("tbaa"), MetadataRef::new(String::from("4"))),
                new_metadata_list!(String::from("dbg"), MetadataRef::new(String::from("13"))),
            ],
            blocks1.get(0).unwrap().mdlists
        );
        assert_parse_stmt_func!(
            r#"
            define linkonce_odr void @fn(i32 %i) unnamed_addr #0 align 2 {
              ret void
            }
            "#,
            r#"void @fn(i32 %i)"#,
            &[
                Attr::Ref(0),
                Attr::ParamAttr(ParamAttr(String::from("align"), Some(ParamAttrArg::U32(2))))
            ],
            &[Linkage::LinkonceOdr],
            Visibility::Default,
            None,
            UnnamedAddr::Normal,
            None,
            MetadataList::empty()
        );
        assert_parse_stmt_func!(
            r#"
            define i32 @main(i32, i8**) #5 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
              ret void
            }
            "#,
            r#"i32 @main(i32, i8**)"#,
            &[Attr::Ref(5)],
            &[],
            Visibility::Default,
            None,
            UnnamedAddr::None,
            Some(String::from(
                "i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*)"
            )),
            MetadataList::empty()
        );
        let (stmt_z3negi, _) = Parser::new_stmt::<ExtIdentUnit>(
            r#"
            define i32 @_Z3negi(i32) #0 {
              %2 = alloca i32, align 4
              %3 = alloca i32, align 4
              store i32 %0, i32* %3, align 4
              %4 = load i32, i32* %3, align 4
              %5 = icmp eq i32 %4, 0
              br i1 %5, label %6, label %7
            ; <label>:6:                                      ; preds = %1
              store i32 1, i32* %2, align 4
              br label %8
            ; <label>:7:                                      ; preds = %1
              store i32 0, i32* %2, align 4
              br label %8
            ; <label>:8:                                      ; preds = %7, %6
              %9 = load i32, i32* %2, align 4
              ret i32 %9
            }
            "#,
        );
        match stmt_z3negi {
            Stmt::Func(_, blocks) => {
                assert_eq!(4, blocks.len());
                assert_eq!(
                    Label::from(LocalIdent::from("1")),
                    blocks.get(0).unwrap().name
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(0).unwrap().preds);
                assert_eq!(
                    vec![
                        Label::from(LocalIdent::from("6")),
                        Label::from(LocalIdent::from("7"))
                    ],
                    blocks.get(0).unwrap().succs
                );
                assert_eq!(6, blocks.get(0).unwrap().insns.len());
                assert_eq!(6, blocks.get(0).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("6")),
                    blocks.get(1).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(1).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("8"))],
                    blocks.get(1).unwrap().succs
                );
                assert_eq!(2, blocks.get(1).unwrap().insns.len());
                assert_eq!(2, blocks.get(1).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("7")),
                    blocks.get(2).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(2).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("8"))],
                    blocks.get(2).unwrap().succs
                );
                assert_eq!(2, blocks.get(2).unwrap().insns.len());
                assert_eq!(2, blocks.get(2).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("8")),
                    blocks.get(3).unwrap().name
                );
                assert_eq!(
                    vec![
                        Label::from(LocalIdent::from("6")),
                        Label::from(LocalIdent::from("7"))
                    ],
                    blocks.get(3).unwrap().preds
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(3).unwrap().succs);
                assert_eq!(2, blocks.get(3).unwrap().insns.len());
                assert_eq!(2, blocks.get(3).unwrap().mdlists.len());
            }
            stmt => panic!("expected Stmt::Func, but got {:?}", stmt),
        }
        let (stmt_xatoi, _) = Parser::new_stmt::<ExtIdentUnit>(
            r#"
            define i32 @xatoi(i8*) #0 {
              %2 = invoke i32 @atoi(i8* %0)
                     to label %3 unwind label %4
            ; <label>:3:                                      ; preds = %1
              br label %5
            ; <label>:4:                                      ; preds = %1
              br label %5
            ; <label>:5:                                      ; preds = %4, %3
              ret i32 0
            }
            "#,
        );
        match stmt_xatoi {
            Stmt::Func(_, blocks) => {
                assert_eq!(4, blocks.len());
                assert_eq!(
                    Label::from(LocalIdent::from("1")),
                    blocks.get(0).unwrap().name
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(0).unwrap().preds);
                assert_eq!(
                    vec![
                        Label::from(LocalIdent::from("3")),
                        Label::from(LocalIdent::from("4"))
                    ],
                    blocks.get(0).unwrap().succs
                );
                assert_eq!(1, blocks.get(0).unwrap().insns.len());
                assert_eq!(1, blocks.get(0).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("3")),
                    blocks.get(1).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(1).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("5"))],
                    blocks.get(1).unwrap().succs
                );
                assert_eq!(1, blocks.get(1).unwrap().insns.len());
                assert_eq!(1, blocks.get(1).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("4")),
                    blocks.get(2).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(2).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("5"))],
                    blocks.get(2).unwrap().succs
                );
                assert_eq!(1, blocks.get(2).unwrap().insns.len());
                assert_eq!(1, blocks.get(2).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("5")),
                    blocks.get(3).unwrap().name
                );
                assert_eq!(
                    vec![
                        Label::from(LocalIdent::from("3")),
                        Label::from(LocalIdent::from("4"))
                    ],
                    blocks.get(3).unwrap().preds
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(3).unwrap().succs);
                assert_eq!(1, blocks.get(3).unwrap().insns.len());
                assert_eq!(1, blocks.get(3).unwrap().mdlists.len());
            }
            stmt => panic!("expected Stmt::Func, but got {:?}", stmt),
        }
        let (stmt_switcher, _) = Parser::new_stmt::<ExtIdentUnit>(
            r#"
            define i32 @_Z8switcheri(i32) #0 {
              %2 = alloca i32, align 4
              %3 = alloca i32, align 4
              %4 = alloca i32, align 4
              store i32 %0, i32* %3, align 4
              store i32 5, i32* %4, align 4
              %5 = load i32, i32* %3, align 4
              switch i32 %5, label %8 [
                i32 1, label %6
                i32 2, label %7
              ]
            ; <label>:6:                                      ; preds = %1
              store i32 1, i32* %2, align 4
              br label %14
            ; <label>:7:                                      ; preds = %1
              store i32 22, i32* %2, align 4
              br label %14
            ; <label>:8:                                      ; preds = %1
              %9 = load i32, i32* %3, align 4
              %10 = load i32, i32* %4, align 4
              %11 = mul nsw i32 %10, %9
              store i32 %11, i32* %4, align 4
              br label %12
            ; <label>:12:                                     ; preds = %8
              %13 = load i32, i32* %4, align 4
              store i32 %13, i32* %2, align 4
              br label %14
            ; <label>:14:                                     ; preds = %12, %7, %6
              %15 = load i32, i32* %2, align 4
              ret i32 %15
            }
            "#,
        );
        match stmt_switcher {
            Stmt::Func(_, blocks) => {
                assert_eq!(6, blocks.len());
                assert_eq!(
                    Label::from(LocalIdent::from("1")),
                    blocks.get(0).unwrap().name
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(0).unwrap().preds);
                assert_eq!(
                    vec![
                        Label::from(LocalIdent::from("8")),
                        Label::from(LocalIdent::from("6")),
                        Label::from(LocalIdent::from("7"))
                    ],
                    blocks.get(0).unwrap().succs
                );
                assert_eq!(7, blocks.get(0).unwrap().insns.len());
                assert_eq!(7, blocks.get(0).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("6")),
                    blocks.get(1).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(1).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("14"))],
                    blocks.get(1).unwrap().succs
                );
                assert_eq!(2, blocks.get(1).unwrap().insns.len());
                assert_eq!(2, blocks.get(1).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("7")),
                    blocks.get(2).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(2).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("14"))],
                    blocks.get(2).unwrap().succs
                );
                assert_eq!(2, blocks.get(2).unwrap().insns.len());
                assert_eq!(2, blocks.get(2).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("8")),
                    blocks.get(3).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("1"))],
                    blocks.get(3).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("12"))],
                    blocks.get(3).unwrap().succs
                );
                assert_eq!(5, blocks.get(3).unwrap().insns.len());
                assert_eq!(5, blocks.get(3).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("12")),
                    blocks.get(4).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("8"))],
                    blocks.get(4).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("14"))],
                    blocks.get(4).unwrap().succs
                );
                assert_eq!(3, blocks.get(4).unwrap().insns.len());
                assert_eq!(3, blocks.get(4).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("14")),
                    blocks.get(5).unwrap().name
                );
                assert_eq!(
                    vec![
                        Label::from(LocalIdent::from("6")),
                        Label::from(LocalIdent::from("7")),
                        Label::from(LocalIdent::from("12"))
                    ],
                    blocks.get(5).unwrap().preds
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(5).unwrap().succs);
                assert_eq!(2, blocks.get(5).unwrap().insns.len());
                assert_eq!(2, blocks.get(5).unwrap().mdlists.len());
            }
            stmt => panic!("expected Stmt::Func, but got {:?}", stmt),
        }
        let (stmt_rust_ex1, _) = Parser::new_stmt::<ExtIdentUnit>(
            r#"
            define internal nonnull i8* @"_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17h0874d54aba2b30d8E"(i8* nonnull %unique) unnamed_addr #0 {
            "start":
              ; call core::ptr::unique::Unique<T>::as_ptr
              %_2 = call i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17hb2ce0dc8ae54d3b2E"(i8* nonnull %unique)
              br label %bb1
            bb1:                                              ; preds = %start
              ; call core::ptr::non_null::NonNull<T>::new_unchecked
              %0 = call nonnull i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h44b557749a9d6ccfE"(i8* %_2)
              br label %2
            2:                                                ; preds = %bb1
              ret i8* %0
            }                
            "#,
        );
        match stmt_rust_ex1 {
            Stmt::Func(_, blocks) => {
                assert_eq!(3, blocks.len());
                assert_eq!(
                    Label::from(LocalIdent::from("start")),
                    blocks.get(0).unwrap().name
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(0).unwrap().preds);
                assert_eq!(
                    vec![Label::from(LocalIdent::from("bb1"))],
                    blocks.get(0).unwrap().succs
                );
                assert_eq!(2, blocks.get(0).unwrap().insns.len());
                assert_eq!(2, blocks.get(0).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("bb1")),
                    blocks.get(1).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("start"))],
                    blocks.get(1).unwrap().preds
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("2"))],
                    blocks.get(1).unwrap().succs
                );
                assert_eq!(2, blocks.get(1).unwrap().insns.len());
                assert_eq!(2, blocks.get(1).unwrap().mdlists.len());
                assert_eq!(
                    Label::from(LocalIdent::from("2")),
                    blocks.get(2).unwrap().name
                );
                assert_eq!(
                    vec![Label::from(LocalIdent::from("bb1"))],
                    blocks.get(2).unwrap().preds
                );
                assert_eq!(Vec::<Label>::new(), blocks.get(2).unwrap().succs);
                assert_eq!(1, blocks.get(2).unwrap().insns.len());
                assert_eq!(1, blocks.get(2).unwrap().mdlists.len());
            }
            stmt => panic!("expected Stmt::Func, but got {:?}", stmt),
        }
    }
    #[test]
    fn parse_attributes() {
        let source = r#"attributes #0 = { noinline nounwind "darwin-stkchk-strong-link" "use-soft-float"="false" allocsize(0) }"#;
        let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>(source);
        assert_eq!(
            Stmt::Attrs(
                0,
                vec![
                    Attr::ParamAttr(ParamAttr(String::from("noinline"), None)),
                    Attr::ParamAttr(ParamAttr(String::from("nounwind"), None)),
                    Attr::Key(String::from("darwin-stkchk-strong-link")),
                    Attr::KeyValue(String::from("use-soft-float"), String::from("false")),
                    Attr::ParamAttr(ParamAttr(
                        String::from("allocsize"),
                        Some(ParamAttrArg::U32(0))
                    )),
                ]
            ),
            stmt
        );
        assert_eq!(MetadataList::empty(), mdlist);
    }
    #[test]
    fn parse_metadata() {
        for input in vec![
            "distinct !{!1, !2, !3}",
            r#"!{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 15]}"#,
            "!DIGlobalVariableExpression(var: !1, expr: !DIExpression())",
            r#"!DIGlobalVariable(line: 1, name: "name", isLocal: false, isDefinition: true)"#,
            "!DIDerivedType(tag: DW_TAG_pointer_type, baseType: null)",
            "!DISubprogram(spFlags: DISPFlagLocalToUnit | DISPFlagDefinition)",
            "!DIExpression(DW_OP_plus_uconst, 65535, DW_OP_stack_value)",
            r#"!DIEnumerator(name: "unknownerror", value: -1)"#,
        ] {
            let source = format!("!0 = {}", input);
            let (stmt, mdlist) = Parser::new_stmt::<ExtIdentUnit>(&source);
            let (with_distinct, input) = match input.starts_with("distinct") {
                true => (true, &input[9..]),
                false => (false, input),
            };
            match stmt {
                Stmt::Metadata(name, is_distinct, md) => {
                    assert_eq!(MetadataRef::new(String::from("0")), name, "{}", source);
                    assert_eq!(with_distinct, is_distinct, "{}", source);
                    assert_eq!(input, md.to_string(), "{}", source);
                }
                _ => panic!("unexpected stmt: {:?} in {}", stmt, source),
            }
            assert_eq!(MetadataList::empty(), mdlist);
        }
    }
    #[test]
    fn parse_module() {
        let module = Module::<ExtIdentUnit>::parse(
            r#"
            ; ModuleID = 'hello_world.cpp'
            source_filename = "hello_world.cpp"
            target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
            target triple = "x86_64-apple-macosx10.15.0"
            
            %class.X = type { i32 }
            
            @.str = private unnamed_addr constant [15 x i8] c"Hello, world!\0A\00", align 1
            @.str.1 = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
            
            ; Func Attrs: noinline norecurse optnone ssp uwtable
            define i32 @main(i32, i8**) #0 {
              %3 = alloca i32, align 4
              %4 = alloca i32, align 4
              %5 = alloca i8**, align 8
              %6 = alloca %class.X, align 4
              store i32 0, i32* %3, align 4
              store i32 %0, i32* %4, align 4
              store i8** %1, i8*** %5, align 8
              %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str, i32 0, i32 0))
              %8 = getelementptr inbounds %class.X, %class.X* %6, i32 0, i32 0
              %9 = load i32, i32* %8, align 4
              %10 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i32 0, i32 0), i32 %9)
              ret i32 0
            }
            
            declare i32 @printf(i8*, ...) #1
            
            attributes #0 = { noinline norecurse optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "darwin-stkchk-strong-link" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
            attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "darwin-stkchk-strong-link" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
            
            !llvm.module.flags = !{!0, !1, !2}
            !llvm.ident = !{!3}
            
            !0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 15]}
            !1 = !{i32 1, !"wchar_size", i32 4}
            !2 = !{i32 7, !"PIC Level", i32 2}
            !3 = !{!"Apple clang version 11.0.0 (clang-1100.0.33.17)"}
            "#,
            "input",
        ).unwrap();
        assert_eq!(
            "hello_world.cpp",
            module.source_filename().as_ref().unwrap()
        );
        assert_eq!(
            &DataLayout::parse("e-m:o-i64:64-f80:128-n8:16:32:64-S128").expect("success"),
            module.target_datalayout()
        );
        assert_eq!(
            "x86_64-apple-macosx10.15.0",
            module.target_triple().as_ref().unwrap()
        );
        assert_eq!(1, module.typedef_order().len());
        assert_eq!(1, module.typedefs().len());
        assert_eq!(2, module.globals().len());
        assert_eq!(2, module.funcs().len());
        assert_eq!(2, module.attr_groups().len());
        assert_eq!(6, module.metadata_list().len());
        let module = Module::<ExtIdentUnit>::parse(
            r#"
            target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
            %struct.Tuple2 = type { i32, i32 }
            %struct.Tuple3 = type { %struct.Tuple2, i32 }
            %struct.X = type { <4 x %struct.Y> }
            %struct.Y = type { [4 x %struct.Z] }
            %struct.Z = type { %struct.Z*, i32 }
            "#,
            "input",
        )
        .unwrap();
        for (a, b) in vec![("%struct.Z", "%struct.Y"), ("%struct.Y", "%struct.X")] {
            let order = module.typedef_order();
            let i = order.iter().position(|name| &name.to_string() == a);
            let j = order.iter().position(|name| &name.to_string() == b);
            assert!(
                i < j,
                "not {} < {} in {}",
                a,
                b,
                DisplayIter("[", order.iter(), ",", "]")
            );
        }
        let err = Module::<ExtIdentUnit>::parse(
            r#"
            target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
            %struct.A = type { %struct.X }
            %struct.X = type { %struct.Y }
            %struct.Y = type { %struct.Z }
            %struct.Z = type { %struct.X }
            "#,
            "input",
        )
        .unwrap_err();
        assert_eq!(
            "detected typedef cycle: %struct.X -> %struct.Y -> %struct.Z -> %struct.X",
            err
        );
    }
}
