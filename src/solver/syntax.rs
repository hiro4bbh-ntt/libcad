//! The syntax of the input language used by MSSS.

use crate::fmt::DisplayIter;
use crate::reader::sexpr::SExpr;
use std::fmt;

/// A constant in conditions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CondConst {
    /// A 64-bit unsigned integer.
    U64(u64),
}

impl CondConst {
    /// Parses a constant in the S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<CondConst, String> {
        match sexpr {
            SExpr::U64(n) => Ok(CondConst::U64(*n)),
            _ => Err(format!("illegal condition constant {}", sexpr)),
        }
    }
}

impl fmt::Display for CondConst {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CondConst::U64(n) => write!(f, "{:#x}", n),
        }
    }
}

/// A variable in conditions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CondVar(usize);

impl CondVar {
    /// Parses a variable in the S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<CondVar, String> {
        match sexpr {
            SExpr::Symbol(ident!("$0")) => Ok(CondVar(0)),
            SExpr::Symbol(ident!("$1")) => Ok(CondVar(1)),
            SExpr::Symbol(ident!("$2")) => Ok(CondVar(2)),
            SExpr::Symbol(ident!("$3")) => Ok(CondVar(3)),
            SExpr::Symbol(ident!("$4")) => Ok(CondVar(4)),
            SExpr::Symbol(ident!("$5")) => Ok(CondVar(5)),
            SExpr::Symbol(ident!("$6")) => Ok(CondVar(6)),
            SExpr::Symbol(ident!("$7")) => Ok(CondVar(7)),
            SExpr::Symbol(ident!("$8")) => Ok(CondVar(8)),
            SExpr::Symbol(ident!("$9")) => Ok(CondVar(9)),
            _ => Err(format!("illegal condition variable {}", sexpr)),
        }
    }
    /// Returns the ID.
    pub fn id(&self) -> usize {
        self.0
    }
}

impl From<usize> for CondVar {
    fn from(id: usize) -> CondVar {
        CondVar(id)
    }
}

impl fmt::Display for CondVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "${}", self.id())
    }
}

/// An expression in conditions.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CondExpr {
    /// A constant.
    Const(CondConst),
    /// A variable.
    Var(CondVar),
    /// Dereferences the variable.
    Deref(CondVar),
    /// Applies the bit-wise AND with the constant.
    Bitand(Box<CondExpr>, CondConst),
    /// Applies the logical shift to right by the constant.
    Bitlshr(Box<CondExpr>, CondConst),
}

impl CondExpr {
    /// Parses an expression in the S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<CondExpr, String> {
        match sexpr {
            SExpr::U64(_) => Ok(CondExpr::Const(CondConst::try_parse(sexpr)?)),
            SExpr::Symbol(_) => Ok(CondExpr::Var(CondVar::try_parse(sexpr)?)),
            sexpr => match sexpr.try_to_cmd() {
                Some((ident!("bitand"), args)) if args.len() == 2 => {
                    let left = CondExpr::try_parse(&args[0])?;
                    let right = CondConst::try_parse(&args[1])?;
                    Ok(CondExpr::Bitand(Box::new(left), right))
                }
                Some((ident!("bitlshr"), args)) if args.len() == 2 => {
                    let left = CondExpr::try_parse(&args[0])?;
                    let right = CondConst::try_parse(&args[1])?;
                    Ok(CondExpr::Bitlshr(Box::new(left), right))
                }
                Some((ident!("deref"), args)) if args.len() == 1 => {
                    Ok(CondExpr::Deref(CondVar::try_parse(&args[0])?))
                }
                _ => Err(format!("illegal condition expression {}", sexpr)),
            },
        }
    }
}

impl fmt::Display for CondExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CondExpr::Const(val) => write!(f, "{}", val),
            CondExpr::Var(var) => write!(f, "{}", var),
            CondExpr::Deref(ptr) => write!(f, "deref({})", ptr),
            CondExpr::Bitand(left, right) => write!(f, "bitand({}, {})", left, right),
            CondExpr::Bitlshr(left, right) => write!(f, "bitlshr({}, {})", left, right),
        }
    }
}

/// A predicate in conditions.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CondPred {
    /// The constant `false`.
    False,
    /// The constant `true`.
    True,
    /// An equality.
    Eq(CondExpr, CondExpr),
    /// An inequality.
    Neq(CondExpr, CondExpr),
}

impl CondPred {
    /// Parses a predicate in the S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<CondPred, String> {
        match sexpr {
            SExpr::Symbol(ident!("false")) => Ok(CondPred::False),
            SExpr::Symbol(ident!("true")) => Ok(CondPred::True),
            _ => match sexpr.try_to_cmd() {
                Some((name @ ident!("=="), args)) | Some((name @ ident!("!="), args))
                    if args.len() == 2 =>
                {
                    let var = CondExpr::try_parse(&args[0])?;
                    let val = CondExpr::try_parse(&args[1])?;
                    match name {
                        ident!("==") => Ok(CondPred::Eq(var, val)),
                        ident!("!=") => Ok(CondPred::Neq(var, val)),
                        _ => unreachable!("{}", name),
                    }
                }
                _ => Err(format!("illegal condition predicate {}", sexpr)),
            },
        }
    }
}

impl fmt::Display for CondPred {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CondPred::False => write!(f, "false"),
            CondPred::True => write!(f, "true"),
            CondPred::Eq(var, val) => write!(f, "eq({}, {})", var, val),
            CondPred::Neq(var, val) => write!(f, "neq({}, {})", var, val),
        }
    }
}

/// A condition.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Cond {
    /// A conjunction of predicates.
    And(Vec<CondPred>),
}

impl Cond {
    /// Returns a condition expressing the constant `true`.
    pub fn top() -> Cond {
        Cond::And(Vec::new())
    }
    /// Parses a condition in the S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<Cond, String> {
        match sexpr.try_to_cmd() {
            Some((ident!("and"), args)) if args.is_empty() => Ok(Cond::And(vec![CondPred::True])),
            Some((ident!("and"), args)) if !args.is_empty() => {
                let mut preds = Vec::with_capacity(args.len());
                for arg in args {
                    preds.push(CondPred::try_parse(arg)?);
                }
                Ok(Cond::And(preds))
            }
            _ => Ok(Cond::And(vec![CondPred::try_parse(sexpr)?])),
        }
    }
    /// Returns a condition conjuncting with `pred`.
    pub fn conjunct(&mut self, pred: CondPred) {
        match self {
            Cond::And(preds) => preds.push(pred),
        }
    }
    /// Returns a condition conjuncting with any element of `other`.
    pub fn conjunct_any(&mut self, other: Cond) {
        match self {
            Cond::And(preds) => match other {
                Cond::And(mut opreds) => preds.append(&mut opreds),
            },
        }
    }
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Cond::And(preds) => write!(f, "and({})", DisplayIter("", preds.iter(), ", ", "")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cond_expr_to_string() {
        for (expected, input) in vec![
            ("0x40", CondExpr::Const(CondConst::U64(64))),
            ("$0", CondExpr::Var(CondVar(0))),
            ("deref($0)", CondExpr::Deref(CondVar(0))),
            (
                "bitand($0, 0xf)",
                CondExpr::Bitand(Box::new(CondExpr::Var(CondVar(0))), CondConst::U64(0x0f)),
            ),
            (
                "bitlshr($0, 0x2f)",
                CondExpr::Bitlshr(Box::new(CondExpr::Var(CondVar(0))), CondConst::U64(47)),
            ),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn cond_expr_try_parse() {
        for (expected, input) in vec![
            ("Ok(0x40)", r#"64"#),
            ("Ok($0)", r#"$0"#),
            ("Ok($1)", r#"$1"#),
            ("Ok($2)", r#"$2"#),
            ("Ok($3)", r#"$3"#),
            ("Ok($4)", r#"$4"#),
            ("Ok($5)", r#"$5"#),
            ("Ok($6)", r#"$6"#),
            ("Ok($7)", r#"$7"#),
            ("Ok($8)", r#"$8"#),
            ("Ok($9)", r#"$9"#),
            ("Err(illegal condition variable $11)", r#"$11"#),
            ("Ok(deref($0))", r#"(deref $0)"#),
            ("Ok(bitand($0, 0xf))", r#"(bitand $0 0x0f)"#),
            ("Ok(bitlshr($0, 0x2f))", r#"(bitlshr $0 47)"#),
            ("Err(illegal condition expression (fn $0))", r#"(fn $0)"#),
            ("Err(illegal condition variable sym)", r#"sym"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match CondExpr::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn cond_pred_to_string() {
        for (expected, input) in vec![
            ("false", CondPred::False),
            ("true", CondPred::True),
            (
                "eq($0, 0x1)",
                CondPred::Eq(
                    CondExpr::Var(CondVar(0)),
                    CondExpr::Const(CondConst::U64(1)),
                ),
            ),
            (
                "neq($0, 0x1)",
                CondPred::Neq(
                    CondExpr::Var(CondVar(0)),
                    CondExpr::Const(CondConst::U64(1)),
                ),
            ),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn cond_pred_try_parse() {
        for (expected, input) in vec![
            ("Ok(false)", r#"false"#),
            ("Ok(eq($0, 0x1))", r#"(== $0 1)"#),
            ("Ok(neq($0, 0x1))", r#"(!= $0 1)"#),
            ("Err(illegal condition predicate sym)", r#"sym"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match CondPred::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn cond_to_string() {
        for (expected, input) in vec![(
            "and(true, false)",
            Cond::And(vec![CondPred::True, CondPred::False]),
        )] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn cond_try_parse() {
        for (expected, input) in vec![
            ("Ok(and(true))", r#"true"#),
            ("Ok(and(true))", r#"(and)"#),
            ("Ok(and(false))", r#"(and false)"#),
            ("Ok(and(true, false))", r#"(and true false)"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match Cond::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
}
