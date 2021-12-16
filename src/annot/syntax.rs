//! The syntax of an annotation.

use crate::fmt::DisplayIter;
use crate::llir::interp::rtti::{ExtIdent, ExtName};
use crate::llir::syntax::{LocalIdent, Type as LLIRType};
use crate::ops::TotallyComparable;
use crate::reader::sexpr::SExpr;
use crate::solver::syntax::{Cond, CondVar};
use crate::symbol::Ident;
use std::cmp::max;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Deref, DerefMut};

use super::AnnotFile;

/// A `fieldptr` term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fieldptr(Vec<u64>);

impl Fieldptr {
    /// Returns a new `baseptr` term.
    pub fn baseptr() -> Fieldptr {
        Fieldptr(Vec::new())
    }
    /// Parses a `baseptr` or `fieldptr` term in the given S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<Fieldptr, String> {
        if let SExpr::Symbol(ident!("baseptr")) = sexpr {
            return Ok(Fieldptr::baseptr());
        }
        if let Some((ident!("fieldptr"), args)) = sexpr.try_to_cmd() {
            let mut indices = Vec::with_capacity(args.len());
            for arg in args {
                indices.push(match arg {
                    SExpr::U64(n) => *n,
                    sexpr => {
                        return Err(format!("fieldptr: index must be u64, but got {}", sexpr));
                    }
                });
            }
            return Ok(Fieldptr(indices));
        }
        Err(format!("expected fieldptr expression, but got {}", sexpr))
    }
    /// Returns `true` if the fieldptr is `baseptr`.
    pub fn is_baseptr(&self) -> bool {
        self.0.is_empty()
    }
    /// Returns `true` if the fieldptr is prefix of the other.
    pub fn contains(&self, other: &Fieldptr) -> bool {
        self.0.len() <= other.0.len() && self.0[..] == other.0[..(self.0.len())]
    }
    /// Returns `true` if the fieldptr is not prefix of the other, and vice versa.
    pub fn is_disjoint(&self, other: &Fieldptr) -> bool {
        !self.contains(other) && !other.contains(self)
    }
}

impl Deref for Fieldptr {
    type Target = [u64];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for Fieldptr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.0.len() {
            0 => write!(f, "baseptr"),
            _ => write!(f, "fieldptr({})", DisplayIter("", self.0.iter(), ", ", "")),
        }
    }
}

/// A case in a `cast-match` term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CastMatchCase {
    cond: Cond,
    target: LLIRType<ExtIdent>,
}

impl CastMatchCase {
    /// Returns the condition.
    pub fn cond(&self) -> &Cond {
        &self.cond
    }
    /// Returns the target type.
    pub fn target(&self) -> &LLIRType<ExtIdent> {
        &self.target
    }
    /// Parses a `cast-match` case in the given S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<CastMatchCase, String> {
        match sexpr {
            SExpr::List(list) if list.len() == 2 => {
                let cond = Cond::try_parse(&list[0])?;
                let target = LLIRType::try_from_sexpr(&list[1])?;
                Ok(CastMatchCase { cond, target })
            }
            _ => Err(format!("cast-match: case must be list, but got {}", sexpr)),
        }
    }
}

impl fmt::Display for CastMatchCase {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{} -> {}", self.cond, self.target)
    }
}

/// A `cast-match` term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CastMatch(Vec<CastMatchCase>);

impl CastMatch {
    /// Returns the cases.
    pub fn cases(&self) -> &[CastMatchCase] {
        &self.0
    }
}

impl fmt::Display for CastMatch {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "cast-match({})",
            DisplayIter("", self.0.iter(), "; ", "")
        )
    }
}

/// A `restrict-cast-match` term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RestrictCastMatch {
    basename: Ident,
    targets: Vec<LLIRType<ExtIdent>>,
}

impl RestrictCastMatch {
    /// Returns the basename.
    pub fn basename(&self) -> Ident {
        self.basename
    }
    /// Returns the list of the target types.
    pub fn targets(&self) -> &[LLIRType<ExtIdent>] {
        &self.targets
    }
}

impl fmt::Display for RestrictCastMatch {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let targets = DisplayIter("", self.targets.iter(), ", ", "");
        write!(f, "restrict-cast-match({}; {})", self.basename, targets)
    }
}

/// A refiner term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Refiner {
    CastMatch(CastMatch),
    RestrictCastMatch(RestrictCastMatch),
}

impl Refiner {
    /// Parses a refinier in the given S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<Refiner, String> {
        match sexpr.try_to_cmd() {
            Some((ident!("cast-match"), args)) => {
                let mut cases = Vec::with_capacity(args.len());
                for arg in args {
                    cases.push(CastMatchCase::try_parse(arg)?);
                }
                Ok(Refiner::CastMatch(CastMatch(cases)))
            }
            Some((ident!("restrict-cast-match"), args)) if args.len() >= 2 => {
                let basename = match &args[0] {
                    SExpr::Symbol(name) => *name,
                    arg => {
                        return Err(format!(
                            "restrict-cast-match: #0 argument must be Symbol, but got {}",
                            arg
                        ))
                    }
                };
                let mut targets = Vec::with_capacity(args.len() - 1);
                for arg in &args[1..] {
                    targets.push(LLIRType::try_from_sexpr(arg)?);
                }
                Ok(Refiner::RestrictCastMatch(RestrictCastMatch {
                    basename,
                    targets,
                }))
            }
            _ => Err(format!("expected refiner, but got {}", sexpr)),
        }
    }
    /// Try to return the `cast-match` term.
    pub fn try_to_cast_match(&self) -> Option<&CastMatch> {
        match self {
            Refiner::CastMatch(cm) => Some(cm),
            _ => None,
        }
    }
    /// Returns the list of the cases as resolving `restrict-cast-match` in the annotation file.
    pub fn enum_cases(&self, annotfile: &AnnotFile) -> Result<Vec<CastMatchCase>, String> {
        match self {
            Refiner::CastMatch(cm) => Ok(cm.cases().to_vec()),
            Refiner::RestrictCastMatch(rcm) => {
                let base = match annotfile.refiner(&rcm.basename) {
                    Some(refiner) => refiner,
                    None => return Err(format!("refiner {} not found", rcm.basename)),
                };
                let cases0 = base.enum_cases(annotfile)?;
                let mut cases = Vec::new();
                for case in cases0 {
                    if rcm.targets.contains(&case.target) {
                        cases.push(case);
                    }
                }
                Ok(cases)
            }
        }
    }
}

impl fmt::Display for Refiner {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Refiner::CastMatch(cm) => write!(f, "{}", cm),
            Refiner::RestrictCastMatch(rcm) => write!(f, "{}", rcm),
        }
    }
}

/// A refiner application term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RefinerApp {
    Cast(Ident, Vec<Fieldptr>),
    Downcast(Ident, Vec<Fieldptr>),
    Restrict(Ident),
}

impl RefinerApp {
    /// Parses a refinier application term in the given S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<RefinerApp, String> {
        match sexpr.try_to_cmd() {
            Some((kind @ ident!("cast"), args)) | Some((kind @ ident!("downcast"), args))
                if args.len() >= 2 =>
            {
                let name = match &args[0] {
                    SExpr::Symbol(name) => *name,
                    arg => {
                        return Err(format!(
                            "{}: #0 argument must be Symbol, but got {}",
                            kind, arg
                        ));
                    }
                };
                let mut tags = Vec::with_capacity(args.len() - 1);
                for arg in &args[1..] {
                    tags.push(Fieldptr::try_parse(arg)?);
                }
                Ok(match kind {
                    ident!("cast") => RefinerApp::Cast(name, tags),
                    ident!("downcast") => RefinerApp::Downcast(name, tags),
                    _ => unreachable!("{}", name),
                })
            }
            Some((ident!("restrict"), args)) if args.len() == 1 => {
                let name = match &args[0] {
                    SExpr::Symbol(name) => *name,
                    arg => {
                        return Err(format!(
                            "restrict: #0 argument must be Symbol, but got {}",
                            arg
                        ))
                    }
                };
                Ok(RefinerApp::Restrict(name))
            }
            _ => Err(format!("expected refiner application, but got {}", sexpr)),
        }
    }
    /// Returns the refiner application name.
    pub fn name(&self) -> Ident {
        match self {
            RefinerApp::Cast(name, _)
            | RefinerApp::Downcast(name, _)
            | RefinerApp::Restrict(name) => *name,
        }
    }
    /// Returns the fieldptr list of the tag variables.
    pub fn tags(&self) -> &[Fieldptr] {
        match self {
            RefinerApp::Cast(_, tags) | RefinerApp::Downcast(_, tags) => tags,
            RefinerApp::Restrict(_) => &[],
        }
    }
    /// Returns the extention name of the target field indicating this application.
    pub fn extname_target(&self) -> ExtName {
        match self {
            RefinerApp::Cast(name, _) => ExtName::CastTarget(*name),
            RefinerApp::Downcast(name, _) => ExtName::DowncastTarget(*name),
            RefinerApp::Restrict(name) => ExtName::RestrictBase(*name),
        }
    }
    /// Returns the extension name of the `n`-th tag field indicating this application.
    pub fn extname_tag(&self, n: usize) -> Option<ExtName> {
        match self {
            RefinerApp::Cast(name, _) => Some(ExtName::CastTag(*name, n)),
            RefinerApp::Downcast(name, _) => Some(ExtName::DowncastTag(*name, n)),
            RefinerApp::Restrict(_) => None,
        }
    }
}

impl fmt::Display for RefinerApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            RefinerApp::Cast(name, tags) => {
                write!(
                    f,
                    "cast(!{}; {})",
                    name,
                    DisplayIter("", tags.iter(), ", ", "")
                )
            }
            RefinerApp::Downcast(name, tags) => {
                let tags = DisplayIter("", tags.iter(), ", ", "");
                write!(f, "downcast(!{}; {})", name, tags)
            }
            RefinerApp::Restrict(name) => write!(f, "restrict(!{})", name),
        }
    }
}

/// A `define-refiner` term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefineRefiner {
    name: Ident,
    refiner: Refiner,
}

impl DefineRefiner {
    /// Returns the name of the defined refiner.
    pub fn name(&self) -> Ident {
        self.name
    }
    /// Returns the defined refiner.
    pub fn refiner(&self) -> &Refiner {
        &self.refiner
    }
}

impl fmt::Display for DefineRefiner {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "define-refiner(!{}; {})", self.name, self.refiner)
    }
}

/// A `apply-refiner` term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ApplyRefiner {
    typename: LocalIdent,
    target: Fieldptr,
    app: RefinerApp,
}

impl ApplyRefiner {
    /// Returns the name of the refined type.
    pub fn typename(&self) -> LocalIdent {
        self.typename
    }
    /// Returns the fieldptr of the refined target.
    pub fn target(&self) -> &Fieldptr {
        &self.target
    }
    /// Returns the refiner application.
    pub fn app(&self) -> &RefinerApp {
        &self.app
    }
    /// Returns `true` if the application is valid.
    /// This only validates the consistency of the body of the refinement,
    ///   hence this won't check the refiner application name of `restrict`.
    pub fn check_validity(&self) -> Result<(), String> {
        match &self.app {
            RefinerApp::Cast(_, tags) => {
                if self.target.is_baseptr() {
                    return Err("cast cannot set on baseptr".to_string());
                }
                for (i, tagi) in tags.iter().enumerate() {
                    if !tagi.is_disjoint(&self.target) {
                        return Err(format!(
                            "cast cannot use {} as tag not disjoint with target {}",
                            tagi, self.target
                        ));
                    }
                    for tagj in &tags[..i] {
                        if !tagi.is_disjoint(tagj) {
                            return Err(format!(
                                "cast cannot use {} as tag not disjoint with another tag {}",
                                tagi, tagj
                            ));
                        }
                    }
                }
            }
            RefinerApp::Downcast(_, tags) => {
                for (i, tagi) in tags.iter().enumerate() {
                    if !self.target.contains(tagi) || &self.target == tagi {
                        return Err(format!(
                            "downcast cannot use {} as tag not truly contained in target {}",
                            tagi, self.target
                        ));
                    }
                    for tagj in &tags[..i] {
                        if !tagi.is_disjoint(tagj) {
                            return Err(format!(
                                "downcast cannot use {} as tag not disjoint with another tag {}",
                                tagi, tagj
                            ));
                        }
                    }
                }
            }
            RefinerApp::Restrict(_) => {}
        }
        Ok(())
    }
    /// Returns the variable map with the given pointer.
    pub fn varmap<P: TotallyComparable>(&self, ptr: &P) -> VarMap<P> {
        let mut varmap = VarMap::empty();
        for (n, var) in self.app.tags().iter().enumerate() {
            let tagname = self.app.extname_tag(n).unwrap();
            varmap.insert((ptr.clone(), tagname), CondVar::from(n));
            if var == &self.target {
                varmap.insert((ptr.clone(), self.app.extname_target()), CondVar::from(n));
            }
        }
        varmap
    }
}

impl fmt::Display for ApplyRefiner {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "apply-refiner({}, {}; {})",
            self.typename, self.target, self.app
        )
    }
}

/// An annotation term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Annot {
    ApplyRefiner(ApplyRefiner),
    DefineRefiner(DefineRefiner),
}

impl Annot {
    /// Parses an annotation in the given S-expression.
    pub fn try_parse(sexpr: &SExpr) -> Result<Annot, String> {
        match sexpr.try_to_cmd() {
            Some((ident!("apply-refiner"), args)) if args.len() == 3 => {
                let typename = match &args[0] {
                    SExpr::String(name) => LocalIdent::from(name.clone()),
                    arg => {
                        return Err(format!(
                            "apply-refiner: #0 argument must be String, but got {}",
                            arg
                        ))
                    }
                };
                let target = Fieldptr::try_parse(&args[1])?;
                let app = RefinerApp::try_parse(&args[2])?;
                Ok(Annot::ApplyRefiner(ApplyRefiner {
                    typename,
                    target,
                    app,
                }))
            }
            Some((ident!("define-refiner"), args)) if args.len() == 2 => {
                let name = match &args[0] {
                    SExpr::Symbol(name) => *name,
                    arg => {
                        return Err(format!(
                            "define-refiner: #0 argument must be String, but got {}",
                            arg
                        ))
                    }
                };
                let refiner = Refiner::try_parse(&args[1])?;
                Ok(Annot::DefineRefiner(DefineRefiner { name, refiner }))
            }
            _ => Err(format!("expected annotation, but got {}", sexpr)),
        }
    }
}

impl fmt::Display for Annot {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Annot::ApplyRefiner(cmd) => write!(f, "{}", cmd),
            Annot::DefineRefiner(cmd) => write!(f, "{}", cmd),
        }
    }
}

/// A variable map that is a map from the pairs of the pointer and the extension name to the condition variables.
#[derive(Clone, Debug)]
pub struct VarMap<P: TotallyComparable>(BTreeMap<(P, ExtName), CondVar>);

impl<P: TotallyComparable> VarMap<P> {
    /// Returns the empty variable map.
    pub fn empty() -> VarMap<P> {
        VarMap(BTreeMap::new())
    }
    /// Returns the maximum ID of the condition variables.
    pub fn maxid(&self) -> usize {
        let mut maxid = 0;
        for (_, var) in self.iter() {
            maxid = max(maxid, var.id());
        }
        maxid
    }
    /// Returns the condition variable from the given pair of the pointer and the extension name.
    /// This also inserts a new condition variable if not found.
    pub fn var(&mut self, ptr: &P, name: &ExtName) -> CondVar {
        if let Some(var) = self.get(&(ptr.clone(), *name)) {
            return *var;
        }
        let var = CondVar::from(self.maxid() + 1);
        self.insert((ptr.clone(), *name), var);
        var
    }
    /// Inserts the duplicated condition variables replacing the pointer with `newptr`.
    pub fn insert_dupvars(&mut self, newptr: P) {
        let baseid = self.maxid() + 1;
        let mut varmap = VarMap::empty();
        for ((_, name), var) in self.iter() {
            varmap.insert((newptr.clone(), *name), CondVar::from(baseid + var.id()));
        }
        self.append(&mut varmap);
    }
}

impl<P: TotallyComparable> Deref for VarMap<P> {
    type Target = BTreeMap<(P, ExtName), CondVar>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<P: TotallyComparable> DerefMut for VarMap<P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<P: TotallyComparable> fmt::Display for VarMap<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{{")?;
        for (i, ((tag, kind), valid)) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "({}, {}) -> {}", tag, kind, valid)?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::syntax::CondPred;
    #[test]
    fn fieldptr_to_string() {
        for (expected, input) in vec![
            ("baseptr", Fieldptr(vec![])),
            ("fieldptr(1, 2)", Fieldptr(vec![1, 2])),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn fieldptr_try_parse() {
        for (expected, input) in vec![
            ("Ok(baseptr)", r#"baseptr"#),
            ("Ok(baseptr)", r#"(fieldptr)"#),
            ("Ok(fieldptr(1, 2))", r#"(fieldptr 1 2)"#),
            (
                "Err(fieldptr: index must be u64, but got sym)",
                r#"(fieldptr sym 1 2)"#,
            ),
            ("Err(expected fieldptr expression, but got sym)", r#"sym"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match Fieldptr::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn refiner_to_string() {
        for (expected, input) in vec![
            (
                "cast-match(and(true) -> i8; and(false) -> i32)",
                Refiner::CastMatch(CastMatch(vec![
                    CastMatchCase {
                        cond: Cond::And(vec![CondPred::True]),
                        target: LLIRType::I8,
                    },
                    CastMatchCase {
                        cond: Cond::And(vec![CondPred::False]),
                        target: LLIRType::I32,
                    },
                ])),
            ),
            (
                "restrict-cast-match(object-tag; %struct.Closure)",
                Refiner::RestrictCastMatch(RestrictCastMatch {
                    basename: Ident::from("object-tag"),
                    targets: vec![LLIRType::Name(LocalIdent::from("struct.Closure"))],
                }),
            ),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn refiner_try_parse() {
        for (expected, input) in vec![
            (
                "Ok(cast-match(and(true) -> i8; and(false) -> i32))",
                r#"(cast-match (true i8) (false i32))"#,
            ),
            (
                "Err(cast-match: case must be list, but got false)",
                r#"(cast-match (true i8) false)"#,
            ),
            (
                "Ok(restrict-cast-match(object-tag; %struct.Closure))",
                r#"(restrict-cast-match object-tag "struct.Closure")"#,
            ),
            (
                "Err(restrict-cast-match: #0 argument must be Symbol, but got 0x0)",
                r#"(restrict-cast-match 0 "struct.Closure")"#,
            ),
            ("Err(expected refiner, but got sym)", r#"sym"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match Refiner::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn refiner_app_to_string() {
        for (expected, input) in vec![
            (
                "cast(!object-tag; fieldptr(1))",
                RefinerApp::Cast(Ident::from("object-tag"), vec![Fieldptr(vec![1])]),
            ),
            (
                "downcast(!object-tag; fieldptr(1))",
                RefinerApp::Downcast(Ident::from("object-tag"), vec![Fieldptr(vec![1])]),
            ),
            (
                "restrict(!closure-tag)",
                RefinerApp::Restrict(Ident::from("closure-tag")),
            ),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn refiner_app_try_parse() {
        for (expected, input) in vec![
            (
                "Ok(cast(!object-tag; fieldptr(0)))",
                r#"(cast object-tag (fieldptr 0))"#,
            ),
            (
                "Err(cast: #0 argument must be Symbol, but got 0x0)",
                r#"(cast 0 (fieldptr 0))"#,
            ),
            (
                "Ok(downcast(!object-tag; fieldptr(0)))",
                r#"(downcast object-tag (fieldptr 0))"#,
            ),
            (
                "Err(downcast: #0 argument must be Symbol, but got 0x0)",
                r#"(downcast 0 (fieldptr 0))"#,
            ),
            ("Ok(restrict(!closure-tag))", r#"(restrict closure-tag)"#),
            (
                "Err(restrict: #0 argument must be Symbol, but got 0x0)",
                r#"(restrict 0)"#,
            ),
            ("Err(expected refiner application, but got sym)", r#"sym"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match RefinerApp::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn annot_to_string() {
        for (expected, input) in vec![
            (
                "define-refiner(!object-tag; cast-match(and(true) -> i8; and(false) -> i32))",
                Annot::DefineRefiner(DefineRefiner {
                    name: Ident::from("object-tag"),
                    refiner: Refiner::try_parse(&SExpr::parse(
                        r#"(cast-match (true i8) (false i32))"#,
                    ))
                    .unwrap(),
                }),
            ),
            (
                "apply-refiner(%struct.Object, fieldptr(1); cast(!object-tag; fieldptr(0)))",
                Annot::ApplyRefiner(ApplyRefiner {
                    typename: LocalIdent::from("struct.Object"),
                    target: Fieldptr(vec![1]),
                    app: RefinerApp::try_parse(&SExpr::parse(r#"(cast object-tag (fieldptr 0))"#))
                        .unwrap(),
                }),
            ),
        ] {
            assert_eq!(expected, input.to_string(), "{}", input);
        }
    }
    #[test]
    fn annot_try_parse() {
        for (expected, input) in vec![
            (
                "Ok(define-refiner(!object-tag; cast-match(and(true) -> i8; and(false) -> i32)))",
                r#"(define-refiner object-tag (cast-match (true i8) (false i32)))"#,
            ),
            (
                "Ok(apply-refiner(%struct.Object, fieldptr(1); cast(!object-tag; fieldptr(0))))",
                r#"(apply-refiner "struct.Object" (fieldptr 1) (cast object-tag (fieldptr 0)))"#,
            ),
            ("Err(expected annotation, but got sym)", r#"sym"#),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match Annot::try_parse(&sexpr) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn apply_refiner_varmap() {
        for (expected, input) in vec![
            (
                "{(T, !value-tag.cast-tag0) -> $0}",
                r#"(apply-refiner "union.Value" (fieldptr 0) (cast value-tag (fieldptr 1)))"#,
            ),
            (
                "{(T, !vaue-tag.downcast-tag0) -> $0}",
                r#"(apply-refiner "union.Value" baseptr (downcast vaue-tag (fieldptr 1)))"#,
            ),
        ] {
            let sexpr = SExpr::parse(input);
            let annot = Annot::try_parse(&sexpr).expect(input);
            let refiner = match annot {
                Annot::ApplyRefiner(refiner) => refiner,
                annot => panic!("unexpected annotation {}: {}", annot, input),
            };
            let result = refiner.varmap(&"T");
            assert_eq!(expected, result.to_string(), "{}", input);
        }
    }
    #[test]
    fn varmap_insert_dupvars() {
        for (expected, input) in vec![(
            "{(S, !value-tag.cast-tag0) -> $1, (T, !value-tag.cast-tag0) -> $0}",
            r#"(apply-refiner "union.Value" (fieldptr 0) (cast value-tag (fieldptr 1)))"#,
        )] {
            let sexpr = SExpr::parse(input);
            let annot = Annot::try_parse(&sexpr).expect(input);
            let refiner = match annot {
                Annot::ApplyRefiner(refiner) => refiner,
                annot => panic!("unexpected annotation {}: {}", annot, input),
            };
            let mut result = refiner.varmap(&"T");
            result.insert_dupvars("S");
            assert_eq!(expected, result.to_string(), "{}", input);
        }
    }
}
