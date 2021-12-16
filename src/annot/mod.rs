//! The annotation module.

use crate::llir::abi::DataLayout;
use crate::llir::interp::rtti::{ExtIdent, ExtName};
use crate::llir::syntax::{LocalIdent, Type as LLIRType, Typedefs};
use crate::reader::sexpr::{MacroEnv, Parser};
use crate::symbol::Ident;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub mod syntax;
use syntax::{Annot, ApplyRefiner, CastMatch, Fieldptr, Refiner, RefinerApp};

/// A annotation file.
#[derive(Clone, Debug)]
pub struct AnnotFile {
    filename: String,
    refiners: BTreeMap<Ident, Refiner>,
    apply_refiners: Vec<ApplyRefiner>,
}

impl AnnotFile {
    /// Returns a new empty annotation file.
    pub fn empty() -> AnnotFile {
        AnnotFile {
            filename: String::from(""),
            refiners: BTreeMap::new(),
            apply_refiners: Vec::new(),
        }
    }
    /// Returns a parsed annotation file from the given source text with the filename.
    pub fn parse(source: &str, filename: String) -> Result<AnnotFile, String> {
        let mut parser = Parser::new(source, &filename)?;
        let mut env = MacroEnv::empty();
        let mut refiners = BTreeMap::new();
        let mut apply_refiners = Vec::new();
        let mut refineds = BTreeSet::new();
        while let Some(sexpr) = parser.parse()? {
            if env.parse_insert(&sexpr)? {
                continue;
            }
            let sexpr = env.apply(&sexpr);
            let annot = match Annot::try_parse(&sexpr) {
                Ok(annot) => annot,
                Err(err) => return Err(format!("{}: {}", parser.pos(), err)),
            };
            match annot {
                Annot::ApplyRefiner(arg) => {
                    arg.check_validity()?;
                    let refined = (arg.typename(), arg.target().clone());
                    if refineds.contains(&refined) {
                        return Err(format!(
                            "{}: apply-refiner on ({}, {}) multiple times",
                            parser.pos(),
                            refined.0,
                            refined.1,
                        ));
                    }
                    apply_refiners.push(arg);
                    refineds.insert(refined);
                }
                Annot::DefineRefiner(arg) => {
                    if refiners.contains_key(&arg.name()) {
                        return Err(format!("refiner {} is already defined", arg.name()));
                    }
                    refiners.insert(arg.name(), arg.refiner().clone());
                }
            }
        }
        Ok(AnnotFile {
            filename,
            refiners,
            apply_refiners,
        })
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.refiners.is_empty() && self.apply_refiners.is_empty()
    }
    /// Returns the file name.
    pub fn filename(&self) -> &str {
        &self.filename
    }
    /// Returns the refiners.
    pub fn refiners(&self) -> &BTreeMap<Ident, Refiner> {
        &self.refiners
    }
    /// Returns the refiner by name.
    pub fn refiner(&self, name: &Ident) -> Option<&Refiner> {
        self.refiners.get(name)
    }
    /// Returns the refiner application terms.
    pub fn apply_refiners(&self) -> &[ApplyRefiner] {
        &self.apply_refiners
    }
    /// Returns the refiner application term by name.
    pub fn apply_refiner(&self, id: usize) -> Option<&ApplyRefiner> {
        self.apply_refiners.get(id)
    }
    /// Rewrites the given typedefs with the annotation file and the data layout.
    pub fn rewrite_typedefs(
        &self,
        typedefs: &mut Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> Result<(), String> {
        Rewriter::exec(self, typedefs, datalayout)
    }
}

impl fmt::Display for AnnotFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        writeln!(f, "refiners:")?;
        for (name, refiner) in self.refiners.iter() {
            writeln!(f, "  !{}: {}", name, refiner)?;
        }
        writeln!(f, "apply-refiners:")?;
        for (id, apply_refiner) in self.apply_refiners.iter().enumerate() {
            writeln!(f, "  @{}: {}", id, apply_refiner)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RewriteMsg {
    basename: LocalIdent,
    replacer: ExtIdent,
    replacee: Option<LLIRType<ExtIdent>>,
}

impl RewriteMsg {
    fn new(
        basename: LocalIdent,
        replacer: ExtIdent,
        replacee: Option<LLIRType<ExtIdent>>,
        typedefs: &Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> RewriteMsg {
        let mut msg = RewriteMsg {
            basename,
            replacer,
            replacee,
        };
        if let Some(ty0) = typedefs.get(&msg.basename) {
            msg.find_by_replacer(ty0, 0, typedefs, datalayout);
        }
        msg
    }
    fn find_by_replacer(
        &mut self,
        ty0: &LLIRType<ExtIdent>,
        offset: i64,
        typedefs: &Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> Option<()> {
        if self.check_replace(ty0, offset) {
            return Some(());
        }
        match ty0 {
            LLIRType::Struct(packed, fields) => {
                let (i, delta) = datalayout.field_at(
                    *packed,
                    fields,
                    self.replacer.offset - offset,
                    typedefs,
                )?;
                self.find_by_replacer(&fields[i], offset + delta, typedefs, datalayout)
            }
            LLIRType::Name(name) => {
                self.basename = *name;
                self.find_by_replacer(typedefs.get(name)?, offset, typedefs, datalayout)
            }
            LLIRType::Ext(_, ty) => self.find_by_replacer(ty, offset, typedefs, datalayout),
            _ => None,
        }
    }
    fn new_with_fieldptr(
        basename: LocalIdent,
        replacer: ExtIdent,
        indices: &Fieldptr,
        typedefs: &Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> Result<RewriteMsg, String> {
        let mut msg = RewriteMsg {
            basename,
            replacer,
            replacee: None,
        };
        if let Some(ty0) = typedefs.get(&msg.basename) {
            if let Some(()) = msg.find_by_indices(ty0, indices, typedefs, datalayout) {
                return Ok(msg);
            }
        }
        Err(format!(
            "cannot replace type at {} in {} with {}",
            indices, basename, replacer,
        ))
    }
    fn find_by_indices(
        &mut self,
        ty0: &LLIRType<ExtIdent>,
        indices: &[u64],
        typedefs: &Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> Option<()> {
        if indices.is_empty() {
            return match ty0 {
                LLIRType::Ext(..) => None,
                _ => {
                    self.replacee = Some(ty0.clone());
                    Some(())
                }
            };
        }
        match ty0 {
            LLIRType::Struct(packed, fields) => {
                let i = indices[0] as usize;
                if i >= fields.len() {
                    return None;
                }
                let delta = datalayout.offsetof_field(*packed, fields, i, typedefs)?;
                let offset = self.replacer.offset + delta;
                self.replacer = ExtIdent {
                    name: self.replacer.name,
                    appid: self.replacer.appid,
                    offset,
                };
                self.find_by_indices(&fields[i], &indices[1..], typedefs, datalayout)
            }
            LLIRType::Name(name) => {
                self.basename = *name;
                self.find_by_indices(typedefs.get(name)?, indices, typedefs, datalayout)
            }
            LLIRType::Ext(_, ty) => self.find_by_indices(ty, indices, typedefs, datalayout),
            _ => None,
        }
    }
    fn apply(
        &self,
        typedefs: &mut Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> Result<(), String> {
        let ty = match typedefs.get(&self.basename) {
            Some(ty) => ty,
            None => return Ok(()),
        };
        let ty = match self.do_apply(ty, 0, typedefs, datalayout) {
            Some(ty) => ty,
            None => {
                return Err(format!(
                    "cannot replace type with {} in {}",
                    self.replacer, self.basename,
                ))
            }
        };
        typedefs.insert(self.basename, ty);
        Ok(())
    }
    fn do_apply(
        &self,
        ty: &LLIRType<ExtIdent>,
        offset: i64,
        typedefs: &Typedefs<ExtIdent>,
        datalayout: &DataLayout,
    ) -> Option<LLIRType<ExtIdent>> {
        if self.check_replace(ty, offset) {
            return match ty {
                LLIRType::Ext(ExtIdent { name, .. }, _) => match name == &self.replacer.name {
                    true => Some(ty.clone()),
                    false => None,
                },
                _ => Some(LLIRType::Ext(self.replacer, Box::new(ty.clone()))),
            };
        }
        match ty {
            LLIRType::Struct(packed, fields) => {
                let (i, delta) = datalayout.field_at(
                    *packed,
                    fields,
                    self.replacer.offset - offset,
                    typedefs,
                )?;
                let mut fields = fields.clone();
                fields[i] = self.do_apply(&fields[i], offset + delta, typedefs, datalayout)?;
                Some(LLIRType::Struct(*packed, fields))
            }
            LLIRType::Ext(id, ty0) => match id.name == self.replacer.name {
                true => Some(ty.clone()),
                false => {
                    let ty = self.do_apply(ty0, offset, typedefs, datalayout)?;
                    Some(LLIRType::Ext(*id, Box::new(ty)))
                }
            },
            _ => None,
        }
    }
    fn check_replace(&self, ty: &LLIRType<ExtIdent>, offset: i64) -> bool {
        if offset == self.replacer.offset {
            return match &self.replacee {
                Some(replacee) => replacee == ty,
                None => true,
            };
        }
        false
    }
}

struct Rewriter<'a, 'b, 'c> {
    file: &'a AnnotFile,
    typedefs: &'b mut Typedefs<ExtIdent>,
    datalayout: &'c DataLayout,
    queue: Vec<RewriteMsg>,
}

impl<'a, 'b, 'c> Rewriter<'a, 'b, 'c> {
    fn exec(
        file: &'a AnnotFile,
        typedefs: &'b mut Typedefs<ExtIdent>,
        datalayout: &'c DataLayout,
    ) -> Result<(), String> {
        let mut rewriter = Rewriter {
            file,
            typedefs,
            datalayout,
            queue: Vec::new(),
        };
        for (appid, cmd) in rewriter.file.apply_refiners().iter().enumerate() {
            match rewriter.file.refiner(&cmd.app().name()) {
                Some(refiner) => match refiner {
                    Refiner::CastMatch(cm) => rewriter.check_cast_match(appid, cmd, cm)?,
                    Refiner::RestrictCastMatch(_) => {
                        rewriter.check_restrict_cast_match(appid, cmd)?
                    }
                },
                None => return Err(format!("refiner {} not found", cmd.app().name())),
            }
        }
        for msg in rewriter.queue {
            msg.apply(typedefs, datalayout)?;
        }
        Ok(())
    }
    fn check_field(
        &mut self,
        cm: &CastMatch,
        app: &RefinerApp,
        basename: LocalIdent,
        indices: &Fieldptr,
        replacer: ExtIdent,
    ) -> Result<(), String> {
        let msg = RewriteMsg::new_with_fieldptr(
            basename,
            replacer,
            indices,
            self.typedefs,
            self.datalayout,
        )?;
        self.queue.push(msg.clone());
        if let RefinerApp::Downcast(..) = app {
            for (i, case) in cm.cases().iter().enumerate() {
                if let LLIRType::Name(basename) = case.target() {
                    let (name, replacee) = match replacer.name.is_downcast_target() {
                        true => (ExtName::DowncastSubtarget(replacer.name.id(), i), None),
                        false => (replacer.name, msg.replacee.clone()),
                    };
                    let replacer = ExtIdent {
                        name,
                        appid: replacer.appid,
                        offset: msg.replacer.offset,
                    };
                    let msg = RewriteMsg::new(
                        *basename,
                        replacer,
                        replacee,
                        self.typedefs,
                        self.datalayout,
                    );
                    self.queue.push(msg);
                }
            }
        }
        Ok(())
    }
    fn check_cast_match(
        &mut self,
        appid: usize,
        cmd: &ApplyRefiner,
        cm: &CastMatch,
    ) -> Result<(), String> {
        let app = cmd.app();
        let (basename, indices) = (cmd.typename(), cmd.target());
        let ty = match self.typedefs.get(&basename) {
            Some(ty) => ty,
            None => return Ok(()),
        };
        if let LLIRType::Opaque = ty {
            return Ok(());
        }
        let ident = ExtIdent {
            name: app.extname_target(),
            appid,
            offset: 0,
        };
        self.check_field(cm, app, basename, indices, ident)?;
        let varmap = cmd.varmap(&0);
        for ((_, name), var) in varmap.iter() {
            let tag = &app.tags()[var.id()];
            if cmd.target() != tag {
                let ident = ExtIdent {
                    name: *name,
                    appid,
                    offset: 0,
                };
                self.check_field(cm, app, basename, tag, ident)?;
            }
        }
        Ok(())
    }
    fn check_restrict_cast_match(
        &mut self,
        appid: usize,
        cmd: &ApplyRefiner,
    ) -> Result<(), String> {
        let app = cmd.app();
        let (basename, indices) = (cmd.typename(), &cmd.target());
        let ty = match self.typedefs.get(&basename) {
            Some(ty) => ty,
            None => return Ok(()),
        };
        if let LLIRType::Opaque = ty {
            return Ok(());
        }
        let replacer = ExtIdent {
            name: app.extname_target(),
            appid,
            offset: 0,
        };
        let msg = RewriteMsg::new_with_fieldptr(
            basename,
            replacer,
            indices,
            self.typedefs,
            self.datalayout,
        )?;
        self.queue.push(msg);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llir::parser::Parser as LLIRParser;
    #[test]
    fn annotfile_parse_check_validity() {
        for (expected, input) in vec![
            (
                "cast cannot set on baseptr",
                r#"(apply-refiner "struct.Object" baseptr (cast object-tag (fieldptr 0)))"#,
            ),
            (
                "cast cannot use baseptr as tag not disjoint with target fieldptr(0)",
                r#"(apply-refiner "struct.Object" (fieldptr 0) (cast object-tag baseptr))"#,
            ),
            (
                "cast cannot use fieldptr(0, 1) as tag not disjoint with target fieldptr(0)",
                r#"(apply-refiner "struct.Object" (fieldptr 0) (cast object-tag (fieldptr 0 1)))"#,
            ),
            (
                "cast cannot use fieldptr(1) as tag not disjoint with another tag fieldptr(1, 2)",
                r#"(apply-refiner "struct.Object" (fieldptr 0) (cast object-tag (fieldptr 1 2) (fieldptr 1)))"#,
            ),
            (
                "downcast cannot use fieldptr(0) as tag not truly contained in target fieldptr(0)",
                r#"(apply-refiner "struct.Object" (fieldptr 0) (downcast object-tag (fieldptr 0)))"#,
            ),
            (
                "downcast cannot use fieldptr(0, 1) as tag not disjoint with another tag fieldptr(0, 1, 2)",
                r#"(apply-refiner "struct.Object" (fieldptr 0) (downcast object-tag (fieldptr 0 1 2) (fieldptr 0 1)))"#,
            ),
        ] {
            match AnnotFile::parse(input, String::from("annot")) {
                Ok(_) => panic!("expected error, but got Ok(_): {}", input),
                Err(err) => assert_eq!(expected, err.to_string(), "{}", input),
            }
        }
    }
    #[test]
    fn annotfile_rewrite_typedefs() {
        let datalayout = DataLayout::lp64();
        let mut typedefs = Typedefs::new(btree_map![
            LocalIdent::from("tagged-union1") => LLIRParser::new_type("{ i32, i64 }"),
            LocalIdent::from("tagged-union2") => LLIRParser::new_type("{ i32, %other }"),
            LocalIdent::from("tagged-union3") => LLIRParser::new_type("{ %other, i64 }"),
            LocalIdent::from("object1") => LLIRParser::new_type("{ i64, i64 }"),
            LocalIdent::from("object1-sub1") => LLIRParser::new_type("{ i64, i64, i32 }"),
            LocalIdent::from("object1-sub2") => LLIRParser::new_type("{ { i64, i64 }, i64 }"),
            LocalIdent::from("object2") => LLIRParser::new_type("{ i64, i64 }"),
            LocalIdent::from("object2-sub1") => LLIRParser::new_type("{ %object2, i32 }"),
            LocalIdent::from("object2-sub2") => LLIRParser::new_type("{ %object2, i64 }"),
            LocalIdent::from("other") => LLIRParser::new_type("i64")
        ]);
        let annotfile = AnnotFile::parse(
            r#"
            (define-refiner tagged-union1-tag (cast-match))
            (apply-refiner "tagged-union1" (fieldptr 1) (cast tagged-union1-tag (fieldptr 0)))
            (define-refiner tagged-union2-tag (cast-match))
            (apply-refiner "tagged-union2" (fieldptr 1) (cast tagged-union2-tag (fieldptr 0)))
            (define-refiner tagged-union3-tag (cast-match))
            (apply-refiner "tagged-union3" (fieldptr 1) (cast tagged-union3-tag (fieldptr 0)))
            (define-refiner object1-tag (cast-match
              (true "object1-sub1")
              (true "object1-sub2")))
            (apply-refiner "object1" baseptr (downcast object1-tag (fieldptr 1)))
            (define-refiner object2-tag (cast-match
              (true "object2-sub1")
              (true "object2-sub2")))
            (apply-refiner "object2" baseptr (downcast object2-tag (fieldptr 0)))
            "#,
            String::from("annot"),
        )
        .unwrap();
        annotfile
            .rewrite_typedefs(&mut typedefs, &datalayout)
            .unwrap();
        assert_eq!(10, typedefs.len());
        for (name, expected) in btree_map![
           "tagged-union1" => "{ !tagged-union1-tag.cast-tag0@0+0(i32), !tagged-union1-tag.cast-target@0+8(i64) }",
           "tagged-union2" => "{ !tagged-union2-tag.cast-tag0@1+0(i32), !tagged-union2-tag.cast-target@1+8(%other) }",
           "tagged-union3" => "{ !tagged-union3-tag.cast-tag0@2+0(%other), !tagged-union3-tag.cast-target@2+8(i64) }",
           "object1" => "!object1-tag.downcast-target@3+0({ i64, !object1-tag.downcast-tag0@3+8(i64) })",
           "object1-sub1" => "!object1-tag.downcast-subtarget0@3+0({ i64, !object1-tag.downcast-tag0@3+8(i64), i32 })",
           "object1-sub2" => "!object1-tag.downcast-subtarget1@3+0({ { i64, !object1-tag.downcast-tag0@3+8(i64) }, i64 })",
           "object2" => "!object2-tag.downcast-target@4+0({ !object2-tag.downcast-tag0@4+0(i64), i64 })",
           "object2-sub1" => "!object2-tag.downcast-subtarget0@4+0({ %object2, i32 })",
           "object2-sub2" => "!object2-tag.downcast-subtarget1@4+0({ %object2, i64 })",
           "other" => "i64"
        ] {
            let got = typedefs.get(&LocalIdent::from(name)).expect(name);
            assert_eq!(expected, got.to_string(), "{}", name);
        }
    }
}
