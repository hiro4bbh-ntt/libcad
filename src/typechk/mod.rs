//! The type checking module.

use crate::annot::AnnotFile;
use crate::fmt::DisplayIter;
use crate::llir::interp::rtti::ExtIdent;
use crate::llir::syntax::{
    CallBody, Callee, ConvOpArgs, ConvOpcode, FuncSig, GlobalIdent, Insn, Label, Loc, LocLineInfo,
    LocalIdent, Module, ParamValue, Type as LLIRType, TypedValue, Value,
};
use std::collections::BTreeMap;
use std::fmt;

pub mod cast;
pub mod env;
pub mod syntax;

use cast::{CastChk, CastChkResult, Resolver};
use env::{InternMode, TypeEnv};
use syntax::{
    AllocKind, CastReason, Constr, ConstrKind, Constrs, EffectKind, FreeKind, FuncArgs, JudgeTerm,
    Size, Type, ValueExt, VarName,
};

/// A type checker of a LLIR module with an annotation file.
pub struct TypeChk<'a, 'b> {
    annotfile: &'a AnnotFile,
    module: &'b Module<ExtIdent>,
    env: TypeEnv,
    constrs: Constrs,
    errors: BTreeMap<Loc, String>,
    resolver: Resolver<usize>,
}

impl<'a, 'b> TypeChk<'a, 'b> {
    /// Returns a new type checker for the given LLIR module with the given annotation file.
    pub fn new(
        annotfile: &'a AnnotFile,
        module: &'b Module<ExtIdent>,
    ) -> Result<TypeChk<'a, 'b>, String> {
        Ok(TypeChk {
            annotfile,
            module,
            env: TypeEnv::empty(module.target_datalayout().clone()),
            constrs: Constrs::empty(),
            errors: BTreeMap::new(),
            resolver: Resolver::new(),
        })
    }
    /// Returns the annotation file.
    pub fn annotfile(&self) -> &AnnotFile {
        self.annotfile
    }
    /// Returns the module.
    pub fn module(&self) -> &Module<ExtIdent> {
        self.module
    }
    /// Returns the instruction at the location.
    pub fn insn(&self, loc: &Loc) -> Option<&Insn<ExtIdent>> {
        if loc.insnidx == 0 {
            return None;
        }
        let (_, blocks) = self.module.funcs().get(&loc.func)?;
        let block = blocks.block(&loc.block)?;
        block.insns.get(loc.insnidx - 1)
    }
    /// Returns the typing environment.
    pub fn env(&self) -> &TypeEnv {
        &self.env
    }
    /// Returns the constraints.
    pub fn constrs(&self) -> &Constrs {
        &self.constrs
    }
    /// Returns the errors which is a map from the location to the message string.
    pub fn errors(&self) -> &BTreeMap<Loc, String> {
        &self.errors
    }
    fn intern_type(&mut self, ty: &LLIRType<ExtIdent>, loc: &Loc) -> Result<Type, String> {
        self.env.intern_fresh_llir_type(ty, loc)
    }
    fn intern_type_value(
        &mut self,
        mode: InternMode,
        ty: Option<&LLIRType<ExtIdent>>,
        val: &Value<ExtIdent>,
        loc: &Loc,
    ) -> Result<Type, String> {
        self.env
            .intern_type_value(mode, ty, val, loc, &mut self.constrs)
    }
    fn intern_typedvalue(
        &mut self,
        mode: InternMode,
        tyval: &TypedValue<ExtIdent>,
        loc: &Loc,
    ) -> Result<Type, String> {
        self.env
            .intern_typedvalue(mode, tyval, loc, &mut self.constrs)
    }
    fn intern_param_value(
        &mut self,
        mode: InternMode,
        pval: &ParamValue<ExtIdent>,
        loc: &Loc,
    ) -> Result<Type, String> {
        self.intern_type_value(mode, Some(&(pval.0).ty), &pval.1, loc)
    }
    fn intern_value_expr(
        &mut self,
        mode: InternMode,
        val: &Value<ExtIdent>,
        loc: &Loc,
    ) -> Result<Type, String> {
        self.env
            .intern_value_expr(mode, val, loc, &mut self.constrs)
    }
    fn intern_value_ext(
        &mut self,
        mode: InternMode,
        val: ValueExt,
        loc: &Loc,
    ) -> Result<Type, String> {
        self.env.intern_value_ext(mode, val, loc, &mut self.constrs)
    }
    fn judge_term(&mut self, term: JudgeTerm, loc: &Loc) -> Result<(), String> {
        self.env.judge_term(term, loc, &mut self.constrs)
    }
    fn declare_result_var(&mut self, insn: &Insn<ExtIdent>, loc: &Loc) -> Result<(), String> {
        match insn {
            Insn::Alloca { res, ty, .. } => {
                let val = ValueExt::Alloc(AllocKind::Alloca, ty.clone());
                let ty = self.intern_value_ext(InternMode::Declare, val, loc)?;
                self.env.declare_var(VarName::Local(*res, loc.func), ty)
            }
            Insn::Br(_)
            | Insn::BrI1(..)
            | Insn::Indirectbr(..)
            | Insn::Resume(_)
            | Insn::Switch(..)
            | Insn::Unreachable => Ok(()),
            Insn::Call {
                res: None,
                body: CallBody { callee, args, .. },
                ..
            }
            | Insn::Invoke {
                res: None,
                body: CallBody { callee, args, .. },
                ..
            } => match callee {
                Callee::Value(Value::GlobalRef(name @ global_ident!("free")))
                | Callee::Value(Value::GlobalRef(name @ global_ident!("_ZdlPv")))
                    if args.len() == 1 =>
                {
                    self.constrs
                        .insert(Constr::Free(FreeKind::Dynamic(*name)), *loc)?;
                    Ok(())
                }
                _ => Ok(()),
            },
            Insn::Call {
                res: Some(res),
                body: CallBody {
                    ret, callee, args, ..
                },
                ..
            }
            | Insn::Invoke {
                res: Some(res),
                body: CallBody {
                    ret, callee, args, ..
                },
                ..
            } => {
                let ty = match callee {
                    Callee::Value(Value::GlobalRef(name)) if name.is_dbg_intr() => return Ok(()),
                    Callee::Value(Value::GlobalRef(name @ global_ident!("malloc")))
                    | Callee::Value(Value::GlobalRef(name @ global_ident!("_Znwm")))
                        if args.len() == 1 =>
                    {
                        let kind = AllocKind::Dynamic(*name);
                        let len = Size::from(args[0].1.try_to_i64());
                        let val = ValueExt::Poison(kind, len);
                        self.intern_value_ext(InternMode::Declare, val, loc)?
                    }
                    _ => match &ret.ty {
                        LLIRType::Func(sig) => self.intern_type(&sig.ret.ty, loc)?,
                        _ => self.intern_type(&ret.ty, loc)?,
                    },
                };
                self.env.declare_var(VarName::Local(*res, loc.func), ty)
            }
            Insn::Landingpad { res, ty, .. }
            | Insn::Load { res, ty, .. }
            | Insn::Phi { res, ty, .. } => {
                let ty = self.intern_type(ty, loc)?;
                self.env.declare_var(VarName::Local(*res, loc.func), ty)
            }
            Insn::Ret(_) | Insn::Store { .. } => Ok(()),
            Insn::Select(res, _, TypedValue(ty1, _), TypedValue(ty2, _)) => {
                if ty1 != ty2 {
                    return Err(format!("selected types must be equal: {} != {}", ty1, ty2));
                }
                let ty = self.intern_type(ty1, loc)?;
                self.env.declare_var(VarName::Local(*res, loc.func), ty)
            }
            Insn::Value(res, val) => {
                let ty = self.intern_value_expr(InternMode::Declare, val, loc)?;
                self.env.declare_var(VarName::Local(*res, loc.func), ty)
            }
        }
    }
    fn interpret_insn_call_global(
        &mut self,
        res: &Option<LocalIdent>,
        name: &GlobalIdent,
        args: &[ParamValue<ExtIdent>],
        loc: &Loc,
    ) -> Result<(), String> {
        let func = self.env.func(name)?.clone();
        let (argnames, variadic) = (func.argnames, func.variadic);
        if variadic && argnames.len() > args.len() {
            return Err(format!(
                "expected at least {} argument(s) by function {}, but got {} argument(s)",
                argnames.len(),
                name,
                args.len()
            ));
        } else if !variadic && argnames.len() != args.len() {
            return Err(format!(
                "expected {} argument(s) by function {}, but got {} argument(s)",
                argnames.len(),
                name,
                args.len()
            ));
        }
        // Assume that variadic function should be handled in Refiner, so variadic arguments are ignored.
        let nargs = argnames.len();
        for i in 0..nargs {
            let arg = self.env.var(&argnames[i])?.clone();
            let ty = self.intern_param_value(InternMode::Define, &args[i], loc)?;
            self.judge_term(JudgeTerm::Cast(ty, arg), loc)?;
        }
        if let Some(res) = res {
            let ret = self.env.var(&VarName::Ret(*name))?.clone();
            let var = self.env.var(&VarName::Local(*res, loc.func))?.clone();
            self.judge_term(JudgeTerm::Cast(ret, var), loc)?;
        }
        self.env.insert_effect(*loc, EffectKind::CallGlobal(*name));
        Ok(())
    }
    fn interpret_insn_call_value(
        &mut self,
        res: &Option<LocalIdent>,
        ptr: &Value<ExtIdent>,
        args: &[ParamValue<ExtIdent>],
        loc: &Loc,
    ) -> Result<(), String> {
        match ptr {
            Value::GlobalRef(name) if name.is_dbg_intr() => Ok(()),
            Value::GlobalRef(global_ident!("free")) | Value::GlobalRef(global_ident!("_ZdlPv"))
                if res.is_none() && args.len() == 1 =>
            {
                Ok(())
            }
            Value::GlobalRef(global_ident!("malloc"))
            | Value::GlobalRef(global_ident!("_Znwm"))
                if res.is_some() && args.len() == 1 =>
            {
                Ok(())
            }
            Value::GlobalRef(global_ident!("llvm.memcpy.p0i8.p0i8.i64"))
                if res.is_none() && args.len() == 4 =>
            {
                let dst = self.intern_param_value(InternMode::Define, &args[0], loc)?;
                let src = self.intern_param_value(InternMode::Define, &args[1], loc)?;
                let len = Size::from(args[2].1.try_to_i64());
                self.judge_term(JudgeTerm::Memcpy(dst, src, len), loc)
            }
            Value::LocalRef(_) => {
                let ty = self.intern_type_value(InternMode::Define, None, ptr, loc)?;
                if let Type::Ptr(_, fnty) = &ty {
                    if let Type::Func(..) = fnty.as_ref() {
                        self.constrs.insert(Constr::IndirectCall(ty), *loc)?;
                        self.env.insert_effect(*loc, EffectKind::CallIndirect);
                        return Ok(());
                    }
                }
                Err(format!("cannot call {}", ty))
            }
            Value::GlobalRef(name) => self.interpret_insn_call_global(res, name, args, loc),
            Value::ConvOp(convargs) => {
                let ConvOpArgs {
                    opcode,
                    srctyval: TypedValue(_, srcval),
                    ..
                } = convargs as &ConvOpArgs<_>;
                match opcode {
                    ConvOpcode::Bitcast => self.interpret_insn_call_value(res, srcval, args, loc),
                    _ => Err(format!("cannot call {}", ptr)),
                }
            }
            ptr => Err(format!("cannot call {}", ptr)),
        }
    }
    fn interpret_insn(&mut self, insn: &Insn<ExtIdent>, loc: &Loc) -> Result<(), String> {
        match insn {
            Insn::Alloca { .. } => Ok(()),
            Insn::Br(_) | Insn::Unreachable => Ok(()),
            Insn::BrI1(val, ..) => {
                let ty = Type::I(1);
                let val = self.intern_value_expr(InternMode::Define, val, loc)?;
                self.judge_term(JudgeTerm::Cast(val, ty), loc)
            }
            Insn::Call {
                res,
                body: CallBody { callee, args, .. },
                ..
            }
            | Insn::Invoke {
                res,
                body: CallBody { callee, args, .. },
                ..
            } => match callee {
                Callee::Value(val) => self.interpret_insn_call_value(res, val, args, loc),
                Callee::Asm(..) => {
                    self.constrs.insert(
                        Constr::UnsupportedFeature(format!("relating asm: {}", insn)),
                        *loc,
                    )?;
                    Ok(())
                }
            },
            Insn::Indirectbr(..) => {
                self.constrs.insert(
                    Constr::UnsupportedFeature(format!("relating indirect branch: {}", insn)),
                    *loc,
                )?;
                Ok(())
            }
            Insn::Landingpad { .. } => {
                self.constrs.insert(
                    Constr::UnsupportedFeature(format!("relating exception handlers: {}", insn)),
                    *loc,
                )?;
                Ok(())
            }
            Insn::Load { res, src, .. } => {
                let ty = self.env.var(&VarName::Local(*res, loc.func))?.clone();
                let src = self.intern_typedvalue(InternMode::Define, src, loc)?;
                self.judge_term(JudgeTerm::Load(ty, src), loc)
            }
            Insn::Phi {
                res,
                ty: valty,
                val_labels,
            } => {
                let ty = self.env.var(&VarName::Local(*res, loc.func))?.clone();
                for (val, _) in val_labels {
                    match val {
                        Value::Undef | Value::Zeroinitializer => {}
                        _ => {
                            let val =
                                self.intern_type_value(InternMode::Define, Some(valty), val, loc)?;
                            self.judge_term(JudgeTerm::Cast(val, ty.clone()), loc)?;
                        }
                    }
                }
                Ok(())
            }
            Insn::Ret(tyval) => {
                let ty = match tyval {
                    Some(tyval) => self.intern_typedvalue(InternMode::Define, tyval, loc)?,
                    None => self.intern_type(&LLIRType::Void, loc)?,
                };
                let var = self.env.var(&VarName::Ret(loc.func))?.clone();
                self.judge_term(JudgeTerm::Cast(ty, var), loc)
            }
            Insn::Resume(_) => {
                self.constrs.insert(
                    Constr::UnsupportedFeature(format!("relating exception handlers: {}", insn)),
                    *loc,
                )?;
                Ok(())
            }
            Insn::Switch(tyval, _, cases) => {
                if !tyval.0.is_int() {
                    return Err(format!(
                        "switch value must be integer type but is {}",
                        &tyval.0
                    ));
                }
                let ty = self.intern_type(&tyval.0, loc)?;
                let val = self.intern_typedvalue(InternMode::Define, tyval, loc)?;
                self.judge_term(JudgeTerm::Cast(ty, val), loc)?;
                for case in cases {
                    let case_tyval = &case.0;
                    if case_tyval.0 != tyval.0 {
                        return Err(format!(
                            "switch case type must be match: {} != {}",
                            &case_tyval.0, &tyval.0
                        ));
                    }
                    let ty = self.intern_type(&case_tyval.0, loc)?;
                    let val = self.intern_typedvalue(InternMode::Define, case_tyval, loc)?;
                    self.judge_term(JudgeTerm::Cast(ty, val), loc)?;
                }
                Ok(())
            }
            Insn::Select(res, _, tyval1, tyval2) => {
                let ty = self.env.var(&VarName::Local(*res, loc.func))?.clone();
                let val1 = self.intern_typedvalue(InternMode::Define, tyval1, loc)?;
                let val2 = self.intern_typedvalue(InternMode::Define, tyval2, loc)?;
                self.judge_term(JudgeTerm::Cast(val1, ty.clone()), loc)?;
                self.judge_term(JudgeTerm::Cast(val2, ty), loc)
            }
            Insn::Store { src, dst, .. } => {
                let size = match &dst.0 {
                    LLIRType::Ptr(ty) => {
                        match self.env.datalayout().sizeof_type(ty, self.env.typedefs()) {
                            Some(size) => size,
                            None => return Err(format!("unknown size of stored type {}", ty)),
                        }
                    }
                    _ => return Err(format!("destination must be pointer, but got {}", dst)),
                };
                let src = self.intern_typedvalue(InternMode::Define, src, loc)?;
                let srcptr = Type::Ptr(self.env.new_infervar(), Box::new(src));
                let dst = self.intern_typedvalue(InternMode::Define, dst, loc)?;
                self.judge_term(JudgeTerm::Memcpy(dst, srcptr, Size::Const(size)), loc)
            }
            Insn::Value(res, val) => {
                let ty = self.env.var(&VarName::Local(*res, loc.func))?.clone();
                let val = self.intern_value_expr(InternMode::Define, val, loc)?;
                self.judge_term(JudgeTerm::Cast(val, ty), loc)
            }
        }
    }
    fn declare_type(
        &mut self,
        name: &LocalIdent,
        prototype: &LLIRType<ExtIdent>,
    ) -> Result<(), String> {
        let loc = Loc::new(GlobalIdent::from(""), Label::from(LocalIdent::from("")), 0);
        let ty = self.intern_type(prototype, &loc)?;
        self.env.define_type(*name, prototype.clone(), ty)
    }
    fn declare_global(
        &mut self,
        name: &GlobalIdent,
        ty: &LLIRType<ExtIdent>,
    ) -> Result<(), String> {
        let loc = Loc::new(*name, Label::from(LocalIdent::from("")), 0);
        let val = ValueExt::DeclareGlobal(ty.clone());
        let ty = self.intern_value_ext(InternMode::Declare, val, &loc)?;
        self.env.declare_var(VarName::Global(*name), ty)
    }
    fn declare_func(&mut self, name: &GlobalIdent, sig: &FuncSig<ExtIdent>) -> Result<(), String> {
        // Ignore special debug intrinsic.
        if name.is_dbg_intr() {
            return Ok(());
        }
        let loc = Loc::new(*name, Label::from(LocalIdent::from("")), 0);
        let mut args = Vec::with_capacity(sig.args.len());
        let mut argnames = Vec::with_capacity(sig.args.len());
        for (i, arg) in sig.args.iter().enumerate() {
            let regname = match arg.name {
                Some(name) => name,
                None => LocalIdent::from(format!("{}", i)),
            };
            let arg = self.intern_type(&arg.ty, &loc)?;
            let varname = VarName::Local(regname, *name);
            self.env.declare_var(varname, arg.clone())?;
            args.push(arg);
            argnames.push(varname);
        }
        let ret = self.intern_type(&sig.ret.ty, &loc)?;
        self.env.declare_var(VarName::Ret(*name), ret.clone())?;
        let val = ValueExt::DeclareFunc(ret, args, sig.variadic);
        let ty = self.intern_value_ext(InternMode::Declare, val, &loc)?;
        let args = FuncArgs {
            argnames,
            variadic: sig.variadic,
        };
        self.env.declare_func(*name, ty, args)
    }
    fn define_global(
        &mut self,
        name: &GlobalIdent,
        ty: &LLIRType<ExtIdent>,
        val: &Value<ExtIdent>,
    ) -> Result<(), String> {
        let loc = Loc::new(*name, Label::from(LocalIdent::from("")), 0);
        let val = ValueExt::DefineGlobal(ty.clone(), val.clone());
        let ty = self.intern_value_ext(InternMode::Define, val, &loc)?;
        let var = self.env.var(&VarName::Global(*name))?.clone();
        let term = JudgeTerm::Cast(ty, var);
        self.judge_term(term, &loc)
    }
    fn prepare_env(&mut self) -> Result<(), String> {
        for name in self.module.typedef_order() {
            let prototype = self.module.typedefs().get(name).unwrap();
            if let Err(err) = self.declare_type(name, prototype) {
                return Err(format!("cannot define type {}: {}", name, err));
            }
        }
        for (name, (ty, _)) in self.module.globals() {
            if let Err(err) = self.declare_global(name, ty) {
                return Err(format!("cannot declare global {}: {}", name, err));
            }
        }
        for (name, (decl, _)) in self.module.funcs() {
            if let Err(err) = self.declare_func(name, &decl.sig) {
                return Err(format!("cannot declare func {}: {}", name, err));
            }
        }
        for (name, (ty, val)) in self.module.globals() {
            if let Some(val) = val {
                if let Err(err) = self.define_global(name, ty, val) {
                    return Err(format!("cannot define global {}: {}", name, err));
                }
            }
        }
        Ok(())
    }
    fn declare_result_vars(&mut self) -> Result<(), String> {
        for (name, (_, blocks)) in self.module.funcs() {
            for block in blocks.iter() {
                let mut loc = Loc::new(*name, block.name, 0);
                let mut failed = false;
                for insn in &block.insns {
                    loc.insnidx += 1;
                    if let Err(err) = self.declare_result_var(insn, &loc) {
                        self.errors.insert(loc, format!("{}: {}", insn, err));
                        failed = true;
                        break;
                    }
                }
                if failed {
                    break;
                }
            }
        }
        if !self.errors.is_empty() {
            return Err(format!(
                "{} error(s) found in DeclareResultVars phase",
                self.errors.len()
            ));
        }
        Ok(())
    }
    fn interpret_insns(&mut self) -> Result<(), String> {
        for (name, (_, blocks)) in self.module.funcs() {
            for block in blocks.iter() {
                let mut loc = Loc::new(*name, block.name, 0);
                for insn in &block.insns {
                    loc.insnidx += 1;
                    if let Err(err) = self.interpret_insn(insn, &loc) {
                        self.errors.insert(loc, format!("{}: {}", insn, err));
                    }
                }
            }
        }
        if !self.errors.is_empty() {
            return Err(format!(
                "{} error(s) found in InterpretInsns phase",
                self.errors.len()
            ));
        }
        Ok(())
    }
    /// Conduct the type checking.
    pub fn check_types(&mut self) -> Result<(), String> {
        self.prepare_env()?;
        self.declare_result_vars()?;
        self.interpret_insns()?;
        Ok(())
    }
    /// Conduct the cast checking.
    pub fn check_casts(&mut self) -> Result<(), String> {
        CastChk::check_annot_file_validity(self.annotfile, &self.env)?;
        for (id, (loc, reason)) in self.constrs.iter().enumerate() {
            if let Some(reason) = reason.try_to_cast_reason(&self.env) {
                let castchk = CastChk::from_cast_reason(&reason, loc);
                let res = castchk.run(self.annotfile, &self.env, self.module);
                self.resolver.import_result(id, res, *loc);
            }
        }
        for (id, (loc, reason)) in self.constrs.iter().enumerate() {
            if let Some(reason) = reason.try_to_cast_reason(&self.env) {
                self.resolver.propagate_resolved(id, &(*loc, reason.peid()));
            }
        }
        Ok(())
    }
    /// Returns a type checking report.
    pub fn report(&self) -> TypeChkReport {
        let mut castwarns = Vec::new();
        for (id, res) in self.resolver.results().iter() {
            let (loc, reason) = self.constrs.get(*id).unwrap();
            let reason = reason.try_to_cast_reason(&self.env).unwrap();
            let msg = match self.resolver.dstset(id) {
                Some(locset) if !locset.contains(loc) => {
                    let mut locs = Vec::with_capacity(locset.len());
                    for loc in locset {
                        locs.push(loc.with_lineinfo(self.module));
                    }
                    CastWarnMsg::ValidResolvedAt(locs)
                }
                Some(_) => CastWarnMsg::Valid(res.clone()),
                None => CastWarnMsg::Unsafe(res.clone()),
            };
            castwarns.push(CastWarn {
                loc: loc.with_lineinfo(self.module),
                reason,
                msg,
            });
        }
        let mut typewarns = Vec::new();
        for (i, (loc, reason)) in self.constrs.iter().enumerate() {
            if !reason.is_warning() || self.resolver.dstset(&i).is_some() {
                continue;
            }
            typewarns.push(TypeWarn {
                loc: loc.with_lineinfo(self.module),
                insn: self.insn(loc).cloned(),
                reason: reason.clone(),
            })
        }
        TypeChkReport {
            castwarns,
            typewarns,
        }
    }
}

/// A message of [`CastWarn`].
#[derive(Clone, PartialEq)]
pub enum CastWarnMsg {
    /// Indicating an unsafe cast.
    Unsafe(CastChkResult),
    /// Indicating a valid cast.
    Valid(CastChkResult),
    /// Indicating a valid cast because resolved at elsewhere.
    ValidResolvedAt(Vec<LocLineInfo>),
}

impl CastWarnMsg {
    /// Returns true if the warning indicates the valid cast.
    pub fn is_valid(&self) -> bool {
        match self {
            CastWarnMsg::Unsafe(_) => false,
            CastWarnMsg::Valid(_) | CastWarnMsg::ValidResolvedAt(_) => true,
        }
    }
}

impl fmt::Debug for CastWarnMsg {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CastWarnMsg::Unsafe(res) | CastWarnMsg::Valid(res) => {
                write!(f, "{}: in {}", res.kind, res.state)
            }
            CastWarnMsg::ValidResolvedAt(locs) => {
                write!(
                    f,
                    "valid because resolved at {}",
                    DisplayIter("", locs.iter(), ", ", "")
                )
            }
        }
    }
}

impl fmt::Display for CastWarnMsg {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CastWarnMsg::Valid(res) | CastWarnMsg::Unsafe(res) => write!(f, "{}", res.kind),
            _ => write!(f, "{:?}", self),
        }
    }
}

/// A warning of a cast.
#[derive(Clone, PartialEq)]
pub struct CastWarn {
    /// The location where the cast occurs.
    pub loc: LocLineInfo,
    /// The reason why the cast is warned.
    pub reason: CastReason,
    /// The message.
    pub msg: CastWarnMsg,
}

impl fmt::Debug for CastWarn {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:?}: {:?}: {:?}", self.loc, self.reason, self.msg)
    }
}

impl fmt::Display for CastWarn {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}: {}: {}", self.loc, self.reason, self.msg)
    }
}

/// A warning in structural type checking.
#[derive(Clone, PartialEq)]
pub struct TypeWarn {
    /// The location of the warning.
    pub loc: LocLineInfo,
    /// The instruction which causes the warning.
    pub insn: Option<Insn<ExtIdent>>,
    /// The constraint indicating the reason of the warning.
    pub reason: Constr,
}

impl fmt::Debug for TypeWarn {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:?}: ", self.loc)?;
        if let Some(insn) = &self.insn {
            write!(f, "{}: ", insn)?;
        }
        write!(f, "{}", self.reason)
    }
}

impl fmt::Display for TypeWarn {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut reason = self.reason.clone();
        reason.dummy();
        write!(f, "{}: {}", self.loc, reason)
    }
}

/// A summary of the [`TypeChkReport::castwarns`].
#[derive(Clone, Debug, PartialEq)]
pub struct CastWarnSummary {
    /// The number of the all warnings.
    total: usize,
    /// The number of the all warnings indicating an unsafe cast.
    nunsafes: usize,
}

impl fmt::Display for CastWarnSummary {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} possibly unsafe cast(s) found ({} analyzed)",
            self.nunsafes, self.total,
        )
    }
}

/// A summary of the [`TypeChkReport::typewarns`].
#[derive(Clone, Debug, PartialEq)]
pub struct TypeWarnSummary {
    /// The number of the all warnings.
    pub total: usize,
    /// The histogram on the kind of the constraint of the warnings.
    pub kindhist: BTreeMap<ConstrKind, usize>,
}

impl fmt::Display for TypeWarnSummary {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{} warning(s) found: ", self.total)?;
        for (i, (kind, n)) in self.kindhist.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}={}", kind, n)?;
        }
        Ok(())
    }
}

/// A report generated by [`TypeChk`].
#[derive(Clone, Debug, PartialEq)]
pub struct TypeChkReport {
    /// The warnings related to casts.
    pub castwarns: Vec<CastWarn>,
    /// The warnings in structural type checking.
    pub typewarns: Vec<TypeWarn>,
}

impl TypeChkReport {
    /// Returns a summary of [`TypeChkReport::castwarns`].
    pub fn summarize_castwarns(&self) -> CastWarnSummary {
        let mut nunsafes = 0;
        for warn in &self.castwarns {
            if !warn.msg.is_valid() {
                nunsafes += 1;
            }
        }
        CastWarnSummary {
            total: self.castwarns.len(),
            nunsafes,
        }
    }
    /// Returns a summary of [`TypeChkReport::typewarns`].
    pub fn summarize_typewarns(&self) -> TypeWarnSummary {
        let mut total = 0;
        let mut kindhist = BTreeMap::new();
        for warn in &self.typewarns {
            *kindhist.entry(warn.reason.kind()).or_insert(0) += 1;
            total += 1;
        }
        TypeWarnSummary { total, kindhist }
    }
}
