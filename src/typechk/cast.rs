//! The casting analysis module.

use crate::annot::syntax::{ApplyRefiner, CastMatchCase, VarMap};
use crate::annot::AnnotFile;
use crate::fmt::DisplayIter;
use crate::llir::abi::{AffineExpr, GetelementptrResult};
use crate::llir::interp::rtti::{ExtIdent, ExtName};
use crate::llir::syntax::{
    BinOpArgs, BinOpcode, CallBody, Callee, CmpOpArgs, CmpOpcode, ConvOpArgs, GlobalIdent,
    IcmpCond, Insn, Label, Loc, LocalIdent, Module, Type as LLIRType, TypedValue, Value,
};
use crate::ops::TotallyComparable;
use crate::solver::bitfield::BitFieldSet;
use crate::solver::syntax::{Cond, CondConst, CondExpr, CondPred};
use crate::solver::Solver;
use crate::symbol::Ident;
use crate::typechk::env::TypeEnv;
use crate::typechk::syntax::{
    CastReason, CastReasonKind, Effect, EffectKind, PtrExtIdent, Type, VarName,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A base pointer of [`FieldVar`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldVarBase {
    /// The flag indicating whether the variable is dereferenced or not.
    pub derefed: bool,
    /// The name of the variable.
    pub name: LocalIdent,
}

impl fmt::Display for FieldVarBase {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.derefed {
            true => write!(f, "&(*{})", self.name),
            false => write!(f, "&{}", self.name),
        }
    }
}

/// A field variable.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldVar {
    /// The base pointer.
    pub base: FieldVarBase,
    /// The index from the base pointer.
    pub index: AffineExpr<ExtIdent>,
    /// The offset from the index.
    pub offset: AffineExpr<ExtIdent>,
}

impl FieldVar {
    /// Returns a new field variable indicating the local variable is the base.
    pub fn new(name: LocalIdent) -> FieldVar {
        FieldVar {
            base: FieldVarBase {
                derefed: false,
                name,
            },
            index: AffineExpr::new(0),
            offset: AffineExpr::new(0),
        }
    }
    /// Returns the type of the base variable.
    pub fn basety<'a>(&self, loc: &Loc, env: &'a TypeEnv) -> Option<&'a Type> {
        let ty = env.var(&VarName::Local(self.base.name, loc.func)).ok()?;
        match ty {
            Type::Ptr(_, ty) => match self.base.derefed {
                true => match ty.as_ref() {
                    Type::Ptr(_, ty) => Some(ty),
                    _ => None,
                },
                false => Some(ty),
            },
            _ => None,
        }
    }
}

impl fmt::Display for FieldVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}[{}][{}]", self.base, self.index, self.offset)
    }
}

/// A state of identifying a target pointer.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TargetState {
    /// Indicating that the target is unknown.
    Unknown,
    /// Indicating that the target is being identified.
    Search(ExtIdent),
    /// Indicating that the target is identified as the base.
    Base(ExtIdent),
}

impl TargetState {
    /// Returns the identifier of the target pointer.
    pub fn id(&self) -> Option<Ident> {
        match self {
            TargetState::Search(ident) | TargetState::Base(ident) => Some(ident.name.id()),
            _ => None,
        }
    }
    /// Returns `true` if on [`TargetState::Base`].
    pub fn is_base_ident(&self) -> bool {
        matches!(self, TargetState::Base(_))
    }
}

impl fmt::Display for TargetState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TargetState::Unknown => write!(f, "!??"),
            TargetState::Search(ident) => write!(f, "{}", ident),
            TargetState::Base(ident) => write!(f, "base:{}", ident),
        }
    }
}

/// A state of identifying the pointer of a variable.
#[derive(Clone, Debug, PartialEq)]
pub enum VarState {
    /// Starting from the cast with the kind as the pointer type of the refinement type at the location.
    StartFrom(CastReasonKind, PtrExtIdent, Loc),
    /// Searching the target pointer from the cast with the kind as the pointer type of the refinement type at the location.
    Targetptr(CastReasonKind, TargetState, FieldVar, Loc),
    /// Identified the base pointer of the refinement type at the location.
    Baseptr(ExtIdent, FieldVar, Loc),
    /// Dereferencing the pointer.
    Deref(Box<VarState>),
    /// Logically shift the variable to the left.
    LShift(Box<VarState>, i64),
    /// Hit the source of the another cast at the location.
    HitCastSource(CastReasonKind, PtrExtIdent, FieldVar, Loc),
    /// Hit the side effect on the state at the location.
    HitSideEffect(Box<VarState>, Loc),
    /// Failed on the state at the location.
    Failed(Box<VarState>, Loc),
}

impl VarState {
    /// Returns the extension identifier of the base pointer if identified it.
    pub fn ident(&self) -> Option<ExtIdent> {
        match self {
            VarState::Baseptr(ident, _, _) => Some(*ident),
            _ => None,
        }
    }
    /// Returns the base pointer if identified it.
    pub fn baseptr(&self) -> Option<&FieldVar> {
        match self {
            VarState::Baseptr(_, fp, _) => Some(fp),
            _ => None,
        }
    }
    /// Returns a base pointer rebased by the offset of the field with the refinement type.
    pub fn rebased_baseptr(&self) -> Option<FieldVar> {
        let mut fp = self.baseptr()?.clone();
        let ident = self.ident()?;
        let offset = match ident.name.is_restrict_base() {
            true => 0,
            false => ident.offset,
        };
        fp.offset.add_const(-offset);
        Some(fp)
    }
    fn fail(&mut self, loc: &Loc) {
        *self = VarState::Failed(Box::new(self.clone()), *loc)
    }
    /// Updates the state with the instruction at the location under the effect and the typing environment.
    pub fn update(
        &mut self,
        insn: &Insn<ExtIdent>,
        effect: &Effect,
        loc: &Loc,
        env: &TypeEnv,
    ) -> Result<bool, String> {
        match self {
            VarState::StartFrom(castkind, peid, loc0) => {
                if let Some(res) = insn.res() {
                    let ty = env.var(&VarName::Local(res, loc.func))?;
                    if let Some((res_peid, _)) = ty.try_to_ptr_ext_ident(env) {
                        if &res_peid == peid {
                            let target = TargetState::Base(peid.ident());
                            let fp = FieldVar::new(res);
                            *self = VarState::Targetptr(*castkind, target, fp, *loc0);
                            return self.update(insn, effect, loc, env);
                        }
                    }
                }
            }
            VarState::Targetptr(castkind, target, fp, loc0) => match insn {
                Insn::Alloca { res, .. } if res == &fp.base.name => match target {
                    TargetState::Base(ident) | TargetState::Search(ident) => {
                        let mut fp = fp.clone();
                        fp.base = FieldVarBase {
                            derefed: false,
                            name: *res,
                        };
                        *self = VarState::Baseptr(*ident, fp, *loc0);
                    }
                    _ => self.fail(loc),
                },
                Insn::Load { res, src, .. } if res == &fp.base.name => {
                    if let Some(base) = src.1.local_base() {
                        let ty = env.var(&VarName::Local(base, loc.func))?;
                        if env.judge_effect_modifies_ptr(effect, ty, loc0) {
                            *self = VarState::HitSideEffect(Box::new(self.clone()), *loc);
                            return Ok(true);
                        }
                        let mut fp = fp.clone();
                        fp.base = FieldVarBase {
                            derefed: true,
                            name: base,
                        };
                        let newident = if let Some((peid, _)) = ty.try_to_ptr_ext_ident(env) {
                            if peid.ident().name.is_restrict_base() {
                                *self = VarState::Baseptr(peid.ident(), fp, *loc0);
                                return Ok(false);
                            } else if target.id().is_none()
                                || Some(peid.ident().name.id()) == target.id()
                            {
                                Some(peid.ident())
                            } else if castkind == &CastReasonKind::Downcast {
                                *self =
                                    VarState::HitCastSource(CastReasonKind::Load, peid, fp, *loc);
                                return Ok(true);
                            } else {
                                None
                            }
                        } else {
                            match target {
                                TargetState::Base(ident) | TargetState::Search(ident)
                                    if ident.name.is_restrict_base() =>
                                {
                                    *self = VarState::Baseptr(*ident, fp, *loc0);
                                    return Ok(false);
                                }
                                _ => None,
                            }
                        };
                        *self = match newident {
                            Some(newident) => {
                                let ptr = match fp.index == AffineExpr::new(0) {
                                    true => VarState::Targetptr(
                                        match castkind {
                                            CastReasonKind::Downcast => CastReasonKind::Load,
                                            _ => *castkind,
                                        },
                                        TargetState::Search(newident),
                                        fp,
                                        *loc0,
                                    ),
                                    false => VarState::Baseptr(newident, fp, *loc0),
                                };
                                VarState::Deref(Box::new(ptr))
                            }
                            None => match target {
                                TargetState::Unknown => {
                                    VarState::Targetptr(*castkind, TargetState::Unknown, fp, *loc0)
                                }
                                TargetState::Base(ident) | TargetState::Search(ident) => {
                                    VarState::Baseptr(*ident, fp, *loc0)
                                }
                            },
                        };
                    }
                }
                Insn::Value(res, Value::ConvOp(args)) if res == &fp.base.name => {
                    let ConvOpArgs {
                        srctyval: TypedValue(_, srcval),
                        ..
                    } = args.as_ref();
                    if let Some(base) = srcval.local_base() {
                        let mut fp = fp.clone();
                        fp.base = FieldVarBase {
                            derefed: false,
                            name: base,
                        };
                        *self = VarState::Targetptr(*castkind, *target, fp, *loc0);
                    }
                }
                Insn::Value(res, Value::Getelementptr(args)) if res == &fp.base.name => {
                    if let Some(base) = args.base_ptr.1.local_base() {
                        let ty = env.var(&VarName::Local(*res, loc.func))?;
                        let GetelementptrResult {
                            index: i,
                            offset: mut o,
                            ..
                        } = env.datalayout().getelementptr(args, env.typedefs())?;
                        o.add(&fp.offset);
                        o.add(&fp.index);
                        let fp = FieldVar {
                            base: FieldVarBase {
                                derefed: false,
                                name: base,
                            },
                            index: i,
                            offset: o,
                        };
                        let (target, shift) = match ty.try_to_ptr_ext_ident(env) {
                            Some((peid, _)) => {
                                let delta = match fp.offset.try_to_i64() {
                                    Some(offset) => offset - peid.ident().offset,
                                    None => 0,
                                };
                                if target == &TargetState::Unknown {
                                    (TargetState::Search(peid.ident()), delta * 8)
                                } else if target.is_base_ident()
                                    && peid.ident().name.is_restrict_base()
                                {
                                    (TargetState::Base(peid.ident()), 0)
                                } else {
                                    (*target, 0)
                                }
                            }
                            None => (*target, 0),
                        };
                        *self = VarState::Targetptr(*castkind, target, fp, *loc0);
                        if shift > 0 {
                            *self = VarState::LShift(Box::new(self.clone()), shift);
                        }
                        return Ok(false);
                    }
                    self.fail(loc);
                }
                _ if insn.res() == Some(fp.base.name) => self.fail(loc),
                _ => {}
            },
            VarState::Deref(state) | VarState::LShift(state, _) => {
                return state.update(insn, effect, loc, env);
            }
            VarState::Baseptr(..)
            | VarState::HitCastSource(..)
            | VarState::HitSideEffect(..)
            | VarState::Failed(..) => {}
        }
        Ok(false)
    }
    /// Returns a extracted expression in the condition.
    pub fn try_to_cond_expr(&self, varmap: &mut VarMap<FieldVar>) -> Option<CondExpr> {
        match self {
            VarState::Deref(state) => match state.try_to_cond_expr(varmap)? {
                CondExpr::Var(var) => Some(CondExpr::Deref(var)),
                _ => None,
            },
            VarState::LShift(state, n) if *n >= 0 => {
                let expr = state.try_to_cond_expr(varmap)?;
                Some(CondExpr::Bitlshr(Box::new(expr), CondConst::U64(*n as u64)))
            }
            _ => match self.ident() {
                Some(ident) => Some(CondExpr::Var(
                    varmap.var(&self.rebased_baseptr()?, &ident.name),
                )),
                _ => None,
            },
        }
    }
}

impl fmt::Display for VarState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            VarState::StartFrom(castkind, peid, loc) => {
                write!(f, "start-from({:?}, {}){}", castkind, peid, loc)
            }
            VarState::Targetptr(castkind, target, fp, loc) => {
                write!(f, "targetptr({:?}, {}, {}){}", castkind, target, fp, loc)
            }
            VarState::Baseptr(eid, fp, loc) => write!(f, "baseptr({}, {}){}", eid, fp, loc),
            VarState::Deref(state) => write!(f, "deref({})", state),
            VarState::LShift(state, n) => write!(f, "lshift({}, {})", state, n),
            VarState::HitCastSource(castkind, peid, fp, loc) => write!(
                f,
                "hit-cast-source({:?}, {}, {}){}",
                castkind, peid, fp, loc
            ),
            VarState::HitSideEffect(state, loc) => write!(f, "hit-side-effect({}){}", state, loc),
            VarState::Failed(state, loc) => write!(f, "failed({}){}", state, loc),
        }
    }
}

/// A (dereferenced) value.
#[derive(Clone, Debug, PartialEq)]
pub struct DerefValue<'a> {
    /// Indicating whether the value is dereferenced or not.
    pub derefed: bool,
    /// The value.
    pub value: &'a Value<ExtIdent>,
}

impl<'a> DerefValue<'a> {
    /// Returns a pair of the source and destination (dereferenced) value of the store from the instruction.
    pub fn store_srcdst(insn: &Insn<ExtIdent>) -> Option<(DerefValue, DerefValue)> {
        match insn {
            Insn::Call {
                res,
                body:
                    CallBody {
                        callee:
                            Callee::Value(Value::GlobalRef(global_ident!("llvm.memcpy.p0i8.p0i8.i64"))),
                        args,
                        ..
                    },
                ..
            } if res.is_none() && args.len() == 4 => Some((
                DerefValue {
                    derefed: true,
                    value: &args[1].1,
                },
                DerefValue {
                    derefed: true,
                    value: &args[0].1,
                },
            )),
            Insn::Store { src, dst, .. } => Some((
                DerefValue {
                    derefed: false,
                    value: &src.1,
                },
                DerefValue {
                    derefed: true,
                    value: &dst.1,
                },
            )),
            _ => None,
        }
    }
}

/// A result of [`CondState::Store`].
#[derive(Clone, Debug, PartialEq)]
pub struct StoreResult<'a> {
    /// The location.
    pub loc: &'a Loc,
    /// The destination pointer.
    pub ptr: &'a PtrExtIdent,
    /// The type of a stored value.
    pub ty: &'a LLIRType<ExtIdent>,
    /// The state of the source operand.
    pub srcstate: Option<&'a VarState>,
    /// The extension identifier of the destination operand.
    pub dsteid: ExtIdent,
}

/// A state of extracting a condition.
#[derive(Clone, Debug, PartialEq)]
pub enum CondState {
    /// Searching an branch instruction to the block.
    SearchBrTo(Option<Label>),
    /// Searching an store instruction to a value of the refinement type.
    SearchStoreTo(ExtIdent),
    /// Extracting a (optionally negated) condition assigned to the variable.
    CondVar { negated: bool, var: LocalIdent },
    /// Storing a value with the type to the pointer with the refinement type at the location.
    Store {
        loc: Loc,
        ptr: PtrExtIdent,
        ty: LLIRType<ExtIdent>,
        src: Box<CondState>,
        dst: Box<CondState>,
    },
    /// Applying the binary operation.
    BinOp {
        opcode: BinOpcode,
        left: Box<CondState>,
        right: Box<CondState>,
    },
    /// Applying the comparison operation.
    CmpOp {
        opcode: CmpOpcode,
        left: Box<CondState>,
        right: Box<CondState>,
    },
    /// A constant `n`-bit integer (`n <= 64`).
    ConstInt(usize, i64),
    /// Dereferencing a value of the condition.
    Deref(Box<CondState>),
    /// Tracing the target variable.
    Var(TargetState, LocalIdent),
    /// A state of tracing the variable.
    VarState(VarState),
    /// Detected unknown value at the location.
    UnknownValue(Value<ExtIdent>, Loc),
    /// Failed on the state at the location.
    Failed(Box<CondState>, Loc),
}

impl CondState {
    /// Returns a new state for a variable or a value.
    pub fn from_value(target: TargetState, base: DerefValue, loc: &Loc) -> CondState {
        let state = match base.value {
            Value::I8(n) => CondState::ConstInt(8, *n as i64),
            Value::I16(n) => CondState::ConstInt(16, *n as i64),
            Value::I32(n) => CondState::ConstInt(32, *n as i64),
            Value::I64(n) => CondState::ConstInt(64, *n as i64),
            val => match val.local_base() {
                Some(base) => CondState::Var(target, base),
                None => return CondState::UnknownValue(val.clone(), *loc),
            },
        };
        match base.derefed {
            true => CondState::Deref(Box::new(state)),
            false => state,
        }
    }
    /// Returns the contained [`VarState`].
    pub fn varstate(&self) -> Option<&VarState> {
        match self {
            CondState::VarState(state) => Some(state),
            CondState::Deref(ptr) => ptr.varstate(),
            _ => None,
        }
    }
    /// Returns `true` if the state is valid store.
    pub fn is_invalid_store(&self, env: &TypeEnv) -> bool {
        if let CondState::Store { loc, ptr, dst, .. } = self {
            let dst = match dst.varstate() {
                Some(state) => state,
                None => return false,
            };
            let dstbaseptr = match dst.rebased_baseptr() {
                Some(ptr) => ptr,
                None => return false,
            };
            let dstbasety = match dstbaseptr.basety(loc, env) {
                Some(ty) => ty,
                None => return false,
            };
            if let Some(dstbaseeid) = dstbasety.try_to_ext_ident(env) {
                match (ptr.ident().name, dstbaseeid.name) {
                    (ExtName::DowncastTag(id1, _), ExtName::DowncastSubtarget(id2, _))
                        if id1 == id2 => {}
                    (ExtName::DowncastTag(..), _) => return true,
                    _ => {}
                }
            }
            return false;
        }
        false
    }
    /// Returns the result of the store on the given base variable with the rebase offset.
    pub fn try_to_store_on(&self, base: LocalIdent, rebaseoff: i64) -> Option<StoreResult> {
        if let CondState::Store {
            loc,
            ptr,
            ty,
            src,
            dst,
        } = self
        {
            let dst = dst.varstate()?;
            let dstbaseptr = dst.rebased_baseptr()?;
            if let Some(o) = dstbaseptr.offset.try_to_i64() {
                if o < rebaseoff {
                    return None;
                }
            }
            if dstbaseptr.base.name == base {
                return Some(StoreResult {
                    loc,
                    ptr,
                    ty,
                    srcstate: src.varstate(),
                    dsteid: dst.ident()?,
                });
            }
        }
        None
    }
    fn fail(&mut self, loc: &Loc) {
        *self = CondState::Failed(Box::new(self.clone()), *loc)
    }
    fn update_start_store(
        &mut self,
        ident: ExtIdent,
        insn: &Insn<ExtIdent>,
        effect: &Effect,
        loc: &Loc,
        env: &TypeEnv,
    ) -> Option<()> {
        let insn_effect = env.effect(loc)?;
        let store_effect = insn_effect.try_to_store(loc, env)?;
        if env.judge_effect_modifies(effect, store_effect.dst, loc) {
            return None;
        }
        if store_effect.dst.try_to_ext_ident(env)? != ident {
            return None;
        }
        let src = store_effect.src.normalize(env).ok()?;
        let ty = src.try_to_llir_type()?;
        let srcident = match src.try_to_ext_ident(env) {
            Some(ident) => TargetState::Search(ident),
            None => TargetState::Unknown,
        };
        let dstident = TargetState::Search(ident);
        let (srcval, dstval) = DerefValue::store_srcdst(insn)?;
        let src = CondState::from_value(srcident, srcval, loc);
        let dst = CondState::from_value(dstident, dstval, loc);
        let ptr = PtrExtIdent::new(store_effect.dstvar, ident);
        *self = CondState::Store {
            loc: *loc,
            ptr,
            ty,
            src: Box::new(src),
            dst: Box::new(dst),
        };
        Some(())
    }
    /// Updates the state with the instruction at the location under the effect and the typing environment.
    pub fn update(
        &mut self,
        insn: &Insn<ExtIdent>,
        effect: &Effect,
        loc: &Loc,
        env: &TypeEnv,
    ) -> Result<bool, String> {
        match self {
            CondState::SearchBrTo(nextblock) => match insn {
                Insn::BrI1(val, label1, label0) => {
                    if let Some(var) = val.local_base() {
                        let negated = match nextblock {
                            Some(name) if name == label1 => false,
                            Some(name) if name == label0 => true,
                            _ => return Ok(false),
                        };
                        *self = CondState::CondVar { negated, var };
                    }
                }
                Insn::Switch(TypedValue(_, left), _, cases) => {
                    // TODO: Support default branch.
                    for (TypedValue(_, right), label) in cases {
                        if Some(label) == nextblock.as_ref() {
                            let opcode = CmpOpcode::Icmp(IcmpCond::Eq);
                            let left = CondState::from_value(
                                TargetState::Unknown,
                                DerefValue {
                                    derefed: false,
                                    value: left,
                                },
                                loc,
                            );
                            let right = CondState::from_value(
                                TargetState::Unknown,
                                DerefValue {
                                    derefed: false,
                                    value: right,
                                },
                                loc,
                            );
                            *self = CondState::CmpOp {
                                opcode,
                                left: Box::new(left),
                                right: Box::new(right),
                            };
                            return Ok(false);
                        }
                    }
                }
                _ => {}
            },
            CondState::SearchStoreTo(eid) => {
                let eid = *eid;
                if self
                    .update_start_store(eid, insn, effect, loc, env)
                    .is_none()
                {
                    self.fail(loc);
                }
            }
            CondState::CondVar { negated, var } => match insn {
                Insn::Value(res, Value::CmpOp(args)) if res == var => match args.as_ref() {
                    CmpOpArgs {
                        opcode: CmpOpcode::Icmp(cond),
                        left: TypedValue(_, left),
                        right: TypedValue(_, right),
                    } => {
                        let opcode = CmpOpcode::Icmp(match negated {
                            true => cond.negate(),
                            false => *cond,
                        });
                        let left = CondState::from_value(
                            TargetState::Unknown,
                            DerefValue {
                                derefed: false,
                                value: left,
                            },
                            loc,
                        );
                        let right = CondState::from_value(
                            TargetState::Unknown,
                            DerefValue {
                                derefed: false,
                                value: right,
                            },
                            loc,
                        );
                        *self = CondState::CmpOp {
                            opcode,
                            left: Box::new(left),
                            right: Box::new(right),
                        };
                    }
                    _ if res == var => self.fail(loc),
                    _ => {}
                },
                _ if insn.res() == Some(*var) => self.fail(loc),
                _ => {}
            },
            CondState::Store { loc, src, dst, .. } => {
                if src.update(insn, effect, loc, env)? || dst.update(insn, effect, loc, env)? {
                    return Ok(true);
                }
            }
            CondState::BinOp { left, right, .. } | CondState::CmpOp { left, right, .. } => {
                if left.update(insn, effect, loc, env)? || right.update(insn, effect, loc, env)? {
                    return Ok(true);
                }
            }
            CondState::Deref(state) => return state.update(insn, effect, loc, env),
            CondState::Var(target, name) => match insn {
                Insn::Value(res, Value::BinOp(args)) if res == name => {
                    let BinOpArgs {
                        opcode,
                        left: TypedValue(_, left),
                        right: TypedValue(_, right),
                    } = args.as_ref();
                    let left = CondState::from_value(
                        *target,
                        DerefValue {
                            derefed: false,
                            value: left,
                        },
                        loc,
                    );
                    let right = CondState::from_value(
                        *target,
                        DerefValue {
                            derefed: false,
                            value: right,
                        },
                        loc,
                    );
                    *self = CondState::BinOp {
                        opcode: *opcode,
                        left: Box::new(left),
                        right: Box::new(right),
                    };
                }
                _ if insn.res() == Some(*name) => {
                    *self = CondState::VarState(VarState::Targetptr(
                        CastReasonKind::Load,
                        *target,
                        FieldVar::new(*name),
                        *loc,
                    ));
                    return self.update(insn, effect, loc, env);
                }
                _ => {}
            },
            CondState::VarState(state) => return state.update(insn, effect, loc, env),
            CondState::ConstInt(..) | CondState::UnknownValue(..) | CondState::Failed(..) => {}
        }
        Ok(false)
    }
    /// Returns an extracted constant in the expression in the condition.
    pub fn try_to_cond_const(&self) -> Option<CondConst> {
        match self {
            CondState::ConstInt(n, x) if *n <= 64 => Some(CondConst::U64(*x as u64)),
            _ => None,
        }
    }
    /// Returns an extracted expression in the condition.
    pub fn try_to_cond_expr(&self, varmap: &mut VarMap<FieldVar>) -> Option<CondExpr> {
        match self {
            CondState::BinOp {
                opcode,
                left,
                right,
            } => {
                let left = Box::new(left.try_to_cond_expr(varmap)?);
                let right = right.try_to_cond_const()?;
                match opcode {
                    BinOpcode::And => Some(CondExpr::Bitand(left, right)),
                    BinOpcode::Lshr(_) => Some(CondExpr::Bitlshr(left, right)),
                    _ => None,
                }
            }
            CondState::Deref(state) => match state.try_to_cond_expr(varmap)? {
                CondExpr::Var(ptr) => Some(CondExpr::Deref(ptr)),
                _ => None,
            },
            CondState::VarState(state) => state.try_to_cond_expr(varmap),
            _ => Some(CondExpr::Const(self.try_to_cond_const()?)),
        }
    }
    /// Returns an extracted condition.
    pub fn to_cond(&self, varmap: &mut VarMap<FieldVar>) -> Cond {
        match self {
            CondState::Store { src, dst, .. } => {
                let left = match src.try_to_cond_expr(varmap) {
                    Some(expr) => expr,
                    None => return Cond::top(),
                };
                let right = match dst.try_to_cond_expr(varmap) {
                    Some(expr) => expr,
                    None => return Cond::top(),
                };
                Cond::And(vec![CondPred::Eq(left, right)])
            }
            CondState::CmpOp {
                opcode: CmpOpcode::Icmp(cond),
                left,
                right,
            } => {
                let left = match left.try_to_cond_expr(varmap) {
                    Some(expr) => expr,
                    None => return Cond::top(),
                };
                let right = match right.try_to_cond_expr(varmap) {
                    Some(expr) => expr,
                    None => return Cond::top(),
                };
                let pred = match cond {
                    IcmpCond::Eq => CondPred::Eq(left, right),
                    IcmpCond::Ne => CondPred::Neq(left, right),
                    _ => return Cond::top(),
                };
                Cond::And(vec![pred])
            }
            _ => Cond::top(),
        }
    }
}

impl fmt::Display for CondState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CondState::SearchBrTo(nextblock) => {
                write!(f, "search-br-to(")?;
                match nextblock {
                    Some(name) => write!(f, "{}", name.localident())?,
                    None => write!(f, "none")?,
                }
                write!(f, ")")
            }
            CondState::SearchStoreTo(eid) => write!(f, "search-store-to({})", eid),
            CondState::CondVar { negated, var } => {
                if *negated {
                    write!(f, "!")?;
                }
                write!(f, "cond-var({})", var)
            }
            CondState::Store {
                loc,
                ptr,
                ty,
                src,
                dst,
            } => {
                write!(f, "store{}({}, {}; {}, {})", loc, ptr, ty, src, dst)
            }
            CondState::BinOp {
                opcode,
                left,
                right,
            } => {
                let opcode = opcode.to_string().replace(" ", "-");
                write!(f, "{}({}, {})", opcode, left, right)
            }
            CondState::CmpOp {
                opcode,
                left,
                right,
            } => {
                let opcode = opcode.to_string().replace(" ", "-");
                write!(f, "{}({}, {})", opcode, left, right)
            }
            CondState::ConstInt(n, val) => write!(f, "const({}i{})", val, n),
            CondState::Deref(state) => write!(f, "deref({})", state),
            CondState::Var(target, name) => write!(f, "var({}, {})", target, name),
            CondState::VarState(state) => write!(f, "{}", state),
            CondState::UnknownValue(val, loc) => write!(f, "unknown-value({}){}", val, loc),
            CondState::Failed(state, loc) => write!(f, "failed({}){}", state, loc),
        }
    }
}

/// A kind of the cast checking.
#[derive(Clone, Debug, PartialEq)]
pub enum CastChkKind {
    /// Kind of casting as the LLIR type.
    CastAs(LLIRType<ExtIdent>),
    /// Kind of cast equality.
    Equality,
    /// Kind of detecting the judge kind.
    Unknown,
}

impl fmt::Display for CastChkKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CastChkKind::CastAs(ty) => write!(f, "verify cast as {}", ty),
            CastChkKind::Equality => write!(f, "verify cast equality"),
            CastChkKind::Unknown => write!(f, "detect judge kind"),
        }
    }
}

/// A state of [`Path`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PathState {
    /// Indicating that the path is extending.
    Extending,
    /// Indicating that the path hit a branch.
    HitBranch,
    /// Indicating that the path is escaped.
    Escaped,
}

/// A path that is the list of the locations.
#[derive(Clone, Debug, PartialEq)]
pub struct Path {
    locs: Vec<Loc>,
    state: PathState,
}

impl Path {
    /// Returns a path which has one location.
    pub fn unit(loc: Loc) -> Path {
        Path {
            locs: vec![loc],
            state: PathState::Extending,
        }
    }
    /// Returns the list of the locations.
    pub fn locs(&self) -> &[Loc] {
        &self.locs
    }
    /// Returns the state.
    pub fn state(&self) -> PathState {
        self.state
    }
    fn push(&mut self, loc: Loc) {
        self.locs.push(loc);
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "path[{}; {:?}]",
            DisplayIter("", self.locs.iter(), " -> ", ""),
            self.state
        )
    }
}

/// A state of [`CastChk`].
#[derive(Clone, Debug, PartialEq)]
pub struct CastChkState {
    cause_kind: CastReasonKind,
    cause: PtrExtIdent,
    loc: Loc,
    path: Path,
    effect: Effect,
    baseptr: VarState,
    conds: Vec<CondState>,
}

impl CastChkState {
    /// Returns a new state with the kind, causing pointer and the location.
    pub fn new(cause_kind: CastReasonKind, cause: PtrExtIdent, loc: Loc) -> CastChkState {
        CastChkState {
            cause_kind,
            cause,
            loc,
            path: Path::unit(loc),
            effect: Effect::empty(),
            baseptr: VarState::StartFrom(cause_kind, cause, loc),
            conds: Vec::new(),
        }
    }
    /// Returns the path.
    pub fn path(&self) -> &Path {
        &self.path
    }
    /// Returns the effect.
    pub fn effect(&self) -> &Effect {
        &self.effect
    }
    /// Returns the state of tracking the base pointer.
    pub fn baseptr(&self) -> &VarState {
        &self.baseptr
    }
    /// Returns the states of tracking the condition.
    pub fn conds(&self) -> &[CondState] {
        &self.conds
    }
    fn check_insn(
        &mut self,
        insn: &Insn<ExtIdent>,
        loc: &Loc,
        env: &TypeEnv,
    ) -> Result<bool, String> {
        if let Some(effect) = env.effect(loc) {
            if let Some(store_effect) = effect.try_to_store(loc, env) {
                if let Some(eid) = store_effect.dst.try_to_ext_ident(env) {
                    if eid.name.id() == self.cause.ident().name.id() {
                        self.conds.push(CondState::SearchStoreTo(eid));
                    }
                }
            }
        }
        if self.baseptr.update(insn, &self.effect, loc, env)? {
            return Ok(true);
        }
        for cond in &mut self.conds {
            if cond.update(insn, &self.effect, loc, env)? {
                return Ok(true);
            }
        }
        if let Some(insn_effect) = env.effect(loc) {
            for (effkind, effloc) in insn_effect.iter() {
                let will_push = match effkind {
                    // The location is just before the following insn is executed.
                    EffectKind::CallGlobal(_) | EffectKind::CallIndirect => loc != &self.loc,
                    _ => true,
                };
                if will_push {
                    self.effect.push(effkind.clone(), *effloc);
                }
            }
        }
        Ok(false)
    }
    /// Starts the automaton under the typing environment and the LLIR module.
    pub fn start(&mut self, env: &TypeEnv, module: &Module<ExtIdent>) -> Result<(), String> {
        let mut loc = self.loc;
        let blocks = match module.func(&loc.func) {
            Some((_, blocks)) => blocks,
            None => return Err(format!("cannot find function {}", loc.func)),
        };
        let mut block = blocks.block(&loc.block).unwrap();
        let mut next_blockname = None;
        loop {
            self.conds.push(CondState::SearchBrTo(next_blockname));
            while loc.insnidx >= 1 {
                if self.check_insn(&block.insns[loc.insnidx - 1], &loc, env)? {
                    self.path.push(loc);
                    self.path.state = PathState::Escaped;
                    return Ok(());
                }
                loc.insnidx -= 1;
            }
            if block.preds.len() != 1 {
                self.path.push(loc);
                self.path.state = PathState::HitBranch;
                return Ok(());
            }
            next_blockname = Some(loc.block);
            block = blocks.block(&block.preds[0]).unwrap();
            loc.block = block.name;
            loc.insnidx = block.insns.len();
            self.path.push(loc);
        }
    }
}

impl fmt::Display for CastChkState {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} with {} ==> {}; {}",
            self.path(),
            self.effect(),
            self.baseptr(),
            DisplayIter("", self.conds().iter(), " and ", "")
        )
    }
}

/// A cast checker.
pub struct CastChk {
    target: Option<LLIRType<ExtIdent>>,
    state: CastChkState,
    ctx: Cond,
    matched_cond: Option<Cond>,
    srcs: Vec<(Loc, PtrExtIdent)>,
    chk_kind: CastChkKind,
}

impl CastChk {
    fn new(
        cause_kind: CastReasonKind,
        cause: PtrExtIdent,
        target: Option<LLIRType<ExtIdent>>,
        loc: Loc,
    ) -> CastChk {
        CastChk {
            target,
            state: CastChkState::new(cause_kind, cause, loc),
            ctx: Cond::top(),
            matched_cond: None,
            srcs: Vec::new(),
            chk_kind: CastChkKind::Unknown,
        }
    }
    /// Returns a new cast checker from the cast reason and the location.
    pub fn from_cast_reason(reason: &CastReason, loc: &Loc) -> CastChk {
        let (cause, target) = match reason {
            CastReason::Downcast(peid, target)
            | CastReason::Load(target, peid)
            | CastReason::Store(target, peid) => (*peid, Some(target.clone())),
            CastReason::Memcpy(peid, _, _) => (*peid, None),
        };
        CastChk::new(reason.kind(), cause, target, *loc)
    }
    /// Check the validity of the annotation file under the typing environment.
    pub fn check_annot_file_validity(annotfile: &AnnotFile, env: &TypeEnv) -> Result<(), String> {
        let loc = Loc::new(GlobalIdent::from(""), Label::from(LocalIdent::from("")), 0);
        for refiner in annotfile.refiners().values() {
            let cases = refiner.enum_cases(annotfile)?;
            for i in 0..cases.len() {
                let casei = &cases[i];
                for casej in cases.iter().skip(i + 1) {
                    if !(CastChk::judge_cast(casei.target(), casej.target(), &loc, env)
                        .unwrap_or(true)
                        || CastChk::judge_cast(casej.target(), casei.target(), &loc, env)
                            .unwrap_or(true))
                    {
                        let solver = Solver::new();
                        let mut cond = casei.cond().clone();
                        cond.conjunct_any(casej.cond().clone());
                        if solver.satisfies_cond(&cond) {
                            return Err(format!(
                                "conflict case {} and case {} between incompatible types",
                                casei, casej
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// Judges the type cast at the location under the type environment by [`TypeEnv::judge_cast`].
    pub fn judge_cast(
        ty1: &LLIRType<ExtIdent>,
        ty2: &LLIRType<ExtIdent>,
        loc: &Loc,
        env: &TypeEnv,
    ) -> Result<bool, String> {
        let ty1 = env.intern_llir_type(ty1, loc)?;
        let ty2 = env.intern_llir_type(ty2, loc)?;
        env.judge_cast(&ty1, &ty2, true, loc, &mut None)
    }
    /// Judges the type cast at the location under the given `cast-match` and the condition under the type environment.
    pub fn judge_cast_match_target(
        cases: &[CastMatchCase],
        reason: CastReasonKind,
        cond: &Cond,
        target: &LLIRType<ExtIdent>,
        loc: &Loc,
        env: &TypeEnv,
    ) -> Option<Cond> {
        if cases.len() == 1 && !reason.is_store_tag() {
            return match target == cases[0].target() {
                true => Some(Cond::top()),
                false => None,
            };
        }
        let solver = Solver::new();
        if target == &LLIRType::Void {
            for case in cases {
                if target == case.target() && solver.entails_cond(cond, case.cond()) {
                    return Some(case.cond().clone());
                }
            }
            return None;
        }
        match reason {
            CastReasonKind::Store(_) => {
                let mut matched_cond = Cond::top();
                let mut hit = false;
                for case in cases {
                    if CastChk::judge_cast(target, case.target(), loc, env).unwrap_or(false)
                        || CastChk::judge_cast(case.target(), target, loc, env).unwrap_or(false)
                    {
                        if !solver.entails_cond(cond, case.cond()) {
                            return None;
                        }
                        hit = true;
                        matched_cond.conjunct_any(case.cond().clone());
                    }
                }
                if hit {
                    return Some(matched_cond);
                }
            }
            _ => {
                for case in cases {
                    if CastChk::judge_cast(case.target(), target, loc, env).unwrap_or(false)
                        && solver.entails_cond(cond, case.cond())
                    {
                        return Some(case.cond().clone());
                    }
                }
            }
        }
        None
    }
    /// Judges the equality of the condition under the given `cast-match` and `apply-refiner`.
    pub fn judge_cast_match_equality(
        refiner: &ApplyRefiner,
        cases: &[CastMatchCase],
        cond: &Cond,
    ) -> Option<Cond> {
        let solver = Solver::new();
        let mut bfset = BitFieldSet::empty();
        for case in cases {
            bfset.insert_cond(case.cond().clone());
        }
        let eqcond = bfset.gen_equation(refiner.varmap(&0).maxid() + 1)?;
        if solver.entails_cond(cond, &eqcond) {
            return Some(eqcond);
        }
        None
    }
    /// Returns the state.
    pub fn state(&self) -> &CastChkState {
        &self.state
    }
    /// Returns the context condition.
    pub fn ctx(&self) -> &Cond {
        &self.ctx
    }
    /// Returns the matched condition.
    pub fn matched_cond(&self) -> &Option<Cond> {
        &self.matched_cond
    }
    /// Returns the list of the source location and pointer extension identifier.
    pub fn srcs(&self) -> &[(Loc, PtrExtIdent)] {
        &self.srcs
    }
    /// Returns the kind.
    pub fn chk_kind(&self) -> &CastChkKind {
        &self.chk_kind
    }
    /// Runs the automaton under the annotation file, typing environment and LLIR module.
    pub fn run(
        mut self,
        annotfile: &AnnotFile,
        env: &TypeEnv,
        module: &Module<ExtIdent>,
    ) -> CastChkResult {
        if let Err(err) = self.state.start(env, module) {
            return self.into_result_collect_error(err);
        }
        if let VarState::HitCastSource(newcause_kind, newcause, _, loc) = &self.state.baseptr {
            let newcause = *newcause;
            let loc = *loc;
            let newtarget = self
                .target
                .as_ref()
                .map(|ty| LLIRType::Ptr(Box::new(ty.clone())));
            let castchk = CastChk::new(*newcause_kind, newcause, newtarget, loc);
            let res = castchk.run(annotfile, env, module);
            return self.into_result_merged(loc, newcause, res);
        }
        let (baseptr, baseptr_ident) = match self.state.baseptr.rebased_baseptr() {
            Some(baseptr) => (baseptr, self.state.baseptr.ident().unwrap()),
            None => {
                return self
                    .into_result_collect_error("failed to identify base pointer".to_string());
            }
        };
        let rebaseoff = if baseptr_ident.name.is_restrict_base() {
            baseptr_ident.offset
        } else {
            0
        };
        let baseappid = self.state.baseptr.ident().unwrap().appid;
        let basecmd = match annotfile.apply_refiner(baseappid) {
            Some(cmd) => cmd,
            None => {
                return self
                    .into_result_collect_error(format!("unknown apply-refiner @{}", baseappid));
            }
        };
        let cases = match annotfile.refiner(&basecmd.app().name()) {
            Some(refiner) => match refiner.enum_cases(annotfile) {
                Ok(cases) => cases,
                Err(err) => return self.into_result_collect_error(err),
            },
            None => {
                return self.into_result_collect_error(format!(
                    "unknown refiner !{}",
                    basecmd.app().name()
                ));
            }
        };
        let causeappid = self.state.cause.ident().appid;
        let causecmd = match annotfile.apply_refiner(causeappid) {
            Some(cmd) => cmd,
            None => {
                return self
                    .into_result_collect_error(format!("unknown apply-refiner @{}", causeappid));
            }
        };
        let mut varmap = causecmd.varmap(&baseptr);
        let (target, obaseptr) = match (self.state.cause.ident().name, &self.target) {
            (name, Some(_)) if name.is_any_target() => (self.target.clone(), None),
            _ => {
                let (mut target, mut obaseptr) = (None, None);
                for state in &self.state.conds {
                    if state.is_invalid_store(env) {
                        continue;
                    }
                    if let Some(StoreResult {
                        ty,
                        srcstate,
                        dsteid,
                        ..
                    }) = state.try_to_store_on(baseptr.base.name, rebaseoff)
                    {
                        if dsteid.name.id() == self.state.cause.ident().name.id()
                            && dsteid.name.is_any_target()
                        {
                            if let LLIRType::Ext(ident, _) = ty {
                                if ident.name.id() == self.state.cause.ident().name.id()
                                    && ident.name.is_any_target()
                                {
                                    if let Some(srcstate) = srcstate {
                                        if srcstate.ident().is_some() {
                                            obaseptr = srcstate.rebased_baseptr();
                                        }
                                    }
                                }
                            }
                            target = Some(ty.clone());
                            break;
                        }
                    }
                }
                if target.is_none() {
                    if self.state.cause.ident().name.is_downcast_subtarget() {
                        target = self.target.clone();
                    } else if self.state.cause.ident().name.is_downcast_tag() {
                        target = match baseptr.basety(&self.state.loc, env) {
                            Some(ty) => ty.try_to_llir_type(),
                            None => None,
                        };
                    }
                }
                (target, obaseptr)
            }
        };
        let target = match target {
            Some(target) => target,
            None => LLIRType::Void,
        };
        let check_equality = match obaseptr {
            Some(ptr) => {
                varmap.insert_dupvars(ptr);
                true
            }
            None => false,
        };
        for state in &self.state.conds {
            if state.is_invalid_store(env) {
                continue;
            }
            if let Some(StoreResult { loc, ptr, .. }) =
                state.try_to_store_on(baseptr.base.name, rebaseoff)
            {
                if loc.is_in_same_block(&self.state.loc) {
                    self.srcs.push((*loc, *ptr));
                }
            }
            self.ctx.conjunct_any(state.to_cond(&mut varmap));
        }
        if check_equality {
            self.matched_cond = CastChk::judge_cast_match_equality(causecmd, &cases, &self.ctx);
            self.chk_kind = CastChkKind::Equality;
        } else {
            self.matched_cond = CastChk::judge_cast_match_target(
                &cases,
                self.state.cause_kind,
                &self.ctx,
                &target,
                &self.state.loc,
                env,
            );
            self.chk_kind = CastChkKind::CastAs(target);
        }
        if self.matched_cond.is_none() {
            return self.into_result_failed();
        }
        self.into_result_success()
    }
    fn into_result_collect_error(self, msg: String) -> CastChkResult {
        CastChkResult {
            kind: CastChkResultKind::CollectError(msg),
            state: self.state,
            srcs: self.srcs,
        }
    }
    fn into_result_failed(self) -> CastChkResult {
        CastChkResult {
            kind: CastChkResultKind::Failed(self.chk_kind, self.ctx),
            state: self.state,
            srcs: self.srcs,
        }
    }
    fn into_result_success(self) -> CastChkResult {
        CastChkResult {
            kind: CastChkResultKind::Success(self.chk_kind, self.matched_cond.unwrap(), self.ctx),
            state: self.state,
            srcs: self.srcs,
        }
    }
    fn into_result_merged(
        mut self,
        loc: Loc,
        newcause: PtrExtIdent,
        mut res: CastChkResult,
    ) -> CastChkResult {
        if let CastChkResultKind::Success(_, matched_cond, ctx) = res.kind {
            self.srcs.append(&mut res.srcs);
            self.srcs.push((loc, newcause));
            return CastChkResult {
                kind: CastChkResultKind::Success(self.chk_kind, matched_cond, ctx),
                state: self.state,
                srcs: self.srcs,
            };
        }
        res
    }
}

/// A kind of [`CastChkKind`].
#[derive(Clone, Debug, PartialEq)]
pub enum CastChkResultKind {
    /// Indicating an error in collecting the condition.
    CollectError(String),
    /// Indicating a failure of checking cast under the collected condition.
    Failed(CastChkKind, Cond),
    /// Indicating a success of checking cast under the collected condition with the satisfied condition in a `cast-match`.
    Success(CastChkKind, Cond, Cond),
}

impl fmt::Display for CastChkResultKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CastChkResultKind::CollectError(msg) => write!(f, "{}", msg),
            CastChkResultKind::Failed(kind, ctx) => {
                write!(f, "failed to {} under context {}", kind, ctx)
            }
            CastChkResultKind::Success(kind, matched, ctx) => {
                write!(
                    f,
                    "succeeded to {} because satisfying {} under context {}",
                    kind, matched, ctx
                )
            }
        }
    }
}

/// A result of cast checking.
#[derive(Clone, Debug, PartialEq)]
pub struct CastChkResult {
    /// The kind of the result.
    pub kind: CastChkResultKind,
    /// The state of the cast checker.
    pub state: CastChkState,
    /// The list of the source location and pointer extension identifier.
    pub srcs: Vec<(Loc, PtrExtIdent)>,
}

/// A resolver of multiple results.
pub struct Resolver<I: TotallyComparable> {
    links: BTreeMap<(Loc, PtrExtIdent), Loc>,
    dstsets: BTreeMap<I, BTreeSet<Loc>>,
    results: BTreeMap<I, CastChkResult>,
}

impl<I: TotallyComparable> Resolver<I> {
    /// Returns a new resolver.
    pub fn new() -> Resolver<I> {
        Resolver {
            links: BTreeMap::new(),
            dstsets: BTreeMap::new(),
            results: BTreeMap::new(),
        }
    }
    /// Returns the destination set by identifier.
    pub fn dstset(&self, id: &I) -> Option<&BTreeSet<Loc>> {
        self.dstsets.get(id)
    }
    fn insert_dst(&mut self, id: I, dst: Loc) {
        if let Some(dstset) = self.dstsets.get_mut(&id) {
            dstset.insert(dst);
            return;
        }
        self.dstsets.insert(id, btree_set![dst]);
    }
    /// Returns the results.
    pub fn results(&self) -> &BTreeMap<I, CastChkResult> {
        &self.results
    }
    /// Imports the result at the location with the identifier.
    pub fn import_result(&mut self, id: I, res: CastChkResult, dst: Loc) {
        if let CastChkResultKind::Success(..) = res.kind {
            self.insert_dst(id.clone(), dst);
            for src in res.srcs.iter() {
                self.links.insert(*src, dst);
            }
        }
        self.results.insert(id, res);
    }
    /// Propagate the identifier to a destination from the source location and pointer extension identifier.
    pub fn propagate_resolved(&mut self, id: I, src: &(Loc, PtrExtIdent)) {
        if let Some(dst) = self.links.get(src).cloned() {
            self.insert_dst(id, dst);
        }
    }
}

impl<I: TotallyComparable> Default for Resolver<I> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::annot::syntax::{Annot, Refiner};
    use crate::llir::interp::rtti::ExtName;
    use crate::llir::parser::Parser as LLIRParser;
    use crate::llir::syntax::Typedefs;
    use crate::reader::sexpr::SExpr;
    use crate::typechk::env::tests::prepare_typeenv;
    #[test]
    fn check_annot_file_validity() {
        for (input, expected) in vec![
            (
                r#"
                (define-refiner tvalue-tag (cast-match
                    ((== (bitand (bitlshr (deref $0) 4) 0x0f) 0x01) i64)
                    ((== (bitlshr (bitand (deref $0) 0xf0) 4) 0x02) (ptr i64))))
                "#,
                "Ok(())",
            ),
            (
                r#"
                (define-refiner tvalue-tag (cast-match
                    ((== (bitand (bitlshr (deref $0) 4) 0x0f) 0x01) i64)
                    ((== (bitlshr (bitand (deref $0) 0xf0) 4) 0x01) (ptr i64))))
                "#,
                "Err(conflict case and(eq(bitand(bitlshr(deref($0), 0x4), 0xf), 0x1)) -> i64 and case and(eq(bitlshr(bitand(deref($0), 0xf0), 0x4), 0x1)) -> i64* between incompatible types)",
            ),
            (
                r#"
                (define-refiner tvalue-tag (cast-match
                    ((== (bitand (bitlshr (deref $0) 4) 0x0f) 0x01) i64)
                    ((== (bitlshr (bitand (deref $0) 0xf0) 4) 0x01) (ptr "struct.Unused"))))
                "#,
                "Err(conflict case and(eq(bitand(bitlshr(deref($0), 0x4), 0xf), 0x1)) -> i64 and case and(eq(bitlshr(bitand(deref($0), 0xf0), 0x4), 0x1)) -> %struct.Unused* between incompatible types)",
            ),
            (
                r#"
                (define-refiner tvalue-tag (cast-match
                    ((== (bitand (bitlshr (deref $0) 4) 0x0f) 0x01) (ptr i64))
                    ((== (bitlshr (bitand (deref $0) 0xf0) 4) 0x01) (ptr "struct.Unused"))))
                "#,
                "Ok(())",
            ),
        ] {
            let typedefs = Typedefs::empty();
            let env = prepare_typeenv(&typedefs);
            let annotfile = AnnotFile::parse(input, String::from("annotfile")).expect(&format!("{}", input));
            let got = match CastChk::check_annot_file_validity(&annotfile, &env) {
                Ok(()) => format!("Ok(())"),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn judge_cast_match_target() {
        let typedefs = Typedefs::new(btree_map![
            LocalIdent::from("byte") => LLIRType::I8,
            LocalIdent::from("dword") => LLIRType::I32,
            LocalIdent::from("tuple1") => LLIRParser::new_type("{ i64 }"),
            LocalIdent::from("tuple2") => LLIRParser::new_type("{ i64, i8 }"),
            LocalIdent::from("tuple3") => LLIRParser::new_type("{ i64, i32 }")
        ]);
        let env = prepare_typeenv(&typedefs);
        let loc = Loc::new(
            GlobalIdent::from("main"),
            Label::from(LocalIdent::from("0")),
            0,
        );
        let input = SExpr::parse(
            r#"
            (cast-match
              ((== (bitand (deref $0) 0x0f) 0x00) void)
              ((== (bitand (deref $0) 0x0f) 0x01) void)
              ((== (bitand (deref $0) 0x0f) 0x02) void)
              ((== (bitand (deref $0) 0x0f) 0x03) "byte")
              ((== (bitand (deref $0) 0x0f) 0x04) i32)
              ((== (bitand (deref $0) 0xf0) 0x10) "tuple1")
              ((== (bitand (deref $0) 0x0f) 0x05) "tuple2")
              ((== (bitand (deref $0) 0x0f) 0x06) "tuple3"))
            "#,
        );
        let refiner = Refiner::try_parse(&input).unwrap();
        let cm = refiner.try_to_cast_match().unwrap();
        for (expected, reason, cond, target) in vec![
            // void targets (constant enumeration type)
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x1)))",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x01))",
                "void",
            ),
            (
                "None",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x03))",
                "void",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x2)))",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x02))",
                "void",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x03))",
                "void",
            ),
            // basic type targets
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x3)))",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x03))",
                "i8",
            ),
            (
                "None",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x04))",
                "i8",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x4)))",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x04))",
                "%dword",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x03))",
                "%dword",
            ),
            // inherited type targets
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x5)))",
                CastReasonKind::Load,
                "(and (== (bitand (deref $0) 0x0f) 0x05))",
                "%tuple2",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x5)))",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x15))",
                "%tuple2",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x5)))",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x05))",
                "%tuple2",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x5)))",
                CastReasonKind::Load,
                "(and (== (bitand (deref $0) 0x0f) 0x05))",
                "%tuple1",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf0), 0x10)))",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x15))",
                "%tuple1",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x5)))",
                CastReasonKind::Load,
                "(and (== (deref $0) 0x05))",
                "%tuple1",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf0), 0x10)))",
                CastReasonKind::Load,
                "(and (== (bitand (deref $0) 0xf0) 0x10))",
                "%tuple1",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (bitand (deref $0) 0x0f) 0x05))",
                "%tuple2",
            ),
            (
                "Some(and(eq(bitand(deref($0), 0xf0), 0x10), eq(bitand(deref($0), 0xf), 0x5)))",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x15))",
                "%tuple2",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x05))",
                "%tuple2",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (bitand (deref $0) 0x0f) 0x05))",
                "%tuple1",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x15))",
                "%tuple1",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x05))",
                "%tuple1",
            ),
            (
                "None",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (bitand (deref $0) 0xf0) 0x10))",
                "%tuple1",
            ),
            // NOTICE: condition (premise) is false, but this is safe cast,
            //   because no execution reaches there.
            (
                "Some(and(eq(bitand(deref($0), 0xf), 0x4)))",
                CastReasonKind::Store(ExtName::CastTag(Ident::from("tag"), 0)),
                "(and (== (deref $0) 0x03) (== (deref $0) 0x04))",
                "i32",
            ),
        ] {
            let cond = SExpr::parse(&cond);
            let cond = Cond::try_parse(&cond).expect(&format!("{}", cond));
            let target = LLIRParser::new_type(&target);
            let result = match CastChk::judge_cast_match_target(
                cm.cases(),
                reason,
                &cond,
                &target,
                &loc,
                &env,
            ) {
                Some(cond) => format!("Some({})", cond),
                None => format!("None"),
            };
            assert_eq!(expected, result, "({:?}, {}, {})", reason, cond, target);
        }
    }
    #[test]
    fn judge_cast_match_equality() {
        let refiner = Refiner::try_parse(&SExpr::parse(
            r#"
            (cast-match
              ((== (bitand (deref $0) 0xff) 0x01) i8)
              ((== (bitand (deref $0) 0xff) 0x02) i32))
            "#,
        ))
        .unwrap();
        let cm = refiner.try_to_cast_match().unwrap();
        let annot = Annot::try_parse(&SExpr::parse(
            r#"(apply-refiner "struct.Object" (fieldptr 1) (cast object-tag (fieldptr 0)))"#,
        ))
        .unwrap();
        let refiner = match annot {
            Annot::ApplyRefiner(refiner) => refiner,
            annot => panic!("unexpected annotation {}", annot),
        };
        let expected_input_list = vec![
            (
                "Some(and(eq(bitand(deref($0), 0xff), bitand(deref($1), 0xff))))",
                "(and (== (deref $0) (deref $1)))",
            ),
            // NOTICE: condition (premise) is false, but this is safe cast,
            //   because no execution reaches there.
            (
                "Some(and(eq(bitand(deref($0), 0xff), bitand(deref($1), 0xff))))",
                "(and (== (deref $0) (deref $1)) (== (deref $0) 0x01))",
            ),
        ];
        for (expected, input) in expected_input_list {
            let cond = SExpr::parse(input);
            let cond = Cond::try_parse(&cond).expect(input);
            let result = match CastChk::judge_cast_match_equality(&refiner, &cm.cases(), &cond) {
                Some(cond) => format!("Some({})", cond),
                None => format!("None"),
            };
            assert_eq!(expected, result, "{}", input);
        }
    }
}
