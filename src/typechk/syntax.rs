//! The syntax of the types.

use crate::fmt::DisplayIter;
use crate::llir::abi::AffineExpr;
use crate::llir::interp::rtti::{ExtIdent, ExtName};
use crate::llir::syntax::{
    FuncSig, GlobalIdent, Loc, LocalIdent, Param, RetParam, Type as LLIRType, Value,
};
use crate::typechk::env::TypeEnv;
use std::convert::TryInto;
use std::fmt;

/// A size in byte.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Size {
    /// A constant size.
    Const(i64),
    /// A dynamically calculated size.
    Dynamic,
}

impl Size {
    /// Returns the size as `usize`.
    pub fn try_to_usize(&self) -> Option<usize> {
        match self {
            Size::Const(n) => match TryInto::<usize>::try_into(*n) {
                Ok(n) => Some(n),
                Err(_) => None,
            },
            Size::Dynamic => None,
        }
    }
}

impl From<Option<i64>> for Size {
    fn from(n: Option<i64>) -> Size {
        match n {
            Some(n) => Size::Const(n),
            None => Size::Dynamic,
        }
    }
}

/// An inference variable used in identifying pointers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InferVar(Option<usize>);

impl InferVar {
    /// Returns a new inference variable with the given ID.
    pub fn new(id: usize) -> InferVar {
        InferVar(Some(id))
    }
    /// Returns a new dummy inference variable.
    pub fn dummy() -> InferVar {
        InferVar(None)
    }
}

impl fmt::Display for InferVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.0 {
            Some(id) => write!(f, "?{}", id),
            None => write!(f, "?_"),
        }
    }
}

/// A pointer extention identifier that is an extention identifier with a inference variable of a pointer.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PtrExtIdent(InferVar, ExtIdent);

impl PtrExtIdent {
    /// Returns a new pointer extention identifier.
    pub fn new(var: InferVar, ident: ExtIdent) -> PtrExtIdent {
        PtrExtIdent(var, ident)
    }
    /// Returns the inference variable of the pointer.
    pub fn var(&self) -> InferVar {
        self.0
    }
    /// Returns the extension identifier.
    pub fn ident(&self) -> ExtIdent {
        self.1
    }
    /// Returns a new dummy one.
    pub fn to_dummy(&self) -> PtrExtIdentDummy {
        PtrExtIdentDummy(self.ident())
    }
}

impl fmt::Display for PtrExtIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "*<{}>{}", self.var(), self.ident())
    }
}

/// A pointer extention identifier with a dummy inference variable of a pointer.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PtrExtIdentDummy(ExtIdent);

impl fmt::Display for PtrExtIdentDummy {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "*<?_>{}", self.0)
    }
}

/// A kind of memory allocation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AllocKind {
    /// Allocation on stack.
    Alloca,
    /// Allocation on heap by the function.
    Dynamic(GlobalIdent),
}

impl fmt::Display for AllocKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            AllocKind::Alloca => write!(f, "alloca"),
            AllocKind::Dynamic(name) => write!(f, "dynamic{}", name),
        }
    }
}

/// A type.
#[derive(Clone, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub enum Type {
    /// A unit type.
    Void,
    /// A signed integer type with the given bit width.
    I(usize),
    /// An IEEE-754 floating point number type with the given bit width.
    F(usize),
    /// A pointer type with an inference variable.
    Ptr(InferVar, Box<Type>),
    /// A (scalable) vector type.
    Vector(bool, usize, Box<Type>),
    /// An array type with the given length.
    Array(usize, Box<Type>),
    /// A tuple type.
    Struct(Vec<Type>),
    /// A function type (with variadic arguments optionally).
    Func(Box<Type>, Vec<Type>, bool),
    /// A type name.
    Name(LocalIdent),
    /// An extention type.
    Ext(ExtIdent, Box<Type>),
    /// A type for the undetermined null pointer.
    Nullptr,
    /// A padding with the given size in byte.
    Pad(usize),
    /// A type for a poisoned region by the allocation kind with the size.
    Poison(AllocKind, Size),
}

impl Type {
    /// Returns a type whose (all) inference variables are refreshed.
    pub fn refresh(&mut self, all: bool, env: &mut TypeEnv) {
        match self {
            Type::Void
            | Type::I(_)
            | Type::F(_)
            | Type::Name(_)
            | Type::Ext(..)
            | Type::Nullptr
            | Type::Pad(_)
            | Type::Poison(..) => {}
            Type::Ptr(var, ty) => {
                if all || var == &InferVar(None) {
                    *var = env.new_infervar();
                }
                ty.refresh(all, env);
            }
            Type::Vector(_, _, ty) | Type::Array(_, ty) => ty.refresh(all, env),
            Type::Struct(fields) => {
                for field in fields {
                    field.refresh(all, env);
                }
            }
            Type::Func(ret, args, _) => {
                ret.refresh(all, env);
                for arg in args {
                    arg.refresh(all, env);
                }
            }
        }
    }
    /// Collapses all inference variables with dummy.
    pub fn dummy(&mut self) {
        match self {
            Type::Void
            | Type::I(_)
            | Type::F(_)
            | Type::Name(_)
            | Type::Ext(..)
            | Type::Nullptr
            | Type::Pad(_)
            | Type::Poison(..) => {}
            Type::Ptr(var, ty) => {
                *var = InferVar(None);
                ty.dummy();
            }
            Type::Vector(_, _, ty) | Type::Array(_, ty) => ty.dummy(),
            Type::Struct(fields) => {
                for field in fields {
                    field.dummy();
                }
            }
            Type::Func(ret, args, _) => {
                ret.dummy();
                for arg in args {
                    arg.dummy();
                }
            }
        }
    }
    /// Returns a corresponding LLIR type.
    pub fn try_to_llir_type(&self) -> Option<LLIRType<ExtIdent>> {
        match self {
            Type::I(1) => Some(LLIRType::I1),
            Type::I(8) => Some(LLIRType::I8),
            Type::I(16) => Some(LLIRType::I16),
            Type::I(32) => Some(LLIRType::I32),
            Type::I(64) => Some(LLIRType::I64),
            Type::F(32) => Some(LLIRType::Float),
            Type::F(64) => Some(LLIRType::Double),
            Type::Ptr(_, ty) => Some(LLIRType::Ptr(Box::new(ty.try_to_llir_type()?))),
            Type::Vector(vscale, n, ty) => {
                if *n <= u32::MAX as usize {
                    return Some(LLIRType::Vector(
                        *vscale,
                        *n as u32,
                        Box::new(ty.try_to_llir_type()?),
                    ));
                }
                Some(LLIRType::Void)
            }
            Type::Array(n, ty) => {
                if *n <= u32::MAX as usize {
                    return Some(LLIRType::Array(*n as u32, Box::new(ty.try_to_llir_type()?)));
                }
                Some(LLIRType::Void)
            }
            Type::Struct(fields0) => {
                let mut fields = Vec::with_capacity(fields0.len());
                for field0 in fields0 {
                    fields.push(field0.try_to_llir_type()?);
                }
                Some(LLIRType::Struct(true, fields))
            }
            Type::Func(ret, args0, variadic) => {
                let mut args = Vec::with_capacity(args0.len());
                for arg0 in args0 {
                    args.push(Param::from(arg0.try_to_llir_type()?));
                }
                Some(LLIRType::Func(FuncSig {
                    ret: Box::new(RetParam::from(ret.try_to_llir_type()?)),
                    name: None,
                    args,
                    variadic: *variadic,
                }))
            }
            Type::Name(name) => Some(LLIRType::Name(*name)),
            Type::Ext(eid, ty) => Some(LLIRType::Ext(*eid, Box::new(ty.try_to_llir_type()?))),
            Type::Pad(size) => {
                if *size <= u32::MAX as usize {
                    return Some(LLIRType::Array(*size as u32, Box::new(LLIRType::I8)));
                }
                Some(LLIRType::Void)
            }
            _ => None,
        }
    }
    /// Returns the type as resolving the internal type names.
    pub fn normalize<'a, 'b>(&'a self, env: &'b TypeEnv) -> Result<&'b Type, String>
    where
        'a: 'b,
    {
        match self {
            Type::Name(name) => env.ty(name)?.normalize(env),
            ty => Ok(ty),
        }
    }
    /// Returns the size of a variable with the type.
    pub fn size(&self, env: &TypeEnv) -> Option<Size> {
        match self {
            Type::Void | Type::Func(..) => None,
            Type::I(n) | Type::F(n) => Some(Size::Const(((*n as i64) + 7) / 8)),
            Type::Ptr(_, _) | Type::Nullptr | Type::Poison(..) => Some(Size::Const(8)),
            Type::Vector(false, n, ty) => match ty.size(env)? {
                Size::Const(size) => Some(Size::Const((*n as i64) * size)),
                Size::Dynamic => Some(Size::Dynamic),
            },
            Type::Vector(true, _, _) => Some(Size::Dynamic),
            Type::Array(n, ty) => match ty.size(env)? {
                Size::Const(size) => Some(Size::Const((*n as i64) * size)),
                Size::Dynamic => Some(Size::Dynamic),
            },
            Type::Struct(fields) => {
                let mut size = 0;
                for field in fields {
                    size += match field.size(env)? {
                        Size::Const(size) => size,
                        Size::Dynamic => return Some(Size::Dynamic),
                    }
                }
                Some(Size::Const(size))
            }
            Type::Name(name) => match env.ty(name) {
                Ok(ty) => ty.size(env),
                Err(_) => None,
            },
            Type::Ext(_, orig) => orig.size(env),
            Type::Pad(size) => Some(Size::Const(*size as i64)),
        }
    }
    /// Returns the pointer extension identifier if the type can be handled as a pointer type.
    pub fn try_to_ptr_ext_ident<'a, 'b>(
        &'a self,
        env: &'b TypeEnv,
    ) -> Option<(PtrExtIdent, &'b Type)>
    where
        'a: 'b,
    {
        match self.normalize(env).ok()? {
            Type::Ptr(var, ty) => match ty.normalize(env).ok()? {
                Type::Ext(eid, ty) => Some((PtrExtIdent(*var, *eid), ty)),
                _ => None,
            },
            Type::Vector(_, n, ty) | Type::Array(n, ty) if *n == 1 => ty.try_to_ptr_ext_ident(env),
            Type::Struct(fields) if fields.len() == 1 => fields[0].try_to_ptr_ext_ident(env),
            _ => None,
        }
    }
    /// Returns the extension identifier if the type can be handled as a extension type.
    pub fn try_to_ext_ident(&self, env: &TypeEnv) -> Option<ExtIdent> {
        match self.normalize(env).ok()? {
            Type::Vector(_, n, ty) | Type::Array(n, ty) if *n == 1 => ty.try_to_ext_ident(env),
            Type::Struct(fields) if fields.len() == 1 => fields[0].try_to_ext_ident(env),
            Type::Ext(eid, _) => Some(*eid),
            _ => None,
        }
    }
    /// Returns `true` if the type contains a extention type.
    pub fn contains_ext(&self, env: &TypeEnv) -> Result<bool, String> {
        match self.normalize(env)? {
            Type::Vector(_, _, ty) | Type::Array(_, ty) => ty.contains_ext(env),
            Type::Struct(fields) => {
                for field in fields {
                    if field.contains_ext(env)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::Ext(..) => Ok(true),
            _ => Ok(false),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Type::Void => write!(f, "void"),
            Type::I(n) => write!(f, "i{}", n),
            Type::F(n) => write!(f, "f{}", n),
            Type::Ptr(var, ty) => write!(f, "*<{}>{}", var, ty),
            Type::Vector(vscale, n, ty) => {
                write!(f, "<")?;
                if *vscale {
                    write!(f, "vscale*")?;
                }
                write!(f, "{}>{}", n, ty)
            }
            Type::Array(len, ty) => write!(f, "[{}]{}", len, ty),
            Type::Struct(fields) => write!(f, "{}", DisplayIter("{", fields.iter(), ", ", "}")),
            Type::Func(ret, args, variadic) => {
                write!(f, "{} ({}", ret, DisplayIter("", args.iter(), ", ", ""))?;
                if *variadic {
                    if !args.is_empty() {
                        write!(f, ", ")?;
                    }
                    write!(f, "...")?;
                }
                write!(f, ")")
            }
            Type::Name(name) => write!(f, "{}", name),
            Type::Ext(eid, ty) => write!(f, "{}({})", eid, ty),
            Type::Nullptr => write!(f, "nullptr"),
            Type::Pad(size) => write!(f, "pad({})", size),
            Type::Poison(kind, size) => match size {
                Size::Const(size) => write!(f, "poison({}, {})", kind, size),
                Size::Dynamic => write!(f, "poison({}, ?)", kind),
            },
        }
    }
}

/// Arguments of a function.
#[derive(Clone, Debug)]
pub struct FuncArgs {
    /// The names of the arguments.
    pub argnames: Vec<VarName>,
    /// The indicator whether the variable function or not.
    pub variadic: bool,
}

/// An extended value.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ValueExt {
    /// Allocation with the given kind of the given LLIR type.
    Alloc(AllocKind, LLIRType<ExtIdent>),
    /// Collapse the poison type with the given LLIR type.
    CollapsePoison(Type, LLIRType<ExtIdent>),
    /// Declaration of a function with the given result and parameter type (and variadic arguments optionally).
    DeclareFunc(Type, Vec<Type>, bool),
    /// Declaration of a global variable with the given LLIR type.
    DeclareGlobal(LLIRType<ExtIdent>),
    /// Definition of a global variable with the given LLIR type and value.
    DefineGlobal(LLIRType<ExtIdent>, Value<ExtIdent>),
    /// Poison by the given allocation kind of the region with the given size.
    Poison(AllocKind, Size),
}

impl fmt::Display for ValueExt {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ValueExt::Alloc(kind, ty) => write!(f, "{}({})", kind, ty),
            ValueExt::CollapsePoison(ty1, ty2) => {
                write!(f, "collapse-poison({}, {})", ty1, ty2)
            }
            ValueExt::DeclareFunc(ret, args, variadic) => write!(
                f,
                "declare-func({}, {}, {})",
                ret,
                DisplayIter("[", args.iter(), ", ", "]"),
                variadic
            ),
            ValueExt::DeclareGlobal(ty) => write!(f, "declare-global({})", ty),
            ValueExt::DefineGlobal(ty, val) => write!(f, "define-global({}, {})", ty, val),
            ValueExt::Poison(kind, size) => match size {
                Size::Const(size) => write!(f, "poison({}, {})", kind, size),
                Size::Dynamic => write!(f, "poison({}, ?)", kind),
            },
        }
    }
}

/// A term in judgement.
#[derive(Clone, Debug)]
pub enum JudgeTerm {
    /// Cast a value of the type at left as a right one.
    Cast(Type, Type),
    /// Load the value of the type at left from a pointer of the type at right.
    Load(Type, Type),
    /// Memory copy from the pointer of the type at left to the right one by the size.
    Memcpy(Type, Type, Size),
}

/// A kind of [`Effect`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectKind {
    /// Call the global function.
    CallGlobal(GlobalIdent),
    /// Call a function indirectly.
    CallIndirect,
    /// Memory copy (see [`JudgeTerm::Memcpy`]) by the size.
    Memcpy(Type, Type, Size),
}

impl fmt::Display for EffectKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EffectKind::CallGlobal(name) => write!(f, "call-global({})", name),
            EffectKind::CallIndirect => write!(f, "call-indirect"),
            EffectKind::Memcpy(src, dst, size) => write!(f, "memcpy({}, {}, {:?})", src, dst, size),
        }
    }
}

/// A store (memory copy) effect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StoreEffect<'a> {
    /// The type of the copy source value.
    pub src: &'a Type,
    /// The inference variable of the destination pointer.
    pub dstvar: InferVar,
    /// The type of the copy destination value.
    pub dst: &'a Type,
}

/// An effect that is a list of the pair of the effect kind and the instruction location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Effect(Vec<(EffectKind, Loc)>);

impl Effect {
    /// Returns an empty effect.
    pub fn empty() -> Effect {
        Effect(Vec::new())
    }
    /// Returns an iterator.
    pub fn iter(&self) -> impl Iterator<Item = &(EffectKind, Loc)> {
        self.0.iter()
    }
    /// Merges the other.
    pub fn merge(&mut self, other: &Effect) {
        self.0.extend_from_slice(&other.0);
    }
    /// Pushes the given effect kind and the instruction location.
    pub fn push(&mut self, kind: EffectKind, loc: Loc) {
        self.0.push((kind, loc));
    }
    /// Returns a store effect if found.
    pub fn try_to_store(&self, loc: &Loc, env: &TypeEnv) -> Option<StoreEffect> {
        for (kind, l) in &self.0 {
            match l.cmp_in_block(loc) {
                // The effect kind is set before than loc, hence does not interfere.
                Some(d) if d < 0 => continue,
                _ => {}
            }
            match kind {
                EffectKind::CallGlobal(_) | EffectKind::CallIndirect => {}
                EffectKind::Memcpy(dst, src, Size::Const(len)) => match (dst, src) {
                    (Type::Ptr(dstvar, dst), Type::Ptr(_, src)) => {
                        if let Some(dstsize) = dst.size(env) {
                            if let Some(srcsize) = src.size(env) {
                                if dstsize >= srcsize && srcsize == Size::Const(*len) {
                                    return Some(StoreEffect {
                                        src,
                                        dstvar: *dstvar,
                                        dst,
                                    });
                                }
                            }
                        }
                    }
                    _ => return None,
                },
                EffectKind::Memcpy(_, _, Size::Dynamic) => {}
            }
        }
        None
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "effect[")?;
        for (i, (kind, loc)) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}{}", kind, loc)?;
        }
        write!(f, "]")
    }
}

/// A name of a variable.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum VarName {
    /// For returning a value from the global function.
    Ret(GlobalIdent),
    /// For a local variable in the global function.
    Local(LocalIdent, GlobalIdent),
    /// For the global variable.
    Global(GlobalIdent),
}

impl fmt::Display for VarName {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            VarName::Ret(funcname) => write!(f, "ret{}", funcname),
            VarName::Local(regname, funcname) => write!(f, "{}{}", regname, funcname),
            VarName::Global(regname) => write!(f, "{}", regname),
        }
    }
}

/// A kind of [`Constr`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ConstrKind {
    /// Related to control flow.
    CtrlFlow,
    /// Related to object lifetime.
    ObjectLifetime,
    /// Related to pointer arithmetic.
    PointerArith,
    /// Related to type cast.
    TypeCast,
    /// Other kind.
    Other,
}

impl fmt::Display for ConstrKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ConstrKind::CtrlFlow => write!(f, "control-flow"),
            ConstrKind::ObjectLifetime => write!(f, "object-lifetime"),
            ConstrKind::PointerArith => write!(f, "pointer-arith"),
            ConstrKind::TypeCast => write!(f, "type-cast"),
            ConstrKind::Other => write!(f, "other"),
        }
    }
}

/// A reason of [`Constr::Alloc`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AllocReason {
    /// Allocation of a normal object.
    Normal,
    /// Allocation of an object containing extension types.
    ContainExt,
}

impl fmt::Display for AllocReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            AllocReason::Normal => write!(f, "normal object"),
            AllocReason::ContainExt => write!(f, "containing extension types"),
        }
    }
}

/// A kind of [`Constr::Free`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FreeKind {
    /// Free by the global function.
    Dynamic(GlobalIdent),
}

impl fmt::Display for FreeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            FreeKind::Dynamic(name) => write!(f, "{}", name),
        }
    }
}

/// A constraint which will be resolved after the structural type checking.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Constr {
    /// Allocation of an object with the type.
    Alloc(AllocKind, AllocReason, Type),
    /// Cast the type at left as the type at right.
    Cast(Type, Type),
    /// Pointer escape via `getelementptr` instruction.
    EscapeViaGetelementptr(Type, Type, AffineExpr<ExtIdent>),
    /// Free of an object.
    Free(FreeKind),
    /// Indirect call of the function with the type.
    IndirectCall(Type),
    /// Application of `inttoptr`.
    IntToPtr(Type, Type),
    /// Memory load from the value with the type at left from a pointer with the type at right.
    Load(Type, Type),
    /// Memory copy from a pointer with the type at left to a pointer with the type at right.
    Memcpy(Type, Type, Size),
    /// An index used in `getelementptr` instruction from the type is not constantly zero.
    NonzeroIndex(AffineExpr<ExtIdent>, Type),
    /// The type at left is not subtype of the type at right.
    NotSubtype(Type, Type),
    /// An offset used in `getelementptr` instruction from the type is out-of-bound.
    OutOfBoundOffset(AffineExpr<ExtIdent>, Type),
    /// Store a value with the type at left to a pointer with the type at right.
    Store(Type, Type),
    /// The size of an allocation of a object with the type does not match the poison type.
    UnmatchedPoisonSize(Type, Size),
    /// An unsupported feature indicated by the message string.
    UnsupportedFeature(String),
    /// A variadic function with the type.
    VariadicFunc(Type),
}

impl Constr {
    /// Collapses all inference variables to dummy.
    pub fn dummy(&mut self) {
        match self {
            Constr::Alloc(_, _, ty)
            | Constr::IndirectCall(ty)
            | Constr::NonzeroIndex(_, ty)
            | Constr::OutOfBoundOffset(_, ty)
            | Constr::UnmatchedPoisonSize(ty, _)
            | Constr::VariadicFunc(ty) => ty.dummy(),
            Constr::Cast(ty1, ty2)
            | Constr::EscapeViaGetelementptr(ty1, ty2, _)
            | Constr::IntToPtr(ty1, ty2)
            | Constr::Load(ty1, ty2)
            | Constr::Memcpy(ty1, ty2, _)
            | Constr::NotSubtype(ty1, ty2)
            | Constr::Store(ty1, ty2) => {
                ty1.dummy();
                ty2.dummy();
            }
            Constr::Free(_) | Constr::UnsupportedFeature(_) => {}
        }
    }
    /// Returns `true` if the constraint is a kind of warning.
    pub fn is_warning(&self) -> bool {
        !matches!(self, Constr::Alloc(_, AllocReason::Normal, _))
    }
    /// Returns the kind.
    pub fn kind(&self) -> ConstrKind {
        match self {
            Constr::Alloc(..) | Constr::Free(_) => ConstrKind::ObjectLifetime,
            Constr::Cast(..)
            | Constr::EscapeViaGetelementptr(..)
            | Constr::Load(..)
            | Constr::Memcpy(..)
            | Constr::Store(..)
            | Constr::IntToPtr(..)
            | Constr::NotSubtype(..)
            | Constr::VariadicFunc(_) => ConstrKind::TypeCast,
            Constr::NonzeroIndex(..)
            | Constr::OutOfBoundOffset(..)
            | Constr::UnmatchedPoisonSize(..) => ConstrKind::PointerArith,
            Constr::IndirectCall(_) => ConstrKind::CtrlFlow,
            Constr::UnsupportedFeature(_) => ConstrKind::Other,
        }
    }
    /// Returns the source and destination types if related to type casts.
    pub fn try_get_cast_srcdst(&self) -> Option<(&Type, &Type)> {
        match self {
            Constr::Cast(src, dst)
            | Constr::Load(dst, src)
            | Constr::Memcpy(dst, src, _)
            | Constr::Store(src, dst)
            | Constr::IntToPtr(src, dst)
            | Constr::NotSubtype(src, dst) => Some((src, dst)),
            _ => None,
        }
    }
    /// Returns a cast reason if related to type casts.
    pub fn try_to_cast_reason(&self, env: &TypeEnv) -> Option<CastReason> {
        match self {
            Constr::Cast(Type::Ptr(srcvar, srcty), Type::Ptr(_, dstty)) => {
                match (srcty.normalize(env).as_ref(), dstty.normalize(env).as_ref()) {
                    (Ok(Type::Ext(srceid, _)), Ok(Type::Ext(dsteid, _)))
                        if srceid.name.id() == dsteid.name.id()
                            && srceid.name.is_downcast_target()
                            && dsteid.name.is_downcast_subtarget() =>
                    {
                        let srcpeid = PtrExtIdent(*srcvar, *srceid);
                        Some(CastReason::Downcast(srcpeid, dstty.try_to_llir_type()?))
                    }
                    (Ok(Type::Ext(..)), Ok(Type::Ext(..))) => None,
                    (Ok(_), Ok(Type::Ext(..))) => None,
                    (Ok(Type::Ext(srceid, _)), Ok(_)) => {
                        let srcpeid = PtrExtIdent(*srcvar, *srceid);
                        Some(CastReason::Downcast(srcpeid, dstty.try_to_llir_type()?))
                    }
                    _ => None,
                }
            }
            Constr::Load(dst, Type::Ptr(srcvar, srcty)) => match srcty.normalize(env) {
                Ok(Type::Ext(srceid, _)) => Some(CastReason::Load(
                    dst.try_to_llir_type()?,
                    PtrExtIdent(*srcvar, *srceid),
                )),
                _ => None,
            },
            Constr::Memcpy(Type::Ptr(dstvar, dstty), Type::Ptr(srcvar, srcty), len) => {
                match (dstty.normalize(env).as_ref(), srcty.normalize(env).as_ref()) {
                    (Ok(Type::Ext(dsteid, _)), Ok(Type::Ext(srceid, _))) => {
                        Some(CastReason::Memcpy(
                            PtrExtIdent(*dstvar, *dsteid),
                            PtrExtIdent(*srcvar, *srceid),
                            *len,
                        ))
                    }
                    (Ok(dst), Ok(Type::Ext(srceid, _))) if dst.size(env) == Some(*len) => {
                        let srcpeid = PtrExtIdent(*srcvar, *srceid);
                        Some(CastReason::Load(dst.try_to_llir_type()?, srcpeid))
                    }
                    (Ok(Type::Ext(dsteid, _)), Ok(src)) if src.size(env) == Some(*len) => {
                        let dstpeid = PtrExtIdent(*dstvar, *dsteid);
                        Some(CastReason::Store(src.try_to_llir_type()?, dstpeid))
                    }
                    _ => None,
                }
            }
            Constr::Store(src, Type::Ptr(dstvar, dstty)) => match dstty.normalize(env).as_ref() {
                Ok(Type::Ext(dsteid, _)) => Some(CastReason::Store(
                    src.try_to_llir_type()?,
                    PtrExtIdent(*dstvar, *dsteid),
                )),
                _ => None,
            },
            _ => None,
        }
    }
}

impl fmt::Display for Constr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Constr::Alloc(kind, reason, ty) => {
                write!(f, "{} is allocated with {} as {}", ty, kind, reason)
            }
            Constr::Cast(ty1, ty2) => {
                write!(f, "{} is cast as {}", ty1, ty2)
            }
            Constr::EscapeViaGetelementptr(fieldty, basety, offset) => write!(
                f,
                "escape {} from {} at offset {} via getelementptr",
                fieldty, basety, offset
            ),
            Constr::Free(kind) => {
                write!(f, "{} invalidates the given pointer", kind)
            }
            Constr::IndirectCall(ty) => write!(f, "indirectly call {}", ty),
            Constr::IntToPtr(src, dst) => write!(f, "{} is cast as {}", src, dst),
            Constr::Load(dst, src) => write!(f, "load {} from {}", dst, src),
            Constr::Memcpy(dst, src, len) => match len {
                Size::Const(len) => write!(f, "memcpy {} to {} with length {}", src, dst, len),
                Size::Dynamic => write!(f, "memcpy {} to {} with dynamic length", src, dst),
            },
            Constr::NonzeroIndex(index, base_ty) => {
                write!(f, "non-zero index {} from {}", index, base_ty)
            }
            Constr::NotSubtype(ty1, ty2) => write!(f, "{} is not subtype of {}", ty1, ty2),
            Constr::OutOfBoundOffset(offset, base_ty) => {
                write!(f, "out-of-bound offset {} in {}", offset, base_ty)
            }
            Constr::UnmatchedPoisonSize(ty, size) => match size {
                Size::Const(size) => write!(
                    f,
                    "allocation size of {} does not match with poison with size {}",
                    ty, size
                ),
                Size::Dynamic => write!(
                    f,
                    "allocation size of {} does not match with poison with dynamic size",
                    ty
                ),
            },
            Constr::Store(src, dst) => write!(f, "store {} to {}", src, dst),
            Constr::UnsupportedFeature(msg) => write!(f, "unsupported feature: {}", msg),
            Constr::VariadicFunc(ty) => write!(f, "variadic function {}", ty),
        }
    }
}

/// A kind of [`CastReason`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CastReasonKind {
    /// Related to downcast.
    Downcast,
    /// Related to load operation.
    Load,
    /// Related to store operation with a value with the extension type.
    Store(ExtName),
}

impl CastReasonKind {
    /// Returns `true` if the kind means the store of tags.
    pub fn is_store_tag(&self) -> bool {
        match self {
            CastReasonKind::Store(name) => name.is_any_tag(),
            _ => false,
        }
    }
}

/// A cast reason indicating the reason for checking the cast.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CastReason {
    /// Downcast the pointer at left to the LLIR type at right.
    Downcast(PtrExtIdent, LLIRType<ExtIdent>),
    /// Load a value with the LLIR type at left from the pointer at right.
    Load(LLIRType<ExtIdent>, PtrExtIdent),
    /// Memory copy from the pointer at left to the pointer at right with the size.
    Memcpy(PtrExtIdent, PtrExtIdent, Size),
    /// Store a value with the LLIR type to the pointer at right.
    Store(LLIRType<ExtIdent>, PtrExtIdent),
}

impl CastReason {
    /// Returns the kind.
    pub fn kind(&self) -> CastReasonKind {
        match self {
            CastReason::Downcast(..) => CastReasonKind::Downcast,
            CastReason::Load(..) => CastReasonKind::Load,
            CastReason::Store(_, dst) | CastReason::Memcpy(dst, _, _) => {
                CastReasonKind::Store(dst.ident().name)
            }
        }
    }
    /// Returns the pointer extention identifier.
    pub fn peid(&self) -> PtrExtIdent {
        match self {
            CastReason::Downcast(peid, _)
            | CastReason::Load(_, peid)
            | CastReason::Memcpy(peid, _, _)
            | CastReason::Store(_, peid) => *peid,
        }
    }
}

impl fmt::Debug for CastReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CastReason::Downcast(src, dst) => {
                write!(f, "downcast {} with target {}", src, dst)
            }
            CastReason::Load(dst, src) => write!(f, "load {} from {}", dst, src),
            CastReason::Memcpy(dst, src, len) => {
                write!(f, "memcpy {} to {} with ", src, dst)?;
                match len {
                    Size::Const(len) => write!(f, "length {}", len),
                    Size::Dynamic => write!(f, "dynamic length"),
                }
            }
            CastReason::Store(src, dst) => write!(f, "store {} to {}", src, dst),
        }
    }
}

impl fmt::Display for CastReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CastReason::Downcast(src, dst) => {
                write!(f, "downcast {} with target {}", src.to_dummy(), dst)
            }
            CastReason::Load(dst, src) => write!(f, "load {} from {}", dst, src.to_dummy()),
            CastReason::Memcpy(dst, src, len) => {
                write!(f, "memcpy {} to {} with ", src.to_dummy(), dst.to_dummy())?;
                match len {
                    Size::Const(len) => write!(f, "length {}", len),
                    Size::Dynamic => write!(f, "dynamic length"),
                }
            }
            CastReason::Store(src, dst) => write!(f, "store {} to {}", src, dst.to_dummy()),
        }
    }
}

/// Constraints that is the list of the pair of the instruction location and the constraint.
#[derive(Clone, Debug)]
pub struct Constrs(Vec<(Loc, Constr)>);

impl Constrs {
    /// Returns new empty one.
    pub fn empty() -> Constrs {
        Constrs(Vec::new())
    }
    /// Returns the constraint by index.
    pub fn get(&self, i: usize) -> Option<&(Loc, Constr)> {
        self.0.get(i)
    }
    /// Returns an interator.
    pub fn iter(&self) -> impl Iterator<Item = &(Loc, Constr)> {
        self.0.iter()
    }
    /// Inserts the constraint.
    pub fn insert(&mut self, reason: Constr, loc: Loc) -> Result<(), String> {
        self.0.push((loc, reason));
        Ok(())
    }
}

impl fmt::Display for Constrs {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[")?;
        for (i, (loc, reason)) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", loc, reason)?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llir::syntax::{GlobalIdent, Label, LocalIdent};
    use crate::typechk::env::tests::{
        new_type, prepare_typedefs, prepare_typeenv, prepare_typeset,
    };
    #[test]
    fn type_try_to_llir_type() {
        let mut env = prepare_typeenv(&prepare_typedefs(
            "tuple2,tuple2-cast-tag,tuple2-cast-target",
        ));
        let typeset = prepare_typeset("!tuple2,!nullptr,!pad4,!alloca16");
        for (expected, input) in vec![
            ("None", "void"),
            ("Some(i1)", "i1"),
            ("Some(i8)", "i8"),
            ("Some(i16)", "i16"),
            ("Some(i32)", "i32"),
            ("Some(i64)", "i64"),
            ("Some(float)", "float"),
            ("Some(double)", "double"),
            ("Some(i32**)", "i32**"),
            ("Some(<4 x i32>)", "<4 x i32>"),
            ("Some(<vscale x 4 x i32>)", "<vscale x 4 x i32>"),
            ("Some([4 x i32])", "[4 x i32]"),
            ("Some(<{  }>)", "{}"),
            (
                "Some(<{ i64, i16, [2 x i8], [2 x i32], [4 x i8] }>)",
                "{ i64, i16, [2 x i32] }",
            ),
            ("Some(i32 ())", "i32 ()"),
            ("Some(i32 (i16, i8, ...))", "i32 (i16, i8, ...)"),
            ("None", "opaque"),
            ("Some(%tuple2)", "!tuple2"),
            ("None", "!nullptr"),
            ("Some([4 x i8])", "!pad4"),
            ("None", "!alloca16"),
            (
                "Some(!tuple2-tag.cast-target@1+0(<{ %tuple2-cast-tag, i32 }>))",
                "%tuple2-cast-target",
            ),
        ] {
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let ty = new_type(input, &loc, &mut env, &typeset);
            let got = match ty.try_to_llir_type() {
                Some(ty) => format!("Some({})", ty),
                None => format!("None"),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn type_size() {
        let mut env = prepare_typeenv(&prepare_typedefs("tuple2"));
        let typeset = prepare_typeset("!tuple2,!nullptr,!alloca16,!pad4");
        for (expected, input) in vec![
            ("None", "void"),
            ("Some(Const(4))", "i32"),
            ("Some(Const(8))", "double"),
            ("Some(Const(8))", "i8*"),
            ("Some(Const(16))", "<4 x i32>"),
            ("Some(Dynamic)", "<vscale x 4 x i32>"),
            ("Some(Const(16))", "[4 x i32]"),
            ("Some(Const(24))", "{ i64, i16, [2 x i32] }"),
            ("None", "i32 (...)"),
            ("Some(Const(8))", "!tuple2"),
            ("Some(Const(8))", "!nullptr"),
            ("Some(Const(8))", "!alloca16"),
            ("Some(Const(4))", "!pad4"),
        ] {
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let ty = new_type(input, &loc, &mut env, &typeset);
            let got = match ty.size(&env) {
                Some(size) => format!("Some({:?})", size),
                None => format!("None"),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn type_contains_ext() {
        let mut env = prepare_typeenv(&prepare_typedefs(
            "tuple2,tuple2-cast-tag,tuple2-cast-target",
        ));
        let typeset = prepare_typeset("");
        for (expected, input) in vec![
            ("Ok(true)", "<4 x %tuple2-cast-target>"),
            ("Ok(false)", "<4 x i64>"),
            ("Ok(true)", "[4 x %tuple2-cast-target]"),
            ("Ok(false)", "[4 x i64]"),
            ("Ok(true)", "{ %tuple2-cast-target, i64 }"),
            ("Ok(false)", "{ i64, i64 }"),
            ("Ok(false)", "%tuple2-cast-target*"),
        ] {
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let ty = new_type(input, &loc, &mut env, &typeset);
            let got = match ty.contains_ext(&env) {
                Ok(res) => format!("Ok({})", res),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn constr_reason_try_to_cast_reason() {
        let mut env = prepare_typeenv(&prepare_typedefs(
            "tuple2,tuple2-cast-tag,tuple2-cast-target,tuple2-downcast-tag,tuple2-downcast-target,tuple2-downcast-subtarget",
        ));
        let typeset = prepare_typeset("");
        for (expected, srcinput, dstinput) in vec![
            (
                "Some(downcast *<?0>!tuple2-tag.downcast-target@2+0 with target %tuple2-downcast-subtarget)",
                "%tuple2-downcast-target*",
                "%tuple2-downcast-subtarget*",
            ),
            ("None", "%tuple2*", "%tuple2-cast-target*"),
            (
                "Some(downcast *<?4>!tuple2-tag.cast-target@1+0 with target i32)",
                "%tuple2-cast-target*",
                "i32*",
            ),
            ("None", "i32*", "i64*"),
        ] {
            let loc = Loc::new(GlobalIdent::from("main"), Label::from(LocalIdent::from("0")), 0);
            let src = new_type(srcinput, &loc, &mut env, &typeset);
            let dst = new_type(dstinput, &loc, &mut env, &typeset);
            let reason = Constr::Cast(src, dst);
            let got = match reason.try_to_cast_reason(&env) {
                Some(reason) => format!("Some({:?})", reason),
                None => format!("None"),
            };
            assert_eq!(expected, got, "({}, {})", srcinput, dstinput);
        }
        for (expected, dstinput, srcinput) in vec![(
            "Some(load i32 from *<?8>!tuple2-tag.cast-target@1+0)",
            "i32",
            "%tuple2-cast-target*",
        )] {
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let dst = new_type(dstinput, &loc, &mut env, &typeset);
            let src = new_type(srcinput, &loc, &mut env, &typeset);
            let reason = Constr::Load(dst, src);
            let got = match reason.try_to_cast_reason(&env) {
                Some(reason) => format!("Some({:?})", reason),
                None => format!("None"),
            };
            assert_eq!(expected, got, "({}, {})", dstinput, srcinput);
        }
        for (expected, dstinput, srcinput, len) in vec![
            (
                "Some(memcpy *<?10>!tuple2-tag.cast-target@1+0 to *<?9>!tuple2-tag.cast-target@1+0 with length 8)",
                "%tuple2-cast-target*",
                "%tuple2-cast-target*",
                Size::Const(8),
            ),
            (
                "Some(load i32 from *<?12>!tuple2-tag.cast-target@1+0)",
                "i32*",
                "%tuple2-cast-target*",
                Size::Const(4),
            ),
            (
                "Some(store i32 to *<?13>!tuple2-tag.cast-target@1+0)",
                "%tuple2-cast-target*",
                "i32*",
                Size::Const(4),
            ),
        ] {
            let loc = Loc::new(GlobalIdent::from("main"), Label::from(LocalIdent::from("0")), 0);
            let dst = new_type(dstinput, &loc, &mut env, &typeset);
            let src = new_type(srcinput, &loc, &mut env, &typeset);
            let reason = Constr::Memcpy(dst, src, len);
            let got = match reason.try_to_cast_reason(&env) {
                Some(reason) => format!("Some({:?})", reason),
                None => format!("None"),
            };
            assert_eq!(expected, got, "({}, {}, {:?})", dstinput, srcinput, len);
        }
        for (expected, srcinput, dstinput) in vec![(
            "Some(store i32 to *<?15>!tuple2-tag.cast-target@1+0)",
            "i32",
            "%tuple2-cast-target*",
        )] {
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let src = new_type(srcinput, &loc, &mut env, &typeset);
            let dst = new_type(dstinput, &loc, &mut env, &typeset);
            let reason = Constr::Store(src, dst);
            let got = match reason.try_to_cast_reason(&env) {
                Some(reason) => format!("Some({:?})", reason),
                None => format!("None"),
            };
            assert_eq!(expected, got, "({}, {})", srcinput, dstinput);
        }
    }
}
