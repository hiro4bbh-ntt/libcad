//! The syntax of LLIR.

use super::parser::Parser;
use crate::fmt::DisplayIter;
use crate::llir::abi::DataLayout;
use crate::ops::TotallyComparable;
use crate::reader::sexpr::SExpr;
use crate::symbol::{gensym, symget, Symbol};
use std::collections::BTreeMap;
use std::fmt;

fn ident_is_quoted(s: &str) -> bool {
    !s.chars()
        .all(|c| c == '$' || c == '-' || c == '.' || c.is_alphanumeric() || c == '_')
}

/// A local identifier (<https://llvm.org/docs/LangRef.html#identifiers>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LocalIdent(pub Symbol);

impl LocalIdent {
    /// Returns a string of the name.
    pub fn get(&self) -> String {
        symget(self.0).unwrap()
    }
    /// Returns `true` if quoted.
    pub fn is_quoted(&self) -> bool {
        ident_is_quoted(&self.get())
    }
}

impl From<&str> for LocalIdent {
    fn from(s: &str) -> LocalIdent {
        LocalIdent::from(String::from(s))
    }
}

impl From<String> for LocalIdent {
    fn from(s: String) -> LocalIdent {
        LocalIdent(gensym(s))
    }
}

impl<'a> fmt::Display for LocalIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.is_quoted() {
            true => write!(f, "%{:?}", self.get()),
            false => write!(f, "%{}", self.get()),
        }
    }
}

/// A global identifier (<https://llvm.org/docs/LangRef.html#identifiers>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GlobalIdent(pub Symbol);

impl GlobalIdent {
    /// Returns a string of the name.
    pub fn get(&self) -> String {
        symget(self.0).unwrap()
    }
    /// Returns `true` if quoted.
    pub fn is_quoted(&self) -> bool {
        ident_is_quoted(&self.get())
    }
    /// Returns `true` if representing a LLVM debug intrinsic.
    pub fn is_dbg_intr(&self) -> bool {
        matches!(
            self,
            global_ident!("llvm.dbg.declare")
                | global_ident!("llvm.dbg.label")
                | global_ident!("llvm.dbg.value")
        )
    }
}

impl From<&str> for GlobalIdent {
    fn from(s: &str) -> GlobalIdent {
        GlobalIdent::from(String::from(s))
    }
}

impl From<String> for GlobalIdent {
    fn from(s: String) -> GlobalIdent {
        GlobalIdent(gensym(s))
    }
}

impl<'a> fmt::Display for GlobalIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.is_quoted() {
            true => write!(f, "@{:?}", self.get()),
            false => write!(f, "@{}", self.get()),
        }
    }
}

/// A trait for an extension identifier.
pub trait ExtIdent: TotallyComparable {}

impl<T: TotallyComparable> ExtIdent for T {}

/// The unit extension identifier.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExtIdentUnit();

impl<'a> fmt::Display for ExtIdentUnit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "!()")
    }
}

/// A type (<https://llvm.org/docs/LangRef.html#type-system>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Type<I: ExtIdent> {
    Void,
    I1,
    I8,
    I16,
    I32,
    I64,
    Float,
    Double,
    X86Fp80,
    Ptr(Box<Type<I>>),
    Vector(bool, u32, Box<Type<I>>),
    Array(u32, Box<Type<I>>),
    Struct(bool, Vec<Type<I>>),
    Opaque,
    Func(FuncSig<I>),
    Name(LocalIdent),
    Metadata,
    Ext(I, Box<Type<I>>),
}

impl<I: ExtIdent> Type<I> {
    /// Returns a parsed type from the given S-expression.
    pub fn try_from_sexpr(sexpr: &SExpr) -> Result<Type<I>, String> {
        match sexpr {
            SExpr::Symbol(ident!("void")) => Ok(Type::Void),
            SExpr::Symbol(ident!("i1")) => Ok(Type::I1),
            SExpr::Symbol(ident!("i8")) => Ok(Type::I8),
            SExpr::Symbol(ident!("i16")) => Ok(Type::I16),
            SExpr::Symbol(ident!("i32")) => Ok(Type::I32),
            SExpr::Symbol(ident!("i64")) => Ok(Type::I64),
            SExpr::Symbol(ident!("float")) => Ok(Type::Float),
            SExpr::Symbol(ident!("double")) => Ok(Type::Double),
            SExpr::String(name) => Ok(Type::Name(LocalIdent::from(name.clone()))),
            _ => match sexpr.try_to_cmd() {
                Some((ident!("ptr"), args)) if args.len() == 1 => {
                    Ok(Type::Ptr(Box::new(Type::try_from_sexpr(&args[0])?)))
                }
                Some((kind @ ident!("func"), args)) | Some((kind @ ident!("varfunc"), args))
                    if !args.is_empty() =>
                {
                    let retty = Type::try_from_sexpr(&args[0])?;
                    let mut argtys = Vec::with_capacity(args.len() - 1);
                    for arg in args[1..].iter() {
                        argtys.push(Param::from(Type::try_from_sexpr(arg)?));
                    }
                    Ok(Type::Func(FuncSig {
                        ret: Box::new(RetParam::from(retty)),
                        name: None,
                        args: argtys,
                        variadic: kind == ident!("varfunc"),
                    }))
                }
                _ => Err(format!("malformed LLIR type {}", sexpr)),
            },
        }
    }
    /// Returns `true` if the type is of integers.
    pub fn is_int(&self) -> bool {
        matches!(
            self,
            Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64
        )
    }
    /// Returns the type resolving the type names.
    pub fn normalize<'a, 'b>(&'a self, typedefs: &'b Typedefs<I>) -> Result<&'b Type<I>, String>
    where
        'a: 'b,
    {
        match self {
            Type::Name(name) => match typedefs.get(name) {
                Some(ty) => ty.normalize(typedefs),
                None => Err(format!("type {} is not found", name)),
            },
            _ => Ok(self),
        }
    }
}

impl<I: ExtIdent> fmt::Display for Type<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::I1 => write!(f, "i1"),
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::Float => write!(f, "float"),
            Type::Double => write!(f, "double"),
            Type::X86Fp80 => write!(f, "x86_fp80"),
            Type::Ptr(ty) => write!(f, "{}*", ty),
            Type::Vector(vscale, size, ty) => {
                write!(f, "<")?;
                if *vscale {
                    write!(f, "vscale x ")?;
                }
                write!(f, "{} x {}>", size, ty)
            }
            Type::Array(size, ty) => write!(f, "[{} x {}]", size, ty),
            Type::Struct(packed, fields) => {
                if *packed {
                    write!(f, "<")?;
                }
                write!(f, "{}", DisplayIter("{ ", fields.iter(), ", ", " }"))?;
                if *packed {
                    write!(f, ">")?;
                }
                Ok(())
            }
            Type::Opaque => write!(f, "opaque"),
            Type::Func(sig) => write!(f, "{}", sig),
            Type::Name(name) => write!(f, "{}", name),
            Type::Metadata => write!(f, "metadata"),
            Type::Ext(eid, orig) => write!(f, "{}({})", eid, orig),
        }
    }
}

/// An argument of [`ParamAttr`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ParamAttrArg<I: ExtIdent> {
    Type(Type<I>),
    U32(u32),
}

impl<I: ExtIdent> fmt::Display for ParamAttrArg<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParamAttrArg::Type(ty) => write!(f, "{}", ty),
            ParamAttrArg::U32(n) => write!(f, "{}", n),
        }
    }
}

/// An entry of [`ParamAttrs`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParamAttr<I: ExtIdent>(pub String, pub Option<ParamAttrArg<I>>);

impl<I: ExtIdent> fmt::Display for ParamAttr<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)?;
        if let Some(arg) = &self.1 {
            write!(f, "({})", arg)?;
        }
        Ok(())
    }
}

/// Parameter attributes (<https://llvm.org/docs/LangRef.html#parameter-attributes>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParamAttrs<I: ExtIdent>(Vec<ParamAttr<I>>);

impl<I: ExtIdent> ParamAttrs<I> {
    /// Returns new parameter attributes.
    pub fn new(attrs: Vec<ParamAttr<I>>) -> ParamAttrs<I> {
        ParamAttrs(attrs)
    }
    /// Returns the length.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<I: ExtIdent> fmt::Display for ParamAttrs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", DisplayIter("", self.0.iter(), " ", ""))
    }
}

/// A parameter (<https://llvm.org/docs/LangRef.html#functions>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Param<I: ExtIdent> {
    pub ty: Type<I>,
    pub attrs: ParamAttrs<I>,
    pub name: Option<LocalIdent>,
}

impl<I: ExtIdent> Param<I> {
    /// Returns the name if set, panics otherwise.
    pub fn expect_name(&self) -> LocalIdent {
        match &self.name {
            Some(name) => *name,
            None => panic!("param name must be defined"),
        }
    }
}

impl<I: ExtIdent> From<Type<I>> for Param<I> {
    fn from(ty: Type<I>) -> Self {
        Param {
            ty,
            attrs: ParamAttrs(Vec::new()),
            name: None,
        }
    }
}

impl<I: ExtIdent> fmt::Display for Param<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.ty)?;
        if !(self.attrs).is_empty() {
            write!(f, " {}", self.attrs)?;
        }
        if let Some(name) = &self.name {
            write!(f, " {}", name)?;
        }
        Ok(())
    }
}

/// A return parameter (<https://llvm.org/docs/LangRef.html#functions>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RetParam<I: ExtIdent> {
    pub attrs: ParamAttrs<I>,
    pub ty: Type<I>,
}

impl<I: ExtIdent> From<Type<I>> for RetParam<I> {
    fn from(ty: Type<I>) -> Self {
        RetParam {
            attrs: ParamAttrs(Vec::new()),
            ty,
        }
    }
}

impl<I: ExtIdent> fmt::Display for RetParam<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.attrs.is_empty() {
            write!(f, "{} ", self.attrs)?;
        }
        write!(f, "{}", self.ty)
    }
}

/// A signature of a function (<https://llvm.org/docs/LangRef.html#functions>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FuncSig<I: ExtIdent> {
    pub ret: Box<RetParam<I>>,
    pub name: Option<GlobalIdent>,
    pub args: Vec<Param<I>>,
    pub variadic: bool,
}

impl<I: ExtIdent> FuncSig<I> {
    /// Returns the name if set, panics otherwise.
    pub fn expect_name(&self) -> GlobalIdent {
        match &self.name {
            Some(name) => *name,
            None => panic!("func name must be defined"),
        }
    }
    /// Returns the names of the arguments.
    pub fn argnames(&self) -> Vec<LocalIdent> {
        let mut argnames = Vec::with_capacity(self.args.len());
        for (i, Param { name, .. }) in self.args.iter().enumerate() {
            argnames.push(match name {
                Some(name) => *name,
                None => LocalIdent::from(format!("{}", i)),
            });
        }
        argnames
    }
}

impl<I: ExtIdent> fmt::Display for FuncSig<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ", self.ret)?;
        if let Some(name) = &self.name {
            write!(f, "{}", name)?;
        }
        write!(f, "({}", DisplayIter("", self.args.iter(), ", ", ""))?;
        if self.variadic {
            if !self.args.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "...")?;
        }
        write!(f, ")")
    }
}

/// An aggregate operation (<https://llvm.org/docs/LangRef.html#aggregate-operations>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AggOpArgs<I: ExtIdent> {
    Extractvalue(TypedValue<I>, Vec<u32>),
    Insertvalue(TypedValue<I>, TypedValue<I>, Vec<u32>),
}

impl<I: ExtIdent> fmt::Display for AggOpArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AggOpArgs::Extractvalue(val, idx) => {
                let idx = DisplayIter("", idx.iter(), ", ", "");
                write!(f, "extractvalue ({}, {})", val, idx)
            }
            AggOpArgs::Insertvalue(val, elt, idx) => {
                let idx = DisplayIter("", idx.iter(), ", ", "");
                write!(f, "insertvalue ({}, {}, {})", val, elt, idx)
            }
        }
    }
}

/// A wrap mode of [`BinOpcode`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WrapMode {
    Nuw,
    Nsw,
    NuwNsw,
}

impl fmt::Display for WrapMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            WrapMode::Nuw => write!(f, "nuw"),
            WrapMode::Nsw => write!(f, "nsw"),
            WrapMode::NuwNsw => write!(f, "nuw nsw"),
        }
    }
}

/// An opcode of [`BinOpArgs`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BinOpcode {
    Add(Option<WrapMode>),
    And,
    Ashr(bool),
    Fadd,
    Fdiv,
    Fmul,
    Frem,
    Fsub,
    Lshr(bool),
    Mul(Option<WrapMode>),
    Or,
    Sdiv(bool),
    Shl(Option<WrapMode>),
    Srem,
    Sub(Option<WrapMode>),
    Udiv(bool),
    Urem,
    Xor,
}

impl fmt::Display for BinOpcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinOpcode::Add(None) => write!(f, "add"),
            BinOpcode::Add(Some(wrap_mode)) => write!(f, "add {}", wrap_mode),
            BinOpcode::And => write!(f, "and"),
            BinOpcode::Ashr(false) => write!(f, "ashr"),
            BinOpcode::Ashr(true) => write!(f, "ashr exact"),
            BinOpcode::Fadd => write!(f, "fadd"),
            BinOpcode::Fdiv => write!(f, "fdiv"),
            BinOpcode::Fmul => write!(f, "fmul"),
            BinOpcode::Frem => write!(f, "frem"),
            BinOpcode::Fsub => write!(f, "fsub"),
            BinOpcode::Lshr(false) => write!(f, "lshr"),
            BinOpcode::Lshr(true) => write!(f, "lshr exact"),
            BinOpcode::Mul(None) => write!(f, "mul"),
            BinOpcode::Mul(Some(wrap_mode)) => write!(f, "mul {}", wrap_mode),
            BinOpcode::Or => write!(f, "or"),
            BinOpcode::Sdiv(false) => write!(f, "sdiv"),
            BinOpcode::Sdiv(true) => write!(f, "sdiv exact"),
            BinOpcode::Shl(None) => write!(f, "shl"),
            BinOpcode::Shl(Some(wrap_mode)) => write!(f, "shl {}", wrap_mode),
            BinOpcode::Srem => write!(f, "srem"),
            BinOpcode::Sub(None) => write!(f, "sub"),
            BinOpcode::Sub(Some(wrap_mode)) => write!(f, "sub {}", wrap_mode),
            BinOpcode::Udiv(false) => write!(f, "udiv"),
            BinOpcode::Udiv(true) => write!(f, "udiv exact"),
            BinOpcode::Urem => write!(f, "urem"),
            BinOpcode::Xor => write!(f, "xor"),
        }
    }
}

/// Arguments of binary operation (<https://llvm.org/docs/LangRef.html#binary-operations>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinOpArgs<I: ExtIdent> {
    pub opcode: BinOpcode,
    pub left: TypedValue<I>,
    pub right: TypedValue<I>,
}

impl<I: ExtIdent> fmt::Display for BinOpArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({}, {})", self.opcode, self.left, self.right)
    }
}

/// A condition of `icmp` (<https://llvm.org/docs/LangRef.html#icmp-instruction>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum IcmpCond {
    Eq,
    Ne,
    Ugt,
    Uge,
    Ult,
    Ule,
    Sgt,
    Sge,
    Slt,
    Sle,
}

impl IcmpCond {
    /// Returns the condition representing negation.
    pub fn negate(&self) -> IcmpCond {
        match self {
            IcmpCond::Eq => IcmpCond::Ne,
            IcmpCond::Ne => IcmpCond::Eq,
            IcmpCond::Ugt => IcmpCond::Ule,
            IcmpCond::Uge => IcmpCond::Ult,
            IcmpCond::Ult => IcmpCond::Uge,
            IcmpCond::Ule => IcmpCond::Ugt,
            IcmpCond::Sgt => IcmpCond::Sle,
            IcmpCond::Sge => IcmpCond::Slt,
            IcmpCond::Slt => IcmpCond::Sge,
            IcmpCond::Sle => IcmpCond::Sgt,
        }
    }
}

impl fmt::Display for IcmpCond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_lowercase())
    }
}

/// A condition of `fcmp` (<https://llvm.org/docs/LangRef.html#fcmp-instruction>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FcmpCond {
    False,
    Oeq,
    Ogt,
    Oge,
    Olt,
    Ole,
    One,
    Ord,
    Ueq,
    Ugt,
    Uge,
    Ult,
    Ule,
    Une,
    Uno,
    True,
}

impl fmt::Display for FcmpCond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_lowercase())
    }
}

/// An opcode of [`CmpOpArgs`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CmpOpcode {
    Fcmp(FcmpCond),
    Icmp(IcmpCond),
}

impl fmt::Display for CmpOpcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CmpOpcode::Icmp(cond) => write!(f, "icmp {}", cond),
            CmpOpcode::Fcmp(cond) => write!(f, "fcmp {}", cond),
        }
    }
}

/// Arguments of a comparison operation.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CmpOpArgs<I: ExtIdent> {
    pub opcode: CmpOpcode,
    pub left: TypedValue<I>,
    pub right: TypedValue<I>,
}

impl<I: ExtIdent> fmt::Display for CmpOpArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({}, {})", self.opcode, self.left, self.right)
    }
}

/// A opcode of [`ConvOpArgs`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ConvOpcode {
    Bitcast,
    Fpext,
    Fptosi,
    Fptoui,
    Fptrunc,
    Inttoptr,
    Ptrtoint,
    Sext,
    Sitofp,
    Trunc,
    Uitofp,
    Zext,
}

impl fmt::Display for ConvOpcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_lowercase())
    }
}

/// Arguments of a conversion operation (<https://llvm.org/docs/LangRef.html#conversion-operations>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConvOpArgs<I: ExtIdent> {
    pub opcode: ConvOpcode,
    pub srctyval: TypedValue<I>,
    pub dstty: Type<I>,
}

impl<I: ExtIdent> fmt::Display for ConvOpArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({} to {})", self.opcode, self.srctyval, self.dstty)
    }
}

/// Arguments of `getelementptr` operation (<https://llvm.org/docs/LangRef.html#getelementptr-instruction>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GetelementptrArgs<I: ExtIdent> {
    pub inbounds: bool,
    pub base_ty: Type<I>,
    pub base_ptr: TypedValue<I>,
    pub indices: Vec<(bool, TypedValue<I>)>,
}

impl<I: ExtIdent> fmt::Display for GetelementptrArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "getelementptr")?;
        if self.inbounds {
            write!(f, " inbounds")?;
        }
        write!(f, " ({}, {}", self.base_ty, self.base_ptr)?;
        for index in &self.indices {
            write!(f, ", ")?;
            if index.0 {
                write!(f, "inrange ")?;
            }
            write!(f, "{}", index.1)?;
        }
        write!(f, ")")
    }
}

/// An opcode of [`UnOpArgs`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UnOpcode {
    Fneg,
}

impl fmt::Display for UnOpcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnOpcode::Fneg => write!(f, "fneg"),
        }
    }
}

/// Arguments of a unary operation (<https://llvm.org/docs/LangRef.html#unary-operations>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UnOpArgs<I: ExtIdent> {
    pub opcode: UnOpcode,
    pub tyval: TypedValue<I>,
}

impl<I: ExtIdent> fmt::Display for UnOpArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({})", self.opcode, self.tyval)
    }
}

/// Arguments of a vector operation (<https://llvm.org/docs/LangRef.html#vector-operations>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum VecOpArgs<I: ExtIdent> {
    Extractelement(TypedValue<I>, TypedValue<I>),
    Insertelement(TypedValue<I>, TypedValue<I>, TypedValue<I>),
    Shufflevector(TypedValue<I>, TypedValue<I>, TypedValue<I>),
}

impl<I: ExtIdent> fmt::Display for VecOpArgs<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            VecOpArgs::Extractelement(val, idx) => write!(f, "extractelement ({}, {})", val, idx),
            VecOpArgs::Insertelement(val, elt, idx) => {
                write!(f, "insertelement ({}, {}, {})", val, elt, idx)
            }
            VecOpArgs::Shufflevector(v1, v2, mask) => {
                write!(f, "shufflevector ({}, {}, {})", v1, v2, mask)
            }
        }
    }
}

/// A value (<https://llvm.org/docs/LangRef.html#constants>, <https://llvm.org/docs/LangRef.html#other-values>).
/// This also contains the composable instructions without side effects.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Value<I: ExtIdent> {
    Null,
    Undef,
    False,
    True,
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    Float(String),
    Double(String),
    X86Fp80(String),
    Vector(Vec<TypedValue<I>>),
    ArrayConst(String),
    Array(Vec<TypedValue<I>>),
    Struct(bool, Vec<TypedValue<I>>),
    LocalRef(LocalIdent),
    GlobalRef(GlobalIdent),
    AggOp(Box<AggOpArgs<I>>),
    BinOp(Box<BinOpArgs<I>>),
    CmpOp(Box<CmpOpArgs<I>>),
    ConvOp(Box<ConvOpArgs<I>>),
    Getelementptr(Box<GetelementptrArgs<I>>),
    UnOp(Box<UnOpArgs<I>>),
    VecOp(Box<VecOpArgs<I>>),
    Zeroinitializer,
    Blockaddress(GlobalIdent, Label),
    Metadata(Box<Metadata<I>>),
}

impl<I: ExtIdent> Value<I> {
    /// Returns a 64-bit integer constant.
    pub fn try_to_i64(&self) -> Option<i64> {
        match self {
            Value::I8(n) => Some(*n as i64),
            Value::I16(n) => Some(*n as i64),
            Value::I32(n) => Some(*n as i64),
            Value::I64(n) => Some(*n),
            _ => None,
        }
    }
    /// Returns a 64-bit integer constant, and panics if not.
    pub fn to_i64(&self) -> i64 {
        self.try_to_i64()
            .unwrap_or_else(|| panic!("expected const value, but got {}", self))
    }
    /// Returns the local identifier of the base variable.
    pub fn local_base(&self) -> Option<LocalIdent> {
        match self {
            Value::LocalRef(name) => Some(*name),
            Value::ConvOp(args) => args.srctyval.1.local_base(),
            Value::Getelementptr(args) => args.base_ptr.1.local_base(),
            _ => None,
        }
    }
}

impl<I: ExtIdent> fmt::Display for Value<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Null => write!(f, "null"),
            Value::Undef => write!(f, "undef"),
            Value::False => write!(f, "false"),
            Value::True => write!(f, "true"),
            Value::I8(n) => write!(f, "{}", n),
            Value::I16(n) => write!(f, "{}", n),
            Value::I32(n) => write!(f, "{}", n),
            Value::I64(n) => write!(f, "{}", n),
            Value::Float(x) => write!(f, "{}", x),
            Value::Double(x) => write!(f, "{}", x),
            Value::X86Fp80(x) => write!(f, "{}", x),
            Value::Vector(fields) => write!(f, "{}", DisplayIter("<", fields.iter(), ", ", ">")),
            Value::ArrayConst(c) => write!(f, "c{:?}", c),
            Value::Array(fields) => write!(f, "{}", DisplayIter("[", fields.iter(), ", ", "]")),
            Value::Struct(packed, fields) => {
                if *packed {
                    write!(f, "<")?;
                }
                write!(f, "{}", DisplayIter("{ ", fields.iter(), ", ", " }"))?;
                if *packed {
                    write!(f, ">")?;
                }
                Ok(())
            }
            Value::LocalRef(name) => write!(f, "{}", name),
            Value::GlobalRef(name) => write!(f, "{}", name),
            Value::AggOp(args) => write!(f, "{}", args),
            Value::BinOp(args) => write!(f, "{}", args),
            Value::CmpOp(args) => write!(f, "{}", args),
            Value::ConvOp(args) => write!(f, "{}", args),
            Value::Getelementptr(args) => write!(f, "{}", args),
            Value::UnOp(args) => write!(f, "{}", args),
            Value::VecOp(args) => write!(f, "{}", args),
            Value::Zeroinitializer => write!(f, "zeroinitializer"),
            Value::Blockaddress(name, label) => write!(f, "blockaddress({}, {})", name, label.0),
            Value::Metadata(md) => write!(f, "{}", md),
        }
    }
}

/// A typed value.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypedValue<I: ExtIdent>(pub Type<I>, pub Value<I>);

impl<I: ExtIdent> fmt::Display for TypedValue<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

/// A parameter value.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParamValue<I: ExtIdent>(pub Param<I>, pub Value<I>);

impl<I: ExtIdent> fmt::Display for ParamValue<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

/// A label.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Label(LocalIdent);

impl Label {
    /// Returns the local identifier.
    pub fn localident(&self) -> LocalIdent {
        self.0
    }
}

impl From<LocalIdent> for Label {
    fn from(ident: LocalIdent) -> Label {
        Label(ident)
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "label {}", self.0)
    }
}

/// A tail call mode of `call` instruction (<https://llvm.org/docs/LangRef.html#call-instruction>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TailMode {
    Musttail,
    Notail,
    Tail,
}

impl fmt::Display for TailMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_lowercase())
    }
}

/// A calling convention of [`CallBody`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CallConv {
    Fastcc,
}

impl fmt::Display for CallConv {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_lowercase())
    }
}

/// A callee value of `call` instruction (<https://llvm.org/docs/LangRef.html#call-instruction>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Callee<I: ExtIdent> {
    Value(Value<I>),
    Asm(String, String),
}

impl<I: ExtIdent> fmt::Display for Callee<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Callee::Value(val) => write!(f, "{}", val),
            Callee::Asm(tmpl, constr) => write!(f, "asm {:?}, {:?}", tmpl, constr),
        }
    }
}

/// A clause of `landingpad` instruction (<https://llvm.org/docs/LangRef.html#landingpad-instruction>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LandingpadClause<I: ExtIdent> {
    Catch(TypedValue<I>),
    Filter(TypedValue<I>),
}

impl<I: ExtIdent> fmt::Display for LandingpadClause<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LandingpadClause::Catch(tyval) => write!(f, "catch {}", tyval),
            LandingpadClause::Filter(tyval) => write!(f, "filter {}", tyval),
        }
    }
}

/// An entry of an attribute group (<https://llvm.org/docs/LangRef.html#attribute-groups>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Attr<I: ExtIdent> {
    ParamAttr(ParamAttr<I>),
    Key(String),
    KeyValue(String, String),
    Ref(u32),
}

impl<I: ExtIdent> fmt::Display for Attr<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Attr::ParamAttr(attr) => write!(f, "{}", attr),
            Attr::Key(key) => write!(f, "{:?}", key),
            Attr::KeyValue(key, value) => write!(f, "{:?}={:?}", key, value),
            Attr::Ref(id) => write!(f, "#{}", id),
        }
    }
}

/// An argument body of `call` instruction (<https://llvm.org/docs/LangRef.html#call-instruction>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CallBody<I: ExtIdent> {
    pub call_conv: Option<CallConv>,
    pub ret: RetParam<I>,
    pub callee: Callee<I>,
    pub args: Vec<ParamValue<I>>,
    pub attrs: Vec<Attr<I>>,
}

impl<I: ExtIdent> fmt::Display for CallBody<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let Some(call_conv) = &self.call_conv {
            write!(f, "{} ", call_conv)?;
        }
        write!(
            f,
            "{} {}{}",
            self.ret,
            self.callee,
            DisplayIter("(", self.args.iter(), ", ", ")")
        )?;
        for attr in &self.attrs {
            write!(f, " {}", attr)?;
        }
        Ok(())
    }
}

/// An instruction (<https://llvm.org/docs/LangRef.html#instruction-reference>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Insn<I: ExtIdent> {
    Alloca {
        res: LocalIdent,
        ty: Type<I>,
        align: Option<u32>,
    },
    Br(Label),
    BrI1(Value<I>, Label, Label),
    Call {
        res: Option<LocalIdent>,
        tail_mode: Option<TailMode>,
        body: CallBody<I>,
        range: Option<MetadataRef>,
    },
    Indirectbr(TypedValue<I>, Vec<Label>),
    Invoke {
        res: Option<LocalIdent>,
        body: CallBody<I>,
        to: Label,
        unwind: Label,
    },
    Landingpad {
        res: LocalIdent,
        ty: Type<I>,
        cleanup: bool,
        clauses: Vec<LandingpadClause<I>>,
    },
    Load {
        res: LocalIdent,
        volatile: bool,
        ty: Type<I>,
        src: TypedValue<I>,
        align: Option<u32>,
    },
    Phi {
        res: LocalIdent,
        ty: Type<I>,
        val_labels: Vec<(Value<I>, Label)>,
    },
    Resume(TypedValue<I>),
    Ret(Option<TypedValue<I>>),
    Select(LocalIdent, TypedValue<I>, TypedValue<I>, TypedValue<I>),
    Store {
        volatile: bool,
        src: TypedValue<I>,
        dst: TypedValue<I>,
        align: Option<u32>,
    },
    Switch(TypedValue<I>, Label, Vec<(TypedValue<I>, Label)>),
    Unreachable,
    Value(LocalIdent, Value<I>),
}

impl<I: ExtIdent> Insn<I> {
    /// Returns the local identifier of the result variable.
    pub fn res(&self) -> Option<LocalIdent> {
        match self {
            Insn::Alloca { res, .. } => Some(*res),
            Insn::Call { res: Some(res), .. } => Some(*res),
            Insn::Invoke { res: Some(res), .. } => Some(*res),
            Insn::Landingpad { res, .. } => Some(*res),
            Insn::Load { res, .. } => Some(*res),
            Insn::Phi { res, .. } => Some(*res),
            Insn::Select(res, ..) => Some(*res),
            Insn::Value(res, _) => Some(*res),
            _ => None,
        }
    }
}

impl<I: ExtIdent> fmt::Display for Insn<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Insn::Alloca { res, ty, align } => {
                write!(f, "{} = alloca {}", res, ty)?;
                if let Some(align) = align {
                    write!(f, ", align {}", align)?;
                }
                Ok(())
            }
            Insn::Br(label) => write!(f, "br {}", label),
            Insn::BrI1(value, label1, label2) => {
                write!(f, "br i1 {}, {}, {}", value, label1, label2)
            }
            Insn::Call {
                res,
                tail_mode,
                body,
                range,
            } => {
                if let Some(res) = res {
                    write!(f, "{} = ", res)?;
                }
                if let Some(tail_mode) = tail_mode {
                    write!(f, "{} ", tail_mode)?;
                }
                write!(f, "call {}", body)?;
                if let Some(range) = range {
                    write!(f, ", !range {}", range)?;
                }
                Ok(())
            }
            Insn::Indirectbr(tyval, labels) => {
                write!(
                    f,
                    "indirectbr {}, {}",
                    tyval,
                    DisplayIter("[", labels.iter(), ", ", "]")
                )
            }
            Insn::Invoke {
                res,
                body,
                to,
                unwind,
            } => {
                if let Some(res) = res {
                    write!(f, "{} = ", res)?;
                }
                write!(f, "invoke {} to {} unwind {}", body, to, unwind)
            }
            Insn::Landingpad {
                res,
                ty,
                cleanup,
                clauses,
            } => {
                write!(f, "{} = landingpad {}", res, ty)?;
                if *cleanup {
                    write!(f, " cleanup")?;
                }
                for clause in clauses {
                    write!(f, " {}", clause)?;
                }
                Ok(())
            }
            Insn::Load {
                res,
                volatile,
                ty,
                src,
                align,
            } => {
                write!(f, "{} = load ", res)?;
                if *volatile {
                    write!(f, "volatile ")?;
                }
                write!(f, "{}, {}", ty, src)?;
                if let Some(align) = align {
                    write!(f, ", align {}", align)?;
                }
                Ok(())
            }
            Insn::Phi {
                res,
                ty,
                val_labels,
            } => {
                write!(f, "{} = phi {} ", res, ty)?;
                for (i, (val, label)) in val_labels.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "[ {}, {} ]", val, label.0)?;
                }
                Ok(())
            }
            Insn::Resume(tyval) => write!(f, "resume {}", tyval),
            Insn::Ret(None) => write!(f, "ret void"),
            Insn::Ret(Some(tyval)) => write!(f, "ret {}", tyval),
            Insn::Select(res, cond, tyval0, tyval1) => {
                write!(f, "{} = select {}, {}, {}", res, cond, tyval0, tyval1)
            }
            Insn::Store {
                volatile,
                src,
                dst,
                align,
            } => {
                write!(f, "store ")?;
                if *volatile {
                    write!(f, "volatile ")?;
                }
                write!(f, "{}, {}", src, dst)?;
                if let Some(align) = align {
                    write!(f, ", align {}", align)?;
                }
                Ok(())
            }
            Insn::Switch(val, default, cases) => {
                write!(f, "switch {}, {} [", val, default)?;
                for (val, label) in cases {
                    write!(f, " {}, {}", val, label)?;
                }
                write!(f, " ]")
            }
            Insn::Unreachable => write!(f, "unreachable"),
            Insn::Value(res, val) => write!(f, "{} = {}", res, val),
        }
    }
}

/// A linkage type (<https://llvm.org/docs/LangRef.html#linkage-types>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Linkage {
    Common,
    External,
    Internal,
    LinkonceOdr,
    Private,
}

/// A visibility style (<https://llvm.org/docs/LangRef.html#visibility-styles>).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Visibility {
    Default,
    Hidden,
    Protected,
}

/// An `unnamed_addr` specifier (<https://llvm.org/docs/LangRef.html#global-variables>) and [`FuncDecl`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UnnamedAddr {
    None,
    Normal,
    Local,
}

/// A declaration of a function (<https://llvm.org/docs/LangRef.html#functions>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FuncDecl<I: ExtIdent> {
    pub sig: FuncSig<I>,
    pub attrs: Vec<Attr<I>>,
    pub linkages: Vec<Linkage>,
    pub visibility: Visibility,
    pub call_conv: Option<CallConv>,
    pub unnamed_addr: UnnamedAddr,
    pub personality: Option<TypedValue<I>>,
}

/// A metadata reference (<https://llvm.org/docs/LangRef.html#metadata>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MetadataRef(String);

impl MetadataRef {
    /// Returns a new metadata reference.
    pub fn new(name: String) -> MetadataRef {
        MetadataRef(name)
    }
    /// Returns `true` if quoted.
    pub fn is_quoted(&self) -> bool {
        ident_is_quoted(&self.0)
    }
}

impl fmt::Display for MetadataRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.is_quoted() {
            true => write!(f, "!{:?}", self.0),
            false => write!(f, "!{}", self.0),
        }
    }
}

/// A metadata (<https://llvm.org/docs/LangRef.html#metadata>).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Metadata<I: ExtIdent> {
    Null,
    Bool(bool),
    Number(String),
    Keyword(String),
    String(String),
    TypedValue(TypedValue<I>),
    Struct(Vec<Metadata<I>>),
    KeyValues(MetadataRef, BTreeMap<Label, Metadata<I>>),
    Values(MetadataRef, Vec<Metadata<I>>),
    Or(Vec<Metadata<I>>),
    Ref(MetadataRef),
}

impl<I: ExtIdent> Metadata<I> {
    /// Returns the number.
    pub fn try_to_u32(&self) -> Option<u32> {
        if let Metadata::Number(n) = self {
            return n.parse::<u32>().ok();
        }
        None
    }
    /// Returns the string.
    pub fn try_to_string(&self) -> Option<String> {
        if let Metadata::String(s) = self {
            return Some(s.to_string());
        }
        None
    }
    /// Returns the metadata reference.
    pub fn try_to_ref(&self) -> Option<MetadataRef> {
        if let Metadata::Ref(r) = self {
            return Some(r.clone());
        }
        None
    }
    /// Returns a parsed [`DIFile`].
    pub fn try_to_difile(&self) -> Option<DIFile> {
        match self {
            Metadata::KeyValues(MetadataRef(name), kvs) if name == "DIFile" => {
                let filename = kvs.get(&label!("filename"))?.try_to_string()?;
                let directory = kvs.get(&label!("directory"))?.try_to_string()?;
                Some(DIFile {
                    filename,
                    directory,
                })
            }
            _ => None,
        }
    }
    /// Returns a parsed [`DILexicalBlock`].
    pub fn try_to_dilexicalblock(&self) -> Option<DILexicalBlock> {
        match self {
            Metadata::KeyValues(MetadataRef(name), kvs) if name == "DILexicalBlock" => {
                let file = kvs.get(&label!("file"))?.try_to_ref()?;
                Some(DILexicalBlock { file })
            }
            _ => None,
        }
    }
    /// Returns a parsed [`DILexicalBlockFile`].
    pub fn try_to_dilexicalblockfile(&self) -> Option<DILexicalBlockFile> {
        match self {
            Metadata::KeyValues(MetadataRef(name), kvs) if name == "DILexicalBlockFile" => {
                let file = kvs.get(&label!("file"))?.try_to_ref()?;
                Some(DILexicalBlockFile { file })
            }
            _ => None,
        }
    }
    /// Returns a parsed [`DILocation`].
    pub fn try_to_dilocation(&self) -> Option<DILocation> {
        match self {
            Metadata::KeyValues(MetadataRef(name), kvs) if name == "DILocation" => {
                let line = kvs.get(&label!("line"))?.try_to_u32()? as usize;
                let column = kvs.get(&label!("column"))?.try_to_u32()? as usize;
                let scope = kvs.get(&label!("scope"))?.try_to_ref()?;
                Some(DILocation {
                    line,
                    column,
                    scope,
                })
            }
            _ => None,
        }
    }
    /// Returns a parsed [`DISubprogram`].
    pub fn try_to_disubprogram(&self) -> Option<DISubprogram> {
        match self {
            Metadata::KeyValues(MetadataRef(name), kvs) if name == "DISubprogram" => {
                let file = kvs.get(&label!("file"))?.try_to_ref()?;
                Some(DISubprogram { file })
            }
            _ => None,
        }
    }
}

impl<I: ExtIdent> fmt::Display for Metadata<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Metadata::Null => write!(f, "null"),
            Metadata::Bool(b) => write!(f, "{}", b),
            Metadata::Number(n) => write!(f, "{}", n),
            Metadata::Keyword(key) => match ident_is_quoted(key) {
                true => write!(f, "!{:?}", key),
                false => write!(f, "{}", key),
            },
            Metadata::String(s) => write!(f, "{:?}", s),
            Metadata::TypedValue(tyval) => write!(f, "{}", tyval),
            Metadata::Struct(fields) => {
                write!(f, "!{}", DisplayIter("{", fields.iter(), ", ", "}"))
            }
            Metadata::KeyValues(kind, fields) => {
                write!(f, "{}(", kind)?;
                for (i, (key, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", key.0.get(), val)?;
                }
                write!(f, ")")
            }
            Metadata::Values(kind, fields) => {
                write!(f, "{}{}", kind, DisplayIter("(", fields.iter(), ", ", ")"))
            }
            Metadata::Or(list) => write!(f, "{}", DisplayIter("", list.iter(), " | ", "")),
            Metadata::Ref(r) => write!(f, "{}", r),
        }
    }
}

/// A `DIFile` (<https://llvm.org/docs/LangRef.html#difile>).
#[derive(Clone, Debug, PartialEq)]
pub struct DIFile {
    pub filename: String,
    pub directory: String,
}

impl fmt::Display for DIFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "!DIFile(filename: {}", self.filename)?;
        write!(f, ", directory: {})", self.directory)
    }
}

/// A `DILexicalBlock` (<https://llvm.org/docs/LangRef.html#dilexicalblock>).
#[derive(Clone, Debug, PartialEq)]
pub struct DILexicalBlock {
    pub file: MetadataRef,
}

impl fmt::Display for DILexicalBlock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "!DILexicalBlock(file: {})", self.file)
    }
}

/// A `DILexicalBlockFile` (<https://llvm.org/docs/LangRef.html#dilexicalblockfile>).
#[derive(Clone, Debug, PartialEq)]
pub struct DILexicalBlockFile {
    pub file: MetadataRef,
}

impl fmt::Display for DILexicalBlockFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "!DILexicalBlockFile(file: {})", self.file)
    }
}

/// A `DILocation` (<https://llvm.org/docs/LangRef.html#dilocation>).
#[derive(Clone, Debug, PartialEq)]
pub struct DILocation {
    pub line: usize,
    pub column: usize,
    pub scope: MetadataRef,
}

impl fmt::Display for DILocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "!DILocation(line: {}, column: {}, scope: {})",
            self.line, self.column, self.scope
        )
    }
}

/// A `DISubprogram` (<https://llvm.org/docs/LangRef.html#disubprogram>).
#[derive(Clone, Debug, PartialEq)]
pub struct DISubprogram {
    pub file: MetadataRef,
}

impl fmt::Display for DISubprogram {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "!DISubprogram(file: {})", self.file)
    }
}

/// A metadata list that is a map from the string to the metadata reference.
#[derive(Clone, Debug, PartialEq)]
pub struct MetadataList(BTreeMap<String, MetadataRef>);

impl MetadataList {
    /// Returns a new empty metadata list.
    pub fn empty() -> MetadataList {
        MetadataList(BTreeMap::new())
    }
    /// Returns an iterator.
    pub fn iter(&self) -> impl Clone + Iterator<Item = (&String, &MetadataRef)> {
        self.0.iter()
    }
    /// Inserts the metadata reference entry.
    pub fn insert(&mut self, key: String, value: MetadataRef) -> Option<MetadataRef> {
        self.0.insert(key, value)
    }
}

/// A block of [`Blocks`].
#[derive(Clone, Debug, PartialEq)]
pub struct Block<I: ExtIdent> {
    pub name: Label,
    pub preds: Vec<Label>,
    pub succs: Vec<Label>,
    pub insns: Vec<Insn<I>>,
    pub mdlists: Vec<MetadataList>,
}

impl<I: ExtIdent> Block<I> {
    /// Returns a new block with the given ID.
    pub fn new(id: usize) -> Block<I> {
        Block {
            name: Label::from(LocalIdent::from(format!("{}", id))),
            preds: Vec::new(),
            succs: Vec::new(),
            insns: Vec::new(),
            mdlists: Vec::new(),
        }
    }
}

/// A list of blocks of a function body (<https://llvm.org/docs/LangRef.html#functions>).
#[derive(Clone, Debug, PartialEq)]
pub struct Blocks<I: ExtIdent>(Vec<Block<I>>);

impl<I: ExtIdent> Blocks<I> {
    /// Returns a new empty block list.
    pub fn empty() -> Blocks<I> {
        Blocks(Vec::new())
    }
    /// Returns the length.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Returns an iterator.
    pub fn iter(&self) -> impl Iterator<Item = &Block<I>> {
        self.0.iter()
    }
    /// Returns an mutable iterator.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Block<I>> {
        self.0.iter_mut()
    }
    /// Returns the block by index.
    pub fn get(&self, id: usize) -> Option<&Block<I>> {
        self.0.get(id)
    }
    /// Returns the block by name.
    pub fn block(&self, name: &Label) -> Option<&Block<I>> {
        for block in self.iter() {
            if &block.name == name {
                return Some(block);
            }
        }
        None
    }
    /// Pushes the block.
    pub fn push(&mut self, block: Block<I>) {
        self.0.push(block)
    }
}

/// A statement of LLIR.
#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<I: ExtIdent> {
    SourceFilename(String),
    TargetTriple(String),
    TargetDatalayout(String),
    Typedef(LocalIdent, Type<I>),
    Global {
        name: GlobalIdent,
        is_const: bool,
        ty: Type<I>,
        value: Option<Value<I>>,
        linkages: Vec<Linkage>,
        visibility: Visibility,
        unnamed_addr: UnnamedAddr,
        align: Option<u32>,
    },
    Func(FuncDecl<I>, Blocks<I>),
    Attrs(u32, Vec<Attr<I>>),
    Metadata(MetadataRef, bool, Metadata<I>),
}

/// A line number information.
#[derive(Clone, Debug, PartialEq)]
pub struct LineInfo {
    pub directory: String,
    pub filename: String,
    pub line: usize,
    pub column: usize,
}

impl LineInfo {
    /// Returns the path representation.
    pub fn path(&self) -> String {
        format!("{}/{}", self.directory, self.filename)
    }
}

impl fmt::Display for LineInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.path(), self.line, self.column)
    }
}

/// A location of an instruction.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Loc {
    /// The name of the function in which the instruction is.
    pub func: GlobalIdent,
    /// The label of the block in which the instruction is.
    pub block: Label,
    /// The index of the instruction in the block.
    pub insnidx: usize,
}

impl Loc {
    /// Returns a new location.
    pub fn new(func: GlobalIdent, block: Label, insnidx: usize) -> Loc {
        Loc {
            func,
            block,
            insnidx,
        }
    }
    /// Returns `true` if the two locations are in a same block.
    pub fn is_in_same_block(&self, other: &Loc) -> bool {
        self.func == other.func && self.block == other.block
    }
    /// Returns the comparison result of the two location if the two locations are in a same block.
    /// Otherwise, returns `None`.
    pub fn cmp_in_block(&self, other: &Loc) -> Option<isize> {
        if self.is_in_same_block(other) {
            return Some(self.insnidx as isize - other.insnidx as isize);
        }
        None
    }
    /// Returns a new location with the line number information in the module.
    pub fn with_lineinfo<I: ExtIdent>(&self, module: &Module<I>) -> LocLineInfo {
        if self.insnidx >= 1 {
            let lineinfo = module.lineinfo(self);
            return LocLineInfo {
                loc: *self,
                lineinfo,
            };
        }
        LocLineInfo {
            loc: *self,
            lineinfo: None,
        }
    }
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}{}#{}", self.func, (self.block).0, self.insnidx)
    }
}

/// A location of an instruction with a line number information.
#[derive(Clone, PartialEq)]
pub struct LocLineInfo {
    /// The location of the instruction.
    pub loc: Loc,
    /// The line number information.
    pub lineinfo: Option<LineInfo>,
}

impl fmt::Debug for LocLineInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.loc)?;
        match &self.lineinfo {
            Some(lineinfo) => write!(f, "({})", lineinfo),
            None => write!(f, "(??)"),
        }
    }
}

impl fmt::Display for LocLineInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match &self.lineinfo {
            Some(lineinfo) => write!(
                f,
                "{}:{}:{}",
                lineinfo.filename, lineinfo.line, lineinfo.column
            )?,
            None => write!(f, "??")?,
        }
        write!(f, "({})", self.loc.func)
    }
}

/// A typedef list that is a map from the local identifier of the variable to the type.
#[derive(Clone, Debug)]
pub struct Typedefs<I: ExtIdent>(BTreeMap<LocalIdent, Type<I>>);

impl<I: ExtIdent> Typedefs<I> {
    /// Returns a new empty typedef list.
    pub fn empty() -> Typedefs<I> {
        Typedefs(BTreeMap::new())
    }
    /// Returns a new typedef list.
    pub fn new(m: BTreeMap<LocalIdent, Type<I>>) -> Typedefs<I> {
        Typedefs(m)
    }
    /// Returns the length.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Returns the type.
    pub fn get(&self, name: &LocalIdent) -> Option<&Type<I>> {
        self.0.get(name)
    }
    /// Returns an iterator.
    pub fn iter(&self) -> impl Iterator<Item = (&LocalIdent, &Type<I>)> {
        self.0.iter()
    }
    /// Inserts the typedef.
    pub fn insert(&mut self, name: LocalIdent, ty: Type<I>) -> Option<Type<I>> {
        self.0.insert(name, ty)
    }
    fn do_calc_order_in_type(
        &self,
        ty: &Type<I>,
        order: &mut Vec<LocalIdent>,
        included: &mut Vec<LocalIdent>,
    ) -> Result<(), String> {
        match ty {
            Type::Vector(_, _, ty) | Type::Array(_, ty) => {
                self.do_calc_order_in_type(ty, order, included)
            }
            Type::Struct(_, fields) => {
                for field in fields {
                    self.do_calc_order_in_type(field, order, included)?;
                }
                Ok(())
            }
            Type::Name(name) => self.do_calc_order(name, order, included),
            Type::Ext(_, ty) => self.do_calc_order_in_type(ty, order, included),
            _ => Ok(()),
        }
    }
    fn do_calc_order(
        &self,
        name: &LocalIdent,
        order: &mut Vec<LocalIdent>,
        included: &mut Vec<LocalIdent>,
    ) -> Result<(), String> {
        if order.contains(name) {
            return Ok(());
        }
        if included.contains(name) {
            let start = included.iter().position(|n| n == name).unwrap();
            return Err(format!(
                "detected typedef cycle: {} -> {}",
                DisplayIter("", included[start..].iter(), " -> ", ""),
                name,
            ));
        }
        let ty = match self.get(name) {
            Some(ty) => ty,
            None => return Err(format!("type {} is not defined", name)),
        };
        included.push(*name);
        let result = self.do_calc_order_in_type(ty, order, included);
        included.pop();
        order.push(*name);
        result
    }
    /// Returns an initialization order of the variables.
    pub fn calc_order(&self) -> Result<Vec<LocalIdent>, String> {
        let mut order = Vec::new();
        let mut included = Vec::new();
        for (name, _) in self.iter() {
            self.do_calc_order(name, &mut order, &mut included)?;
        }
        Ok(order)
    }
}

/// A module of LLIR.
#[derive(Clone, Debug)]
pub struct Module<I: ExtIdent> {
    source_filename: Option<String>,
    target_datalayout: DataLayout,
    target_triple: Option<String>,
    typedef_order: Vec<LocalIdent>,
    typedefs: Typedefs<I>,
    globals: BTreeMap<GlobalIdent, (Type<I>, Option<Value<I>>)>,
    funcs: BTreeMap<GlobalIdent, (FuncDecl<I>, Blocks<I>)>,
    attr_groups: BTreeMap<u32, Vec<Attr<I>>>,
    metadata_list: BTreeMap<MetadataRef, Metadata<I>>,
}

impl<I: ExtIdent> Module<I> {
    /// Returns a parsed module from the given source text with the file name.
    pub fn parse(source: &str, source_filename: &str) -> Result<Module<I>, String> {
        let mut parser = Parser::new(source, source_filename)?;
        let mut source_filename = None;
        let mut target_datalayout = String::from("");
        let mut target_triple = None;
        let mut typedefs = Typedefs::empty();
        let mut globals = BTreeMap::new();
        let mut funcs = BTreeMap::new();
        let mut attr_groups = BTreeMap::new();
        let mut metadata_list = BTreeMap::new();
        while let Some((stmt, _)) = match parser.parse_stmt() {
            Ok(result) => result,
            Err(err) => return Err(format!("{}: {}", parser.pos(), err)),
        } {
            match stmt {
                Stmt::SourceFilename(name) => {
                    source_filename = Some(name);
                }
                Stmt::TargetDatalayout(value) => {
                    target_datalayout = value;
                }
                Stmt::TargetTriple(value) => {
                    target_triple = Some(value);
                }
                Stmt::Typedef(name, ty) => {
                    typedefs.insert(name, ty);
                }
                Stmt::Global {
                    name, ty, value, ..
                } => {
                    globals.insert(name, (ty, value));
                }
                Stmt::Func(decl, blocks) => {
                    funcs.insert(decl.sig.expect_name(), (decl, blocks));
                }
                Stmt::Attrs(id, attr) => {
                    attr_groups.insert(id, attr);
                }
                Stmt::Metadata(name, _, md) => {
                    metadata_list.insert(name, md);
                }
            }
        }
        Ok(Module {
            source_filename,
            target_datalayout: DataLayout::parse(&target_datalayout)?,
            target_triple,
            typedef_order: typedefs.calc_order()?,
            typedefs,
            globals,
            funcs,
            attr_groups,
            metadata_list,
        })
    }
    /// Returns the source file name.
    pub fn source_filename(&self) -> &Option<String> {
        &self.source_filename
    }
    /// Returns `target datalayout`.
    pub fn target_datalayout(&self) -> &DataLayout {
        &self.target_datalayout
    }
    /// Returns `target triple`.
    pub fn target_triple(&self) -> &Option<String> {
        &self.target_triple
    }
    /// Returns the initialization order of the typedef list.
    pub fn typedef_order(&self) -> &[LocalIdent] {
        &self.typedef_order
    }
    /// Returns the typedef list.
    pub fn typedefs(&self) -> &Typedefs<I> {
        &self.typedefs
    }
    /// Returns the typedef list as mutable.
    pub fn typedefs_mut(&mut self) -> &mut Typedefs<I> {
        &mut self.typedefs
    }
    /// Returns the globals.
    pub fn globals(&self) -> &BTreeMap<GlobalIdent, (Type<I>, Option<Value<I>>)> {
        &self.globals
    }
    /// Returns the functions.
    pub fn funcs(&self) -> &BTreeMap<GlobalIdent, (FuncDecl<I>, Blocks<I>)> {
        &self.funcs
    }
    /// Returns the function by name.
    pub fn func(&self, name: &GlobalIdent) -> Option<&(FuncDecl<I>, Blocks<I>)> {
        self.funcs.get(name)
    }
    /// Returns the attribute groups.
    pub fn attr_groups(&self) -> &BTreeMap<u32, Vec<Attr<I>>> {
        &self.attr_groups
    }
    /// Returns the metadata list.
    pub fn metadata_list(&self) -> &BTreeMap<MetadataRef, Metadata<I>> {
        &self.metadata_list
    }
    /// Returns the instruction by location.
    pub fn insn(&self, loc: &Loc) -> Option<(&Insn<I>, &MetadataList)> {
        let (_, blocks) = self.func(&loc.func)?;
        for block in blocks.iter() {
            if block.name == loc.block {
                let insn = block.insns.get(loc.insnidx - 1)?;
                let mdlist = block.mdlists.get(loc.insnidx - 1)?;
                return Some((insn, mdlist));
            }
        }
        None
    }
    /// Returns the line number information at the location.
    pub fn lineinfo(&self, loc: &Loc) -> Option<LineInfo> {
        let (_, mdlist) = self.insn(loc)?;
        for (_, mdname) in mdlist.iter() {
            if let Some(md) = self.metadata_list.get(mdname) {
                let diloc = md.try_to_dilocation()?;
                let mdscope = self.metadata_list.get(&diloc.scope)?;
                let mdname_file = if let Some(di) = mdscope.try_to_disubprogram() {
                    di.file
                } else if let Some(di) = mdscope.try_to_dilexicalblock() {
                    di.file
                } else if let Some(di) = mdscope.try_to_dilexicalblockfile() {
                    di.file
                } else {
                    return None;
                };
                let difile = self.metadata_list.get(&mdname_file)?.try_to_difile()?;
                return Some(LineInfo {
                    directory: difile.directory,
                    filename: difile.filename,
                    line: diloc.line,
                    column: diloc.column,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn format_local_ident() {
        assert_eq!(
            "%class.Class0",
            LocalIdent::from("class.Class0").to_string()
        );
        assert_eq!(
            r#"%"union.Object::Value""#,
            LocalIdent::from("union.Object::Value").to_string()
        );
    }
    #[test]
    fn format_global_ident() {
        assert_eq!("@_ZTV6Class0", GlobalIdent::from("_ZTV6Class0").to_string());
        assert_eq!(
            r#"@"class.std::exception""#,
            GlobalIdent::from("class.std::exception").to_string()
        );
    }
    #[test]
    fn format_type() {
        assert_eq!("void", Type::<ExtIdentUnit>::Void.to_string());
        assert_eq!("i1", Type::<ExtIdentUnit>::I1.to_string());
        assert_eq!("i8", Type::<ExtIdentUnit>::I8.to_string());
        assert_eq!("i16", Type::<ExtIdentUnit>::I16.to_string());
        assert_eq!("i32", Type::<ExtIdentUnit>::I32.to_string());
        assert_eq!("i64", Type::<ExtIdentUnit>::I64.to_string());
        assert_eq!("float", Type::<ExtIdentUnit>::Float.to_string());
        assert_eq!("double", Type::<ExtIdentUnit>::Double.to_string());
        assert_eq!("x86_fp80", Type::<ExtIdentUnit>::X86Fp80.to_string());
        assert_eq!(
            "i32*",
            Type::<ExtIdentUnit>::Ptr(Box::new(Type::I32)).to_string()
        );
        assert_eq!(
            "<4 x i64>",
            Type::<ExtIdentUnit>::Vector(false, 4, Box::new(Type::I64)).to_string()
        );
        assert_eq!(
            "<vscale x 4 x i64>",
            Type::<ExtIdentUnit>::Vector(true, 4, Box::new(Type::I64)).to_string()
        );
        assert_eq!(
            "[24 x i8]",
            Type::<ExtIdentUnit>::Array(24, Box::new(Type::I8)).to_string()
        );
        assert_eq!(
            "{ i32 }",
            Type::<ExtIdentUnit>::Struct(false, vec![Type::I32]).to_string()
        );
        assert_eq!(
            "{ i32, i64 }",
            Type::<ExtIdentUnit>::Struct(false, vec![Type::I32, Type::I64]).to_string()
        );
        assert_eq!(
            "<{ i32, i64 }>",
            Type::<ExtIdentUnit>::Struct(true, vec![Type::I32, Type::I64]).to_string()
        );
        assert_eq!("opaque", Type::<ExtIdentUnit>::Opaque.to_string());
        assert_eq!(
            "i32 ()",
            Type::<ExtIdentUnit>::Func(FuncSig {
                ret: Box::new(RetParam {
                    attrs: ParamAttrs(vec![]),
                    ty: Type::I32
                }),
                name: None,
                args: vec![],
                variadic: false
            })
            .to_string()
        );
        assert_eq!(
            "i32 (...)",
            Type::<ExtIdentUnit>::Func(FuncSig {
                ret: Box::new(RetParam {
                    attrs: ParamAttrs(vec![]),
                    ty: Type::I32
                }),
                name: None,
                args: vec![],
                variadic: true
            })
            .to_string()
        );
        assert_eq!(
            "noalias i8* @malloc(i64 %size)",
            Type::<ExtIdentUnit>::Func(FuncSig {
                ret: Box::new(RetParam {
                    attrs: ParamAttrs(vec![ParamAttr(String::from("noalias"), None)]),
                    ty: Type::Ptr(Box::new(Type::I8)),
                }),
                name: Some(GlobalIdent::from("malloc")),
                args: vec![Param {
                    ty: Type::I64,
                    attrs: ParamAttrs(vec![]),
                    name: Some(LocalIdent::from("size"))
                }],
                variadic: false
            })
            .to_string()
        );
        assert_eq!(
            "i32 (i64, ...)",
            Type::<ExtIdentUnit>::Func(FuncSig {
                ret: Box::new(RetParam {
                    attrs: ParamAttrs(vec![]),
                    ty: Type::I32
                }),
                name: None,
                args: vec![Param {
                    ty: Type::I64,
                    attrs: ParamAttrs(vec![]),
                    name: None
                }],
                variadic: true
            })
            .to_string()
        );
        assert_eq!(
            "i32 (i64, i8* byref(i8) align(1))",
            Type::<ExtIdentUnit>::Func(FuncSig {
                ret: Box::new(RetParam {
                    attrs: ParamAttrs(vec![]),
                    ty: Type::I32
                }),
                name: None,
                args: vec![
                    Param {
                        ty: Type::I64,
                        attrs: ParamAttrs(vec![]),
                        name: None
                    },
                    Param {
                        ty: Type::Ptr(Box::new(Type::I8)),
                        attrs: ParamAttrs(vec![
                            ParamAttr(String::from("byref"), Some(ParamAttrArg::Type(Type::I8))),
                            ParamAttr(String::from("align"), Some(ParamAttrArg::U32(1))),
                        ]),
                        name: None
                    }
                ],
                variadic: false
            })
            .to_string()
        );
        assert_eq!(
            "%class.Class0",
            Type::<ExtIdentUnit>::Name(LocalIdent::from("class.Class0")).to_string()
        );
        assert_eq!("metadata", Type::<ExtIdentUnit>::Metadata.to_string());
        assert_eq!(
            "!()(i64)",
            Type::<ExtIdentUnit>::Ext(ExtIdentUnit(), Box::new(Type::I64)).to_string()
        );
    }
    #[test]
    fn type_try_from_sexpr() {
        for (expected, input) in vec![
            ("Ok(void)", "void"),
            ("Ok(i1)", "i1"),
            ("Ok(i8)", "i8"),
            ("Ok(i16)", "i16"),
            ("Ok(i32)", "i32"),
            ("Ok(i64)", "i64"),
            ("Ok(float)", "float"),
            ("Ok(double)", "double"),
            ("Ok(%struct.Object)", r#""struct.Object""#),
            ("Ok(%struct.Object*)", r#"(ptr "struct.Object")"#),
            ("Ok(i32 ())", "(func i32)"),
            ("Ok(i32 (i8, i16))", "(func i32 i8 i16)"),
            ("Ok(i32 (...))", "(varfunc i32)"),
            ("Err(malformed LLIR type (func))", "(func)"),
            ("Err(malformed LLIR type (varfunc))", "(varfunc)"),
            ("Err(malformed LLIR type 0x1)", "1"),
        ] {
            let sexpr = SExpr::parse(input);
            let result = match Type::<ExtIdentUnit>::try_from_sexpr(&sexpr) {
                Ok(ty) => format!("Ok({})", ty),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, &result, "{}", input);
        }
    }
    #[test]
    fn format_wrap_mode() {
        assert_eq!("nuw", WrapMode::Nuw.to_string());
        assert_eq!("nsw", WrapMode::Nsw.to_string());
        assert_eq!("nuw nsw", WrapMode::NuwNsw.to_string());
    }
    #[test]
    fn format_bin_opcode() {
        assert_eq!("add", BinOpcode::Add(None).to_string());
        assert_eq!("add nuw", BinOpcode::Add(Some(WrapMode::Nuw)).to_string());
        assert_eq!("and", BinOpcode::And.to_string());
        assert_eq!("ashr", BinOpcode::Ashr(false).to_string());
        assert_eq!("ashr exact", BinOpcode::Ashr(true).to_string());
        assert_eq!("fadd", BinOpcode::Fadd.to_string());
        assert_eq!("fdiv", BinOpcode::Fdiv.to_string());
        assert_eq!("fmul", BinOpcode::Fmul.to_string());
        assert_eq!("frem", BinOpcode::Frem.to_string());
        assert_eq!("fsub", BinOpcode::Fsub.to_string());
        assert_eq!("lshr", BinOpcode::Lshr(false).to_string());
        assert_eq!("lshr exact", BinOpcode::Lshr(true).to_string());
        assert_eq!("mul", BinOpcode::Mul(None).to_string());
        assert_eq!("mul nuw", BinOpcode::Mul(Some(WrapMode::Nuw)).to_string());
        assert_eq!("or", BinOpcode::Or.to_string());
        assert_eq!("sdiv", BinOpcode::Sdiv(false).to_string());
        assert_eq!("sdiv exact", BinOpcode::Sdiv(true).to_string());
        assert_eq!("shl", BinOpcode::Shl(None).to_string());
        assert_eq!("shl nuw", BinOpcode::Shl(Some(WrapMode::Nuw)).to_string());
        assert_eq!("srem", BinOpcode::Srem.to_string());
        assert_eq!("sub", BinOpcode::Sub(None).to_string());
        assert_eq!("sub nuw", BinOpcode::Sub(Some(WrapMode::Nuw)).to_string());
        assert_eq!("udiv", BinOpcode::Udiv(false).to_string());
        assert_eq!("udiv exact", BinOpcode::Udiv(true).to_string());
        assert_eq!("urem", BinOpcode::Urem.to_string());
        assert_eq!("xor", BinOpcode::Xor.to_string());
    }
    #[test]
    fn format_un_opcode() {
        assert_eq!("fneg", UnOpcode::Fneg.to_string());
    }
    #[test]
    fn format_value() {
        assert_eq!("null", Value::<ExtIdentUnit>::Null.to_string());
        assert_eq!("undef", Value::<ExtIdentUnit>::Undef.to_string());
        assert_eq!("false", Value::<ExtIdentUnit>::False.to_string());
        assert_eq!("true", Value::<ExtIdentUnit>::True.to_string());
        assert_eq!("8", Value::<ExtIdentUnit>::I8(8).to_string());
        assert_eq!("16", Value::<ExtIdentUnit>::I16(16).to_string());
        assert_eq!("32", Value::<ExtIdentUnit>::I32(32).to_string());
        assert_eq!("64", Value::<ExtIdentUnit>::I64(64).to_string());
        assert_eq!(
            "0x46AF8DEF80000000",
            Value::<ExtIdentUnit>::Float(String::from("0x46AF8DEF80000000")).to_string()
        );
        assert_eq!(
            "6.400000e+64",
            Value::<ExtIdentUnit>::Double(String::from("6.400000e+64")).to_string()
        );
        assert_eq!(
            "0xK7FFF8000000000000000",
            Value::<ExtIdentUnit>::X86Fp80(String::from("0xK7FFF8000000000000000")).to_string()
        );
        assert_eq!(
            "<i64 1024, i64 0>",
            Value::<ExtIdentUnit>::Vector(vec![
                TypedValue(Type::I64, Value::I64(1024)),
                TypedValue(Type::I64, Value::I64(0)),
            ])
            .to_string()
        );
        assert_eq!(
            r#"c"Class0(x=%lld)\n\u{0}""#,
            Value::<ExtIdentUnit>::ArrayConst(String::from("Class0(x=%lld)\x0A\x00")).to_string()
        );
        assert_eq!(
            "%1",
            format!("{}", Value::<ExtIdentUnit>::LocalRef(LocalIdent::from("1")))
        );
        assert_eq!("[]", format!("{}", Value::<ExtIdentUnit>::Array(vec![])),);
        assert_eq!(
            "[i8 8]",
            Value::<ExtIdentUnit>::Array(vec![TypedValue(Type::I8, Value::I8(8)),]).to_string()
        );
        assert_eq!(
            "[i8 8, i16 16]",
            Value::<ExtIdentUnit>::Array(vec![
                TypedValue(Type::I8, Value::I8(8)),
                TypedValue(Type::I16, Value::I16(16)),
            ])
            .to_string()
        );
        assert_eq!(
            "{  }",
            format!("{}", Value::<ExtIdentUnit>::Struct(false, vec![])),
        );
        assert_eq!(
            "{ i8 8 }",
            Value::<ExtIdentUnit>::Struct(false, vec![TypedValue(Type::I8, Value::I8(8)),])
                .to_string()
        );
        assert_eq!(
            "{ i8 8, i16 16 }",
            Value::<ExtIdentUnit>::Struct(
                false,
                vec![
                    TypedValue(Type::I8, Value::I8(8)),
                    TypedValue(Type::I16, Value::I16(16)),
                ]
            )
            .to_string()
        );
        assert_eq!(
            "<{ i8 8, i16 16 }>",
            Value::<ExtIdentUnit>::Struct(
                true,
                vec![
                    TypedValue(Type::I8, Value::I8(8)),
                    TypedValue(Type::I16, Value::I16(16)),
                ]
            )
            .to_string()
        );
        assert_eq!(
            "@printf",
            Value::<ExtIdentUnit>::GlobalRef(GlobalIdent::from("printf")).to_string()
        );
        assert_eq!(
            "add (i32 %1, i32 %2)",
            Value::<ExtIdentUnit>::BinOp(Box::new(BinOpArgs {
                opcode: BinOpcode::Add(None),
                left: TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("1"))),
                right: TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("2")))
            }))
            .to_string()
        );
        assert_eq!(
            "fcmp oeq (float %1, float %2)",
            Value::<ExtIdentUnit>::CmpOp(Box::new(CmpOpArgs {
                opcode: CmpOpcode::Fcmp(FcmpCond::Oeq),
                left: TypedValue(Type::Float, Value::LocalRef(LocalIdent::from("1"))),
                right: TypedValue(Type::Float, Value::LocalRef(LocalIdent::from("2")))
            }))
            .to_string()
        );
        assert_eq!(
            "icmp eq (i32 %1, i32 %2)",
            Value::<ExtIdentUnit>::CmpOp(Box::new(CmpOpArgs {
                opcode: CmpOpcode::Icmp(IcmpCond::Eq),
                left: TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("1"))),
                right: TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("2")))
            }))
            .to_string()
        );
        assert_eq!(
            "bitcast (%class.Class0* %6 to %class.Class1*)",
            Value::<ExtIdentUnit>::ConvOp(Box::new(ConvOpArgs {
                opcode: ConvOpcode::Bitcast,
                srctyval: TypedValue(
                    Type::Ptr(Box::new(Type::Name(LocalIdent::from("class.Class0")))),
                    Value::LocalRef(LocalIdent::from("6"))
                ),
                dstty: Type::Ptr(Box::new(Type::Name(LocalIdent::from("class.Class1"))))
            }))
            .to_string()
        );
        assert_eq!(
            "getelementptr inbounds (%class.Class1, %class.Class1* %9, i32 0, i32 1)",
            Value::<ExtIdentUnit>::Getelementptr(Box::new(GetelementptrArgs {
                inbounds: true,
                base_ty: Type::Name(LocalIdent::from("class.Class1")),
                base_ptr: TypedValue(
                    Type::Ptr(Box::new(Type::Name(LocalIdent::from("class.Class1")))),
                    Value::LocalRef(LocalIdent::from("9"))
                ),
                indices: vec![
                    (false, TypedValue(Type::I32, Value::I32(0))),
                    (false, TypedValue(Type::I32, Value::I32(1)))
                ]
            }))
            .to_string()
        );
        assert_eq!(
            "getelementptr (%class.Class1, %class.Class1* %9, i32 0, inrange i32 1)",
            Value::<ExtIdentUnit>::Getelementptr(Box::new(GetelementptrArgs {
                inbounds: false,
                base_ty: Type::Name(LocalIdent::from("class.Class1")),
                base_ptr: TypedValue(
                    Type::Ptr(Box::new(Type::Name(LocalIdent::from("class.Class1")))),
                    Value::LocalRef(LocalIdent::from("9"))
                ),
                indices: vec![
                    (false, TypedValue(Type::I32, Value::I32(0))),
                    (true, TypedValue(Type::I32, Value::I32(1)))
                ]
            }))
            .to_string()
        );
        assert_eq!(
            "fneg (double %1)",
            Value::<ExtIdentUnit>::UnOp(Box::new(UnOpArgs {
                opcode: UnOpcode::Fneg,
                tyval: TypedValue(Type::Double, Value::LocalRef(LocalIdent::from("1")))
            }))
            .to_string()
        );
        assert_eq!(
            "extractelement (<4 x i32> %1, i32 0)",
            Value::<ExtIdentUnit>::VecOp(Box::new(VecOpArgs::Extractelement(
                TypedValue(
                    Type::Vector(false, 4, Box::new(Type::I32)),
                    Value::LocalRef(LocalIdent::from("1"))
                ),
                TypedValue(Type::I32, Value::I32(0))
            )))
            .to_string()
        );
        assert_eq!(
            "insertelement (<4 x i32> %1, i32 1, i32 0)",
            Value::<ExtIdentUnit>::VecOp(Box::new(VecOpArgs::Insertelement(
                TypedValue(
                    Type::Vector(false, 4, Box::new(Type::I32)),
                    Value::LocalRef(LocalIdent::from("1"))
                ),
                TypedValue(Type::I32, Value::I32(1)),
                TypedValue(Type::I32, Value::I32(0))
            )))
            .to_string()
        );
        assert_eq!(
            "shufflevector (<4 x i32> %1, <4 x i32> %2, <1 x i32> <i32 0>)",
            Value::<ExtIdentUnit>::VecOp(Box::new(VecOpArgs::Shufflevector(
                TypedValue(
                    Type::Vector(false, 4, Box::new(Type::I32)),
                    Value::LocalRef(LocalIdent::from("1"))
                ),
                TypedValue(
                    Type::Vector(false, 4, Box::new(Type::I32)),
                    Value::LocalRef(LocalIdent::from("2"))
                ),
                TypedValue(
                    Type::Vector(false, 1, Box::new(Type::I32)),
                    Value::Vector(vec![TypedValue(Type::I32, Value::I32(0))])
                ),
            )))
            .to_string()
        );
        assert_eq!(
            "zeroinitializer",
            Value::<ExtIdentUnit>::Zeroinitializer.to_string()
        );
        assert_eq!(
            "blockaddress(@execute, %434)",
            Value::<ExtIdentUnit>::Blockaddress(
                GlobalIdent::from("execute"),
                Label::from(LocalIdent::from("434"))
            )
            .to_string()
        );
        assert_eq!(
            "!1",
            Value::<ExtIdentUnit>::Metadata(Box::new(Metadata::Ref(MetadataRef(String::from(
                "1"
            )))))
            .to_string()
        );
    }
    #[test]
    fn value_try_to_i64() {
        assert_eq!(None, Value::<ExtIdentUnit>::Null.try_to_i64());
        assert_eq!(Some(8), Value::<ExtIdentUnit>::I8(8).try_to_i64());
        assert_eq!(Some(16), Value::<ExtIdentUnit>::I16(16).try_to_i64());
        assert_eq!(Some(32), Value::<ExtIdentUnit>::I32(32).try_to_i64());
        assert_eq!(Some(64), Value::<ExtIdentUnit>::I64(64).try_to_i64());
    }
    #[test]
    fn format_insn() {
        assert_eq!(
            "%0 = alloca i64",
            Insn::<ExtIdentUnit>::Alloca {
                res: LocalIdent::from("0"),
                ty: Type::I64,
                align: None
            }
            .to_string()
        );
        assert_eq!(
            "%0 = alloca i64, align 8",
            Insn::<ExtIdentUnit>::Alloca {
                res: LocalIdent::from("0"),
                ty: Type::I64,
                align: Some(8)
            }
            .to_string()
        );
        assert_eq!(
            "br label %1",
            Insn::<ExtIdentUnit>::Br(Label::from(LocalIdent::from("1"))).to_string()
        );
        assert_eq!(
            "br i1 %1, label %2, label %3",
            Insn::<ExtIdentUnit>::BrI1(
                Value::LocalRef(LocalIdent::from("1")),
                Label::from(LocalIdent::from("2")),
                Label::from(LocalIdent::from("3"))
            )
            .to_string()
        );
        assert_eq!(
            "call void @f()",
            Insn::<ExtIdentUnit>::Call {
                res: None,
                tail_mode: None,
                body: CallBody {
                    call_conv: None,
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::Void
                    },
                    callee: Callee::Value(Value::GlobalRef(GlobalIdent::from("f"))),
                    args: vec![],
                    attrs: vec![],
                },
                range: None
            }
            .to_string()
        );
        assert_eq!(
            r#"tail call fastcc void @f(i64 %1) "key1" "key2"="value2""#,
            Insn::<ExtIdentUnit>::Call {
                res: None,
                tail_mode: Some(TailMode::Tail),
                body: CallBody {
                    call_conv: Some(CallConv::Fastcc),
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::Void
                    },
                    callee: Callee::Value(Value::GlobalRef(GlobalIdent::from("f"))),
                    args: vec![ParamValue(
                        Param {
                            ty: Type::I64,
                            attrs: ParamAttrs(vec![]),
                            name: None
                        },
                        Value::LocalRef(LocalIdent::from("1"))
                    )],
                    attrs: vec![
                        Attr::Key(String::from("key1")),
                        Attr::KeyValue(String::from("key2"), String::from("value2"))
                    ],
                },
                range: None
            }
            .to_string()
        );
        assert_eq!(
            "%0 = call i64 @f(i64 %1), !range !2",
            Insn::<ExtIdentUnit>::Call {
                res: Some(LocalIdent::from("0")),
                tail_mode: None,
                body: CallBody {
                    call_conv: None,
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::I64
                    },
                    callee: Callee::Value(Value::GlobalRef(GlobalIdent::from("f"))),
                    args: vec![ParamValue(
                        Param {
                            ty: Type::I64,
                            attrs: ParamAttrs(vec![]),
                            name: None
                        },
                        Value::LocalRef(LocalIdent::from("1"))
                    )],
                    attrs: vec![],
                },
                range: Some(MetadataRef(String::from("2")))
            }
            .to_string()
        );
        assert_eq!(
            r#"call void asm "tmpl", "constr"()"#,
            Insn::<ExtIdentUnit>::Call {
                res: None,
                tail_mode: None,
                body: CallBody {
                    call_conv: None,
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::Void
                    },
                    callee: Callee::Asm(String::from("tmpl"), String::from("constr")),
                    args: vec![],
                    attrs: vec![],
                },
                range: None
            }
            .to_string()
        );
        assert_eq!(
            "indirectbr i8* %0, [label %1, label %2]",
            Insn::<ExtIdentUnit>::Indirectbr(
                TypedValue(
                    Type::Ptr(Box::new(Type::I8)),
                    Value::LocalRef(LocalIdent::from("0"))
                ),
                vec![
                    Label::from(LocalIdent::from("1")),
                    Label::from(LocalIdent::from("2")),
                ],
            )
            .to_string()
        );
        assert_eq!(
            "invoke void @f() to label %1 unwind label %2",
            Insn::<ExtIdentUnit>::Invoke {
                res: None,
                body: CallBody {
                    call_conv: None,
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::Void
                    },
                    callee: Callee::Value(Value::GlobalRef(GlobalIdent::from("f"))),
                    args: vec![],
                    attrs: vec![],
                },
                to: Label::from(LocalIdent::from("1")),
                unwind: Label::from(LocalIdent::from("2")),
            }
            .to_string()
        );
        assert_eq!(
            "%0 = invoke i32 @f() to label %1 unwind label %2",
            Insn::<ExtIdentUnit>::Invoke {
                res: Some(LocalIdent::from("0")),
                body: CallBody {
                    call_conv: None,
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::I32
                    },
                    callee: Callee::Value(Value::GlobalRef(GlobalIdent::from("f"))),
                    args: vec![],
                    attrs: vec![],
                },
                to: Label::from(LocalIdent::from("1")),
                unwind: Label::from(LocalIdent::from("2")),
            }
            .to_string()
        );
        assert_eq!(
            r#"%0 = invoke i32 asm "tmpl", "constrs"() to label %1 unwind label %2"#,
            Insn::<ExtIdentUnit>::Invoke {
                res: Some(LocalIdent::from("0")),
                body: CallBody {
                    call_conv: None,
                    ret: RetParam {
                        attrs: ParamAttrs(vec![]),
                        ty: Type::I32
                    },
                    callee: Callee::Asm(String::from("tmpl"), String::from("constrs")),
                    args: vec![],
                    attrs: vec![],
                },
                to: Label::from(LocalIdent::from("1")),
                unwind: Label::from(LocalIdent::from("2")),
            }
            .to_string()
        );
        assert_eq!(
            "%0 = landingpad { i8*, i32 }",
            Insn::<ExtIdentUnit>::Landingpad {
                res: LocalIdent::from("0"),
                ty: Type::Struct(false, vec![Type::Ptr(Box::new(Type::I8)), Type::I32]),
                cleanup: false,
                clauses: vec![],
            }
            .to_string()
        );
        assert_eq!(
            "%0 = landingpad { i8*, i32 } cleanup",
            Insn::<ExtIdentUnit>::Landingpad {
                res: LocalIdent::from("0"),
                ty: Type::Struct(false, vec![Type::Ptr(Box::new(Type::I8)), Type::I32]),
                cleanup: true,
                clauses: vec![],
            }
            .to_string()
        );
        assert_eq!(
            "%0 = landingpad { i8*, i32 } catch i8* null",
            Insn::<ExtIdentUnit>::Landingpad {
                res: LocalIdent::from("0"),
                ty: Type::Struct(false, vec![Type::Ptr(Box::new(Type::I8)), Type::I32]),
                cleanup: false,
                clauses: vec![LandingpadClause::Catch(TypedValue(
                    Type::Ptr(Box::new(Type::I8)),
                    Value::Null
                ))],
            }
            .to_string()
        );
        assert_eq!(
            "%0 = landingpad { i8*, i32 } filter [0 x i8*] zeroinitializer",
            Insn::<ExtIdentUnit>::Landingpad {
                res: LocalIdent::from("0"),
                ty: Type::Struct(false, vec![Type::Ptr(Box::new(Type::I8)), Type::I32]),
                cleanup: false,
                clauses: vec![LandingpadClause::Filter(TypedValue(
                    Type::Array(0, Box::new(Type::Ptr(Box::new(Type::I8)))),
                    Value::Zeroinitializer
                ))],
            }
            .to_string()
        );
        assert_eq!(
            "%0 = load i64, i64* %1",
            Insn::<ExtIdentUnit>::Load {
                res: LocalIdent::from("0"),
                volatile: false,
                ty: Type::I64,
                src: TypedValue(
                    Type::Ptr(Box::new(Type::I64)),
                    Value::LocalRef(LocalIdent::from("1"))
                ),
                align: None,
            }
            .to_string()
        );
        assert_eq!(
            "%0 = load volatile i64, i64* %1, align 8",
            Insn::<ExtIdentUnit>::Load {
                res: LocalIdent::from("0"),
                volatile: true,
                ty: Type::I64,
                src: TypedValue(
                    Type::Ptr(Box::new(Type::I64)),
                    Value::LocalRef(LocalIdent::from("1"))
                ),
                align: Some(8),
            }
            .to_string()
        );
        assert_eq!(
            "%0 = phi %class.Derived1* [ %1, %2 ], [ null, %3 ]",
            Insn::<ExtIdentUnit>::Phi {
                res: LocalIdent::from("0"),
                ty: Type::Ptr(Box::new(Type::Name(LocalIdent::from("class.Derived1")))),
                val_labels: vec![
                    (
                        Value::LocalRef(LocalIdent::from("1")),
                        Label::from(LocalIdent::from("2"))
                    ),
                    (Value::Null, Label::from(LocalIdent::from("3")))
                ]
            }
            .to_string()
        );
        assert_eq!(
            "resume { i8*, i32 } %1",
            Insn::<ExtIdentUnit>::Resume(TypedValue(
                Type::Struct(false, vec![Type::Ptr(Box::new(Type::I8)), Type::I32]),
                Value::LocalRef(LocalIdent::from("1"))
            ))
            .to_string()
        );
        assert_eq!("ret void", Insn::<ExtIdentUnit>::Ret(None).to_string());
        assert_eq!(
            "ret i32 0",
            Insn::<ExtIdentUnit>::Ret(Some(TypedValue(Type::I32, Value::I32(0)))).to_string()
        );
        assert_eq!(
            "%0 = select i1 %1, i64 2, i64 3",
            Insn::<ExtIdentUnit>::Select(
                LocalIdent::from("0"),
                TypedValue(Type::I1, Value::LocalRef(LocalIdent::from("1"))),
                TypedValue(Type::I64, Value::I64(2)),
                TypedValue(Type::I64, Value::I64(3))
            )
            .to_string()
        );
        assert_eq!(
            "store i32 1, i32* %2",
            Insn::<ExtIdentUnit>::Store {
                volatile: false,
                src: TypedValue(Type::I32, Value::I32(1)),
                dst: TypedValue(
                    Type::Ptr(Box::new(Type::I32)),
                    Value::LocalRef(LocalIdent::from("2"))
                ),
                align: None,
            }
            .to_string()
        );
        assert_eq!(
            "store volatile i32 1, i32* %2, align 4",
            Insn::<ExtIdentUnit>::Store {
                volatile: true,
                src: TypedValue(Type::I32, Value::I32(1)),
                dst: TypedValue(
                    Type::Ptr(Box::new(Type::I32)),
                    Value::LocalRef(LocalIdent::from("2"))
                ),
                align: Some(4),
            }
            .to_string()
        );
        assert_eq!(
            "switch i32 %1, label %2 [ i32 3, label %4 i32 5, label %6 ]",
            Insn::<ExtIdentUnit>::Switch(
                TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("1"))),
                Label::from(LocalIdent::from("2")),
                vec![
                    (
                        TypedValue(Type::I32, Value::I32(3)),
                        Label::from(LocalIdent::from("4"))
                    ),
                    (
                        TypedValue(Type::I32, Value::I32(5)),
                        Label::from(LocalIdent::from("6"))
                    )
                ]
            )
            .to_string()
        );
        assert_eq!(
            "%0 = add (i32 %1, i32 1)",
            Insn::<ExtIdentUnit>::Value(
                LocalIdent::from("0"),
                Value::BinOp(Box::new(BinOpArgs {
                    opcode: BinOpcode::Add(None),
                    left: TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("1"))),
                    right: TypedValue(Type::I32, Value::I32(1)),
                }))
            )
            .to_string()
        );
    }
    #[test]
    fn format_metadata_ref() {
        assert_eq!("!0", MetadataRef(String::from("0")).to_string());
        assert_eq!(r#"!"::1""#, MetadataRef(String::from("::1")).to_string());
    }
    #[test]
    fn format_metadata() {
        assert_eq!("null", Metadata::<ExtIdentUnit>::Null.to_string());
        assert_eq!("false", Metadata::<ExtIdentUnit>::Bool(false).to_string());
        assert_eq!("true", Metadata::<ExtIdentUnit>::Bool(true).to_string());
        assert_eq!(
            "keyword",
            Metadata::<ExtIdentUnit>::Keyword(String::from("keyword")).to_string(),
        );
        assert_eq!(
            "!\"keyword with space\"",
            Metadata::<ExtIdentUnit>::Keyword(String::from("keyword with space")).to_string(),
        );
        assert_eq!(
            "\"string\"",
            Metadata::<ExtIdentUnit>::String(String::from("string")).to_string()
        );
        assert_eq!(
            "i32 32",
            Metadata::<ExtIdentUnit>::TypedValue(TypedValue(Type::I32, Value::I32(32))).to_string()
        );
        assert_eq!(
            "!{false, true}",
            Metadata::<ExtIdentUnit>::Struct(vec![Metadata::Bool(false), Metadata::Bool(true)])
                .to_string()
        );
        assert_eq!(
            "!name(key1: false, key2: true)",
            Metadata::<ExtIdentUnit>::KeyValues(MetadataRef(String::from("name")), {
                let mut fields = BTreeMap::new();
                fields.insert(Label::from(LocalIdent::from("key1")), Metadata::Bool(false));
                fields.insert(Label::from(LocalIdent::from("key2")), Metadata::Bool(true));
                fields
            })
            .to_string()
        );
        assert_eq!(
            "false | true",
            Metadata::<ExtIdentUnit>::Or(vec![Metadata::Bool(false), Metadata::Bool(true)])
                .to_string()
        );
        assert_eq!(
            "!1",
            Metadata::<ExtIdentUnit>::Ref(MetadataRef(String::from("1"))).to_string()
        );
    }
}
