//! The typing environment module.

use crate::llir::abi::{DataLayout, GetelementptrResult};
use crate::llir::interp::rtti::ExtIdent;
use crate::llir::syntax::{
    AggOpArgs, BinOpArgs, CmpOpArgs, ConvOpArgs, ConvOpcode, GlobalIdent, Loc, LocalIdent,
    Type as LLIRType, TypedValue, Typedefs, UnOpArgs, Value, VecOpArgs,
};
use crate::typechk::syntax::{
    AllocKind, AllocReason, Constr, Constrs, Effect, EffectKind, FuncArgs, InferVar, JudgeTerm,
    Size, Type, ValueExt, VarName,
};
use std::cmp::Ordering;
use std::collections::BTreeMap;

/// A mode of the intern operation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InternMode {
    /// The mode in declaration.
    Declare,
    /// The mode in definition.
    Define,
}

/// A typing environment which implements the structural typing.
pub struct TypeEnv {
    datalayout: DataLayout,
    typedefs: Typedefs<ExtIdent>,
    typeset: BTreeMap<LocalIdent, Type>,
    funcset: BTreeMap<GlobalIdent, FuncArgs>,
    varset: BTreeMap<VarName, Type>,
    effectset: BTreeMap<Loc, Effect>,
    ninfervars: usize,
}

impl TypeEnv {
    /// Returns a new typing environment.
    pub fn empty(datalayout: DataLayout) -> TypeEnv {
        TypeEnv {
            datalayout,
            typedefs: Typedefs::empty(),
            typeset: BTreeMap::new(),
            funcset: BTreeMap::new(),
            varset: BTreeMap::new(),
            effectset: BTreeMap::new(),
            ninfervars: 0,
        }
    }
    /// Returns the datalayout.
    pub fn datalayout(&self) -> &DataLayout {
        &self.datalayout
    }
    /// Returns the typedef list.
    pub fn typedefs(&self) -> &Typedefs<ExtIdent> {
        &self.typedefs
    }
    /// Returns the typeset (interned typedef list).
    pub fn typeset(&self) -> &BTreeMap<LocalIdent, Type> {
        &self.typeset
    }
    /// Returns the varset (the map from the variable name to the bound type).
    pub fn varset(&self) -> &BTreeMap<VarName, Type> {
        &self.varset
    }
    /// Returns the type in the typeset by name.
    pub fn ty(&self, name: &LocalIdent) -> Result<&Type, String> {
        match self.typeset.get(name) {
            Some(ty) => Ok(ty),
            None => Err(format!("type {} is not found", name)),
        }
    }
    /// Defines the type with the name and the LLIR prototype.
    pub fn define_type(
        &mut self,
        name: LocalIdent,
        prototype: LLIRType<ExtIdent>,
        ty: Type,
    ) -> Result<(), String> {
        if self.typeset.contains_key(&name) {
            return Err(format!("type {} is already defined", name));
        }
        self.typedefs.insert(name, prototype);
        self.typeset.insert(name, ty);
        Ok(())
    }
    /// Returns the function by name.
    pub fn func(&self, name: &GlobalIdent) -> Result<&FuncArgs, String> {
        match self.funcset.get(name) {
            Some(func) => Ok(func),
            None => Err(format!("func {} is not found", name)),
        }
    }
    /// Declares the function with the name, type and arguments.
    pub fn declare_func(
        &mut self,
        name: GlobalIdent,
        ty: Type,
        args: FuncArgs,
    ) -> Result<(), String> {
        if self.funcset.contains_key(&name) {
            return Err(format!("func {} is already defined", name));
        }
        self.declare_var(VarName::Global(name), ty)?;
        self.funcset.insert(name, args);
        Ok(())
    }
    /// Returns the type bound to the variable by name.
    pub fn var(&self, name: &VarName) -> Result<&Type, String> {
        match self.varset.get(name) {
            Some(ty) => Ok(ty),
            None => Err(format!("variable {} is not found", name)),
        }
    }
    /// Declares the variable with the name and type.
    pub fn declare_var(&mut self, name: VarName, ty: Type) -> Result<(), String> {
        if self.varset.contains_key(&name) {
            return Err(format!("variable {} is already defined", name));
        }
        self.varset.insert(name, ty);
        Ok(())
    }
    /// Returns the effect set (the map from the location to the effect).
    pub fn effectset(&self) -> &BTreeMap<Loc, Effect> {
        &self.effectset
    }
    /// Returns the effect by the location.
    pub fn effect(&self, loc: &Loc) -> Option<&Effect> {
        self.effectset.get(loc)
    }
    /// Inserts the effect at the location.
    pub fn insert_effect(&mut self, loc: Loc, effkind: EffectKind) {
        if let Some(effect) = self.effectset.get_mut(&loc) {
            return effect.push(effkind, loc);
        }
        let mut effect = Effect::empty();
        effect.push(effkind, loc);
        self.effectset.insert(loc, effect);
    }
    /// Returns a new (fresh) inference variable.
    pub fn new_infervar(&mut self) -> InferVar {
        let infervar = InferVar::new(self.ninfervars);
        self.ninfervars += 1;
        infervar
    }
    /// Returns the alignment of the LLIR type via [`DataLayout::alignof_type`].
    pub fn alignof_type(&self, ty: &LLIRType<ExtIdent>) -> Option<usize> {
        Some(self.datalayout().alignof_type(ty, &self.typedefs)? as usize)
    }
    /// Returns the size of the LLIR type via [`DataLayout::sizeof_type`].
    pub fn sizeof_type(&self, ty: &LLIRType<ExtIdent>) -> Option<usize> {
        Some(self.datalayout().sizeof_type(ty, &self.typedefs)? as usize)
    }
    fn do_intern_llir_type(
        &self,
        inptr: bool,
        ty: &LLIRType<ExtIdent>,
        loc: &Loc,
    ) -> Result<Type, String> {
        match ty {
            LLIRType::Void | LLIRType::Opaque => Ok(Type::Void),
            LLIRType::I1 => Ok(Type::I(1)),
            LLIRType::I8 => Ok(Type::I(8)),
            LLIRType::I16 => Ok(Type::I(16)),
            LLIRType::I32 => Ok(Type::I(32)),
            LLIRType::I64 => Ok(Type::I(64)),
            LLIRType::Float => Ok(Type::F(32)),
            LLIRType::Double => Ok(Type::F(64)),
            LLIRType::X86Fp80 => Ok(Type::F(128)),
            LLIRType::Ptr(ty) => Ok(Type::Ptr(
                InferVar::dummy(),
                Box::new(self.do_intern_llir_type(true, ty, loc)?),
            )),
            LLIRType::Vector(vscale, n, ty) => Ok(Type::Vector(
                *vscale,
                *n as usize,
                Box::new(self.do_intern_llir_type(inptr, ty, loc)?),
            )),
            LLIRType::Array(n, ty) => Ok(Type::Array(
                *n as usize,
                Box::new(self.do_intern_llir_type(inptr, ty, loc)?),
            )),
            LLIRType::Struct(packed, tys) => {
                if tys.is_empty() {
                    return Ok(Type::Struct(vec![]));
                }
                let mut fields = Vec::with_capacity(tys.len());
                let mut p = 0;
                for i in 0..(tys.len() + 1) {
                    if !*packed {
                        let ty = &tys[i % tys.len()];
                        let align = match self.alignof_type(ty) {
                            Some(align) => align,
                            None => return Err(format!("unknown align of type {}", ty)),
                        };
                        let q = (p + align - 1) / align * align;
                        if q > p {
                            fields.push(Type::Pad(q - p));
                            p = q;
                        }
                    }
                    if i >= tys.len() {
                        break;
                    }
                    let ty = &tys[i];
                    p += match self.sizeof_type(ty) {
                        Some(size) => size,
                        None => return Err(format!("unknown size of type {}", ty)),
                    };
                    let field = self.do_intern_llir_type(inptr, ty, loc)?;
                    match field {
                        Type::Struct(mut fs) => fields.append(&mut fs),
                        _ => fields.push(field),
                    }
                }
                Ok(Type::Struct(fields))
            }
            LLIRType::Func(sig) => {
                let ret = self.do_intern_llir_type(inptr, &sig.ret.ty, loc)?;
                let mut args = Vec::with_capacity(sig.args.len());
                for param in &sig.args {
                    args.push(self.do_intern_llir_type(inptr, &param.ty, loc)?);
                }
                Ok(Type::Func(Box::new(ret), args, sig.variadic))
            }
            LLIRType::Name(name) => match inptr {
                true => Ok(Type::Name(*name)),
                false => match self.ty(name) {
                    Ok(ty) => Ok(ty.clone()),
                    Err(err) => Err(err),
                },
            },
            LLIRType::Ext(eid, orig) => Ok(Type::Ext(
                *eid,
                Box::new(self.do_intern_llir_type(true, orig, loc)?),
            )),
            LLIRType::Metadata => Err("cannot intern metadata type".to_string()),
        }
    }
    /// Returns an type interned from the given LLIR type at the location.
    pub fn intern_llir_type(&self, ty: &LLIRType<ExtIdent>, loc: &Loc) -> Result<Type, String> {
        self.do_intern_llir_type(false, ty, loc)
    }
    /// Returns a type interned from the given LLIR type at the location.
    /// The returned type is refreshed via [`Type::refresh`].
    pub fn intern_refresh_llir_type(
        &mut self,
        ty: &LLIRType<ExtIdent>,
        all: bool,
        loc: &Loc,
    ) -> Result<Type, String> {
        let mut ty = self.intern_llir_type(ty, loc)?;
        ty.refresh(all, self);
        Ok(ty)
    }
    /// Calls [`TypeEnv::intern_refresh_llir_type`] with `all = false`.
    pub fn intern_fresh_llir_type(
        &mut self,
        ty: &LLIRType<ExtIdent>,
        loc: &Loc,
    ) -> Result<Type, String> {
        self.intern_refresh_llir_type(ty, false, loc)
    }
    /// Returns a type interned from the given LLIR type and value at the location.
    pub fn intern_type_value(
        &mut self,
        mode: InternMode,
        ty: Option<&LLIRType<ExtIdent>>,
        val: &Value<ExtIdent>,
        loc: &Loc,
        constrs: &mut Constrs,
    ) -> Result<Type, String> {
        match val {
            Value::Null => match ty {
                Some(ty @ LLIRType::Ptr(_)) => self.intern_fresh_llir_type(ty, loc),
                _ => Ok(Type::Nullptr),
            },
            Value::Undef => match ty {
                Some(ty) => self.intern_fresh_llir_type(ty, loc),
                _ => Ok(Type::Void),
            },
            Value::False | Value::True => self.intern_fresh_llir_type(&LLIRType::I1, loc),
            Value::I8(_) => self.intern_fresh_llir_type(&LLIRType::I8, loc),
            Value::I16(_) => self.intern_fresh_llir_type(&LLIRType::I16, loc),
            Value::I32(_) => self.intern_fresh_llir_type(&LLIRType::I32, loc),
            Value::I64(_) => self.intern_fresh_llir_type(&LLIRType::I64, loc),
            Value::Float(_) => self.intern_fresh_llir_type(&LLIRType::Float, loc),
            Value::Double(_) => self.intern_fresh_llir_type(&LLIRType::Double, loc),
            Value::X86Fp80(_) => self.intern_fresh_llir_type(&LLIRType::X86Fp80, loc),
            Value::Vector(fields) => {
                let mut vecty = None;
                for tyval in fields {
                    let ty = self.intern_typedvalue(mode, tyval, loc, constrs)?;
                    match &vecty {
                        Some(vecty) => {
                            if !self.judge_cast(&ty, vecty, false, loc, &mut Some(constrs))? {
                                constrs.insert(Constr::Cast(ty.clone(), vecty.clone()), *loc)?;
                            }
                        }
                        None => vecty = Some(ty),
                    }
                }
                match vecty {
                    Some(vecty) => Ok(Type::Vector(false, fields.len(), Box::new(vecty))),
                    None => Ok(Type::Vector(false, 0, Box::new(Type::Void))),
                }
            }
            Value::ArrayConst(c) => self.intern_fresh_llir_type(
                &LLIRType::Array(c.len() as u32, Box::new(LLIRType::I8)),
                loc,
            ),
            Value::Array(fields) => {
                let mut arrty = None;
                for tyval in fields {
                    let ty = self.intern_typedvalue(mode, tyval, loc, constrs)?;
                    match &arrty {
                        Some(arrty) => {
                            if !self.judge_cast(&ty, arrty, false, loc, &mut Some(constrs))? {
                                constrs.insert(Constr::Cast(ty.clone(), arrty.clone()), *loc)?;
                            }
                        }
                        None => arrty = Some(ty),
                    }
                }
                match arrty {
                    Some(arrty) => Ok(Type::Array(fields.len(), Box::new(arrty))),
                    None => Ok(Type::Array(0, Box::new(Type::Void))),
                }
            }
            Value::Struct(packed, tyvals) => {
                if tyvals.is_empty() {
                    return Ok(Type::Struct(vec![]));
                }
                let mut fields = Vec::with_capacity(tyvals.len());
                let mut p = 0;
                for i in 0..(tyvals.len() + 1) {
                    if !*packed {
                        let TypedValue(ty, _) = &tyvals[i % tyvals.len()];
                        let align = match self.alignof_type(ty) {
                            Some(align) => align,
                            None => return Err(format!("unknown align of type {}", ty)),
                        };
                        let q = (p + align - 1) / align * align;
                        if q > p {
                            fields.push(Type::Pad(q - p));
                            p = q;
                        }
                    }
                    if i >= tyvals.len() {
                        break;
                    }
                    let TypedValue(ty, val) = &tyvals[i];
                    p += match self.sizeof_type(ty) {
                        Some(size) => size,
                        None => return Err(format!("unknown size of type {}", ty)),
                    };
                    let prototype = self.intern_fresh_llir_type(ty, loc)?;
                    let field = self.intern_type_value(mode, Some(ty), val, loc, constrs)?;
                    if !self.judge_cast(&field, &prototype, false, loc, &mut Some(constrs))? {
                        constrs.insert(Constr::Cast(field.clone(), prototype.clone()), *loc)?;
                    }
                    match field {
                        Type::Struct(mut fs) => fields.append(&mut fs),
                        _ => fields.push(field),
                    }
                }
                Ok(Type::Struct(fields))
            }
            Value::LocalRef(name) => Ok(self.var(&VarName::Local(*name, loc.func))?.clone()),
            Value::GlobalRef(name) => Ok(self.var(&VarName::Global(*name))?.clone()),
            Value::AggOp(args) => {
                let (insert, base_ty, base_val, indices) = match args.as_ref() {
                    AggOpArgs::Extractvalue(TypedValue(ty, val), indices) => {
                        (false, ty, val, indices)
                    }
                    AggOpArgs::Insertvalue(TypedValue(ty, val), _, indices) => {
                        (true, ty, val, indices)
                    }
                };
                let (offset, ty) = {
                    let (o, ty) =
                        self.datalayout()
                            .extractvalue(base_ty, indices, self.typedefs())?;
                    (o, ty.clone())
                };
                if mode == InternMode::Declare {
                    let ty = match args.as_ref() {
                        AggOpArgs::Extractvalue(..) => &ty,
                        AggOpArgs::Insertvalue(..) => base_ty,
                    };
                    return self.intern_fresh_llir_type(ty, loc);
                }
                if let AggOpArgs::Insertvalue(_, elt, _) = args.as_ref() {
                    let ty = self.intern_fresh_llir_type(&ty, loc)?;
                    let eltval = self.intern_typedvalue(mode, elt, loc, constrs)?;
                    if !self.judge_cast(&eltval, &ty, false, loc, &mut Some(constrs))? {
                        constrs.insert(Constr::Cast(eltval, ty), *loc)?;
                    }
                }
                let base_val = if insert && base_val == &Value::Undef {
                    self.intern_fresh_llir_type(base_ty, loc)?
                } else {
                    self.intern_type_value(mode, Some(base_ty), base_val, loc, constrs)?
                };
                match &base_val {
                    Type::Array(n, ty) => {
                        let size = match ty.size(self).unwrap().try_to_usize() {
                            Some(size) => size,
                            res => unreachable!("{:?}", res),
                        };
                        if offset % size != 0 {
                            return Err(format!(
                                "in-bound offset {} in {} with element size {}",
                                offset, base_val, size
                            ));
                        }
                        if offset + size > *n * size {
                            return Err(format!(
                                "out-of-bound offset {} in {} with size {}",
                                offset,
                                base_val,
                                *n * size
                            ));
                        }
                        match insert {
                            false => Ok(ty.as_ref().clone()),
                            true => Ok(base_val),
                        }
                    }
                    Type::Struct(fields) => {
                        let mut p = 0;
                        for (i, field) in fields.iter().enumerate() {
                            match p.cmp(&offset) {
                                Ordering::Greater => {
                                    return Err(format!(
                                        "in-bound offset {} in {}",
                                        offset, base_val
                                    ))
                                }
                                Ordering::Equal => {
                                    return match insert {
                                        false => Ok(fields[i].clone()),
                                        true => Ok(base_val),
                                    }
                                }
                                Ordering::Less => {}
                            }
                            p += match field.size(self).unwrap().try_to_usize() {
                                Some(size) => size,
                                None => unreachable!("None"),
                            };
                        }
                        Err(format!("out-of-bound offset {} in {}", offset, base_val))
                    }
                    _ => Err(format!("illegal base type {}", base_val)),
                }
            }
            Value::BinOp(args) => {
                let BinOpArgs { left, right, .. } = args as &BinOpArgs<_>;
                if left.0 != right.0 {
                    return Err(format!("cannot operate {} and {}", left.0, right.0));
                }
                let leftty = self.intern_fresh_llir_type(&left.0, loc)?;
                if mode == InternMode::Declare {
                    return Ok(leftty);
                }
                let leftval = self.intern_typedvalue(mode, left, loc, constrs)?;
                let rightty = self.intern_fresh_llir_type(&right.0, loc)?;
                let rightval = self.intern_typedvalue(mode, right, loc, constrs)?;
                if !self.judge_cast(&leftval, &leftty, false, loc, &mut Some(constrs))? {
                    constrs.insert(Constr::Cast(leftval, leftty.clone()), *loc)?;
                }
                if !self.judge_cast(&rightval, &rightty, false, loc, &mut Some(constrs))? {
                    constrs.insert(Constr::Cast(rightval, rightty), *loc)?;
                }
                Ok(leftty)
            }
            Value::CmpOp(args) => {
                let CmpOpArgs { left, right, .. } = args as &CmpOpArgs<_>;
                if left.0 != right.0 {
                    return Err(format!("cannot compare {} and {}", left.0, right.0));
                }
                if mode == InternMode::Declare {
                    return self.intern_fresh_llir_type(&LLIRType::I1, loc);
                }
                let leftty = self.intern_fresh_llir_type(&left.0, loc)?;
                let leftval = self.intern_typedvalue(mode, left, loc, constrs)?;
                let rightty = self.intern_fresh_llir_type(&right.0, loc)?;
                let rightval = self.intern_typedvalue(mode, right, loc, constrs)?;
                if !self.judge_cast(&leftval, &leftty, false, loc, &mut Some(constrs))? {
                    constrs.insert(Constr::Cast(leftval, leftty), *loc)?;
                }
                if !self.judge_cast(&rightval, &rightty, false, loc, &mut Some(constrs))? {
                    constrs.insert(Constr::Cast(rightval, rightty), *loc)?;
                }
                self.intern_fresh_llir_type(&LLIRType::I1, loc)
            }
            Value::ConvOp(args) => {
                let ConvOpArgs {
                    opcode,
                    srctyval,
                    dstty,
                } = args.as_ref();
                let TypedValue(srcty, srcval) = srctyval;
                match opcode {
                    ConvOpcode::Inttoptr => {
                        let srcty = self.intern_fresh_llir_type(srcty, loc)?;
                        let dstty = self.intern_fresh_llir_type(dstty, loc)?;
                        if mode == InternMode::Declare {
                            return Ok(dstty);
                        }
                        match &dstty {
                            Type::Ptr(..) => {
                                constrs.insert(Constr::IntToPtr(srcty, dstty.clone()), *loc)?;
                            }
                            _ => return Err(format!("cannot cast {} as {}", srcval, dstty)),
                        }
                        Ok(dstty)
                    }
                    ConvOpcode::Ptrtoint => {
                        match self.intern_typedvalue(mode, srctyval, loc, constrs)? {
                            Type::Ptr(..) => self.intern_fresh_llir_type(dstty, loc),
                            _ => return Err(format!("cannot cast {} as {}", srcval, srcty)),
                        }
                    }
                    _ => self.intern_fresh_llir_type(dstty, loc),
                }
            }
            Value::Getelementptr(args) => {
                let GetelementptrResult {
                    index,
                    offset,
                    ty: fieldptrty,
                } = self.datalayout().getelementptr(args, self.typedefs())?;
                if mode == InternMode::Declare {
                    return self.intern_fresh_llir_type(&fieldptrty, loc);
                }
                let fieldty = match &fieldptrty {
                    LLIRType::Ptr(ty) => self.intern_fresh_llir_type(ty, loc)?,
                    ty => unreachable!("{}", ty),
                };
                let fieldsize = match fieldty.size(self) {
                    Some(Size::Const(size)) => size,
                    _ => return Err(format!("unknown size of field type {}", fieldty)),
                };
                // NOTICE: Due to physical subtyping, it is impossible to judge
                // whether the target pointer type is same as the actual one.
                // Hence, baseptr is checked in order not to permit pointee's upcast.
                let baseptr = self.intern_typedvalue(mode, &args.base_ptr, loc, constrs)?;
                let baseptrty = self.intern_fresh_llir_type(&args.base_ptr.0, loc)?;
                let (var, basety) = match &baseptr {
                    Type::Ptr(var, ty) => (var, ty),
                    ty => return Err(format!("illegal base pointer type {}", ty)),
                };
                let realsize = basety.size(self);
                let baseeid = basety.try_to_ext_ident(self);
                let size = match &baseptrty {
                    Type::Ptr(_, ty) => match ty.size(self) {
                        Some(Size::Const(size)) => size,
                        _ => return Err(format!("unknown size of base type {}", ty)),
                    },
                    ty => return Err(format!("illegal base pointer type {}", ty)),
                };
                if !self.judge_cast(&baseptr, &baseptrty, false, loc, &mut Some(constrs))? {
                    constrs.insert(Constr::Cast(baseptr.clone(), baseptrty), *loc)?;
                }
                if index.try_to_i64() != Some(0) {
                    constrs.insert(Constr::NonzeroIndex(index, baseptr.clone()), *loc)?;
                }
                match offset.try_to_i64() {
                    Some(o) if 0 <= o && o + fieldsize <= size => {
                        if let Some(baseeid) = baseeid {
                            let escapable = match fieldty.try_to_ext_ident(self) {
                                Some(eid) if baseeid.name.id() == eid.name.id() => false,
                                _ => {
                                    if baseeid.name.is_downcast_subtarget() {
                                        false
                                    } else if baseeid.name.is_downcast_target() {
                                        match realsize {
                                            Some(Size::Const(realsize)) => o + fieldsize > realsize,
                                            _ => true,
                                        }
                                    } else {
                                        true
                                    }
                                }
                            };
                            if escapable {
                                let reason = Constr::EscapeViaGetelementptr(
                                    fieldty.clone(),
                                    baseptr.clone(),
                                    offset,
                                );
                                constrs.insert(reason, *loc)?;
                            }
                        }
                    }
                    _ => {
                        constrs.insert(Constr::OutOfBoundOffset(offset, baseptr.clone()), *loc)?;
                    }
                }
                Ok(Type::Ptr(*var, Box::new(fieldty)))
            }
            Value::UnOp(args) => {
                let UnOpArgs { tyval, .. } = args as &UnOpArgs<_>;
                let ty = self.intern_fresh_llir_type(&tyval.0, loc)?;
                if mode == InternMode::Declare {
                    return Ok(ty);
                }
                let val = self.intern_typedvalue(mode, tyval, loc, constrs)?;
                if !self.judge_cast(&val, &ty, false, loc, &mut Some(constrs))? {
                    constrs.insert(Constr::Cast(val, ty.clone()), *loc)?;
                }
                Ok(ty)
            }
            // NOTICE: The range of the indices will not be checked,
            //   because compiler or CPU is expected to detect illegal indices.
            Value::VecOp(args) => match args.as_ref() {
                VecOpArgs::Extractelement(val, idx) => {
                    if mode == InternMode::Declare {
                        return match &val.0 {
                            LLIRType::Vector(_, _, ty) => self.intern_fresh_llir_type(ty, loc),
                            ty => Err(format!("illegal extractelement value type {}", ty)),
                        };
                    }
                    let idxty = self.intern_fresh_llir_type(&idx.0, loc)?;
                    let idxval = self.intern_typedvalue(mode, idx, loc, constrs)?;
                    self.judge_term(JudgeTerm::Cast(idxval, idxty), loc, constrs)?;
                    match self.intern_typedvalue(mode, val, loc, constrs)? {
                        Type::Vector(_, _, ty) => Ok(ty.as_ref().clone()),
                        ty => Err(format!("illegal value: {}", ty)),
                    }
                }
                VecOpArgs::Insertelement(val, elt, idx) => {
                    if mode == InternMode::Declare {
                        return match &val.0 {
                            LLIRType::Vector(_, _, ty) => self.intern_fresh_llir_type(ty, loc),
                            ty => Err(format!("illegal insertelement value type {}", ty)),
                        };
                    }
                    let eltty = self.intern_fresh_llir_type(&elt.0, loc)?;
                    let eltval = self.intern_typedvalue(mode, elt, loc, constrs)?;
                    self.judge_term(JudgeTerm::Cast(eltval, eltty), loc, constrs)?;
                    let idxty = self.intern_fresh_llir_type(&idx.0, loc)?;
                    let idxval = self.intern_typedvalue(mode, idx, loc, constrs)?;
                    self.judge_term(JudgeTerm::Cast(idxval, idxty), loc, constrs)?;
                    self.intern_typedvalue(mode, val, loc, constrs)
                }
                VecOpArgs::Shufflevector(v1, v2, mask) => {
                    if mode == InternMode::Declare {
                        let ty1 = match &v1.0 {
                            LLIRType::Vector(_, _, ty) => ty,
                            ty => return Err(format!("illegal shufflevector v1 type {}", ty)),
                        };
                        let ty2 = match &v2.0 {
                            LLIRType::Vector(_, _, ty) => ty,
                            ty => return Err(format!("illegal shufflevector v2 type {}", ty)),
                        };
                        let (vscale, n) = match &mask.0 {
                            LLIRType::Vector(vscale, n, ty) if ty.as_ref() == &LLIRType::I32 => {
                                (vscale, n)
                            }
                            ty => return Err(format!("illegal shufflevector mask type {}", ty)),
                        };
                        if ty1 != ty2 {
                            return Err(format!("type of v1 and v2 differs: {} <> {}", ty1, ty2));
                        }
                        let ty = LLIRType::Vector(*vscale, *n, ty1.clone());
                        return self.intern_fresh_llir_type(&ty, loc);
                    }
                    let v1ty = self.intern_fresh_llir_type(&v1.0, loc)?;
                    let v1val = match &v1.1 {
                        Value::Undef => v1ty,
                        _ => {
                            let v1val = self.intern_typedvalue(mode, v1, loc, constrs)?;
                            let term = JudgeTerm::Cast(v1val.clone(), v1ty);
                            self.judge_term(term, loc, constrs)?;
                            v1val
                        }
                    };
                    let ty1 = match v1val {
                        Type::Vector(_, _, ty) => ty,
                        _ => return Err(format!("illegal v1 type {}", v1val)),
                    };
                    let v2ty = self.intern_fresh_llir_type(&v2.0, loc)?;
                    let v2val = match &v2.1 {
                        Value::Undef => v2ty,
                        _ => {
                            let v2val = self.intern_typedvalue(mode, v2, loc, constrs)?;
                            let term = JudgeTerm::Cast(v2val.clone(), v2ty);
                            self.judge_term(term, loc, constrs)?;
                            v2val
                        }
                    };
                    let ty2 = match v2val {
                        Type::Vector(_, _, ty) => ty,
                        _ => return Err(format!("illegal v2 type {}", v2val)),
                    };
                    let maskty = self.intern_fresh_llir_type(&mask.0, loc)?;
                    let maskval = match &mask.1 {
                        Value::Zeroinitializer => maskty,
                        _ => {
                            let maskval = self.intern_typedvalue(mode, mask, loc, constrs)?;
                            let term = JudgeTerm::Cast(maskval.clone(), maskty);
                            self.judge_term(term, loc, constrs)?;
                            maskval
                        }
                    };
                    let (vscale, n) = match maskval {
                        Type::Vector(vscale, n, ty) if ty.as_ref() == &Type::I(32) => (vscale, n),
                        _ => return Err(format!("illegal mask type {}", maskval)),
                    };
                    let term = JudgeTerm::Cast(*ty2, ty1.as_ref().clone());
                    self.judge_term(term, loc, constrs)?;
                    Ok(Type::Vector(vscale, n, ty1))
                }
            },
            Value::Zeroinitializer => match ty {
                Some(ty) => self.intern_fresh_llir_type(ty, loc),
                None => Err("illegal zeroinitializer".to_string()),
            },
            Value::Blockaddress(..) => Ok(Type::Ptr(self.new_infervar(), Box::new(Type::I(8)))),
            Value::Metadata(_) => Err(format!("cannot intern metadata value {}", val)),
        }
    }
    /// Returns a type interned from the given LLIR typed value at the location.
    pub fn intern_typedvalue(
        &mut self,
        mode: InternMode,
        tyval: &TypedValue<ExtIdent>,
        loc: &Loc,
        constrs: &mut Constrs,
    ) -> Result<Type, String> {
        self.intern_type_value(mode, Some(&tyval.0), &tyval.1, loc, constrs)
    }
    /// Returns a type interned from the given value at the location.
    pub fn intern_value_expr(
        &mut self,
        mode: InternMode,
        val: &Value<ExtIdent>,
        loc: &Loc,
        constrs: &mut Constrs,
    ) -> Result<Type, String> {
        if let Value::ConvOp(args) = val {
            let ConvOpArgs {
                opcode,
                srctyval: TypedValue(_, srcval),
                dstty,
            } = args.as_ref();
            if let ConvOpcode::Bitcast = opcode {
                let ty = self.intern_type_value(mode, None, srcval, loc, constrs)?;
                let val = ValueExt::CollapsePoison(ty, dstty.clone());
                return self.intern_value_ext(mode, val, loc, constrs);
            }
        }
        self.intern_type_value(mode, None, val, loc, constrs)
    }
    /// Judges the allocation.
    pub fn judge_alloc(
        &mut self,
        kind: &AllocKind,
        ty: &Type,
        loc: &Loc,
        constrs: &mut Constrs,
    ) -> Result<(), String> {
        let reason = match &ty {
            Type::Ptr(_, ty) => match ty.contains_ext(self)? {
                true => AllocReason::ContainExt,
                false => AllocReason::Normal,
            },
            _ => return Err(format!("cannot {} with result type {}", kind, ty)),
        };
        constrs.insert(Constr::Alloc(*kind, reason, ty.clone()), *loc)
    }
    /// Returns a type interned from the extended value at the location.
    pub fn intern_value_ext(
        &mut self,
        mode: InternMode,
        val: ValueExt,
        loc: &Loc,
        constrs: &mut Constrs,
    ) -> Result<Type, String> {
        match val {
            ValueExt::Alloc(kind, ty) => {
                let ty = LLIRType::Ptr(Box::new(ty));
                let ty = self.intern_fresh_llir_type(&ty, loc)?;
                self.judge_alloc(&kind, &ty, loc, constrs)?;
                Ok(ty)
            }
            ValueExt::CollapsePoison(ty1, ty2) => match ty1 {
                Type::Poison(kind, size) => {
                    let ty2 = self.intern_fresh_llir_type(&ty2, loc)?;
                    let ty = match &ty2 {
                        Type::Ptr(_, ty) => ty,
                        _ => return Err(format!("cannot cast {} as {}", ty1, ty2)),
                    };
                    let matched = match size {
                        Size::Const(_) => match ty.size(self) {
                            Some(tysize) => tysize == size,
                            None => false,
                        },
                        Size::Dynamic => false,
                    };
                    match matched {
                        true => {
                            if mode == InternMode::Define {
                                self.judge_alloc(&kind, &ty2, loc, constrs)?;
                            }
                        }
                        false => {
                            constrs.insert(Constr::UnmatchedPoisonSize(ty2.clone(), size), *loc)?;
                        }
                    }
                    Ok(ty2)
                }
                _ => Ok(ty1),
            },
            ValueExt::DeclareFunc(ret, args, variadic) => match mode {
                InternMode::Declare => {
                    let var = self.new_infervar();
                    let ty = Type::Ptr(var, Box::new(Type::Func(Box::new(ret), args, variadic)));
                    if variadic {
                        constrs.insert(Constr::VariadicFunc(ty.clone()), *loc)?;
                    }
                    Ok(ty)
                }
                InternMode::Define => Err(format!(
                    "intern {} in define mode",
                    ValueExt::DeclareFunc(ret, args, variadic)
                )),
            },
            ValueExt::DeclareGlobal(ty) => match mode {
                InternMode::Declare => {
                    self.intern_fresh_llir_type(&LLIRType::Ptr(Box::new(ty)), loc)
                }
                InternMode::Define => Err(format!(
                    "intern {} in define mode",
                    ValueExt::DeclareGlobal(ty)
                )),
            },
            ValueExt::DefineGlobal(ty, val) => match mode {
                InternMode::Declare => Err(format!(
                    "intern {} in declare mode",
                    ValueExt::DefineGlobal(ty, val)
                )),
                InternMode::Define => {
                    let ty = self.intern_type_value(mode, Some(&ty), &val, loc, constrs)?;
                    Ok(Type::Ptr(self.new_infervar(), Box::new(ty)))
                }
            },
            ValueExt::Poison(kind, size) => Ok(Type::Poison(kind, size)),
        }
    }
    /// Judges whether `ty1` is subtype of `ty2` at the location.
    /// See [`TypeEnv::judge_cast`].
    pub fn judge_subtype(
        &self,
        ty1: &Type,
        ty2: &Type,
        base_differs: bool,
        loc: &Loc,
        constrs: &mut Option<&mut Constrs>,
        stack: &mut Vec<(Type, Type)>,
    ) -> Result<bool, String> {
        if ty1 == ty2 {
            return Ok(true);
        }
        let ty1 = ty1.normalize(self)?;
        let ty2 = ty2.normalize(self)?;
        if ty1 == ty2 {
            return Ok(true);
        }
        match (ty1, ty2) {
            (Type::I(n1), Type::I(n2)) if !base_differs && n1 >= n2 => Ok(true),
            (Type::I(n1), Type::F(n2)) | (Type::F(n1), Type::I(n2))
                if !base_differs && n1 == n2 =>
            {
                Ok(true)
            }
            (_, Type::Vector(false, n2, _)) | (_, Type::Array(n2, _)) if *n2 == 0 => Ok(true),
            (Type::Vector(false, n1, ty1), Type::Vector(false, n2, ty2))
            | (Type::Array(n1, ty1), Type::Array(n2, ty2))
                if n1 >= n2 =>
            {
                let res12 = self.judge_subtype(ty1, ty2, base_differs, loc, constrs, stack)?;
                let res21 = self.judge_subtype(ty2, ty1, base_differs, loc, constrs, stack)?;
                Ok(res12 && res21)
            }
            (Type::Vector(false, n1, ty1), ty2) | (Type::Array(n1, ty1), ty2) if *n1 >= 1 => {
                let res12 = self.judge_subtype(ty1, ty2, base_differs, loc, constrs, stack)?;
                let res21 = self.judge_subtype(ty2, ty1, base_differs, loc, constrs, stack)?;
                Ok(res12 && res21)
            }
            (ty1, Type::Vector(false, n2, ty2)) | (ty1, Type::Array(n2, ty2)) if *n2 == 1 => {
                let res12 = self.judge_subtype(ty1, ty2, base_differs, loc, constrs, stack)?;
                let res21 = self.judge_subtype(ty2, ty1, base_differs, loc, constrs, stack)?;
                Ok(res12 && res21)
            }
            (_, Type::Struct(fields2)) if fields2.is_empty() => Ok(true),
            (Type::Struct(fields1), Type::Struct(fields2)) => {
                for i in 0..fields2.len() {
                    if i >= fields1.len() {
                        return Ok(false);
                    }
                    let (field1, field2) = (&fields1[i], &fields2[i]);
                    if i == fields2.len() - 1 {
                        if let Type::Pad(_) = &field2 {
                            return Ok(true);
                        }
                    }
                    if !self.judge_subtype(field1, field2, base_differs, loc, constrs, stack)? {
                        return Ok(false);
                    }
                    if i < fields2.len() - 1
                        && !self.judge_subtype(field2, field1, base_differs, loc, constrs, stack)?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Type::Struct(fields1), ty2) if !fields1.is_empty() => {
                self.judge_subtype(&fields1[0], ty2, base_differs, loc, constrs, stack)
            }
            (ty1, Type::Struct(fields2)) if fields2.len() == 1 => {
                self.judge_subtype(ty1, &fields2[0], base_differs, loc, constrs, stack)
            }
            (Type::Func(ret1, args1, variadic1), Type::Func(ret2, args2, variadic2)) => {
                if !(args1.len() == args2.len() && variadic1 == variadic2) {
                    return Ok(false);
                }
                if !self.judge_subtype(ret1, ret2, base_differs, loc, constrs, stack)? {
                    return Ok(false);
                }
                for (i, arg1) in args1.iter().enumerate() {
                    if !self.judge_subtype(&args2[i], arg1, base_differs, loc, constrs, stack)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Type::Nullptr, Type::Ptr(..)) => Ok(true),
            (Type::Ptr(_, rty1), Type::Ptr(_, rty2)) => {
                let key: (Type, Type) = (rty1.as_ref().clone(), rty2.as_ref().clone());
                if stack.contains(&key) {
                    return Ok(true);
                }
                stack.push(key);
                let res12 = self.judge_subtype(rty1, rty2, base_differs, loc, constrs, stack)?;
                let res21 = self.judge_subtype(rty2, rty1, base_differs, loc, constrs, stack)?;
                if !(res12 && res21) {
                    match constrs {
                        Some(constrs) => {
                            constrs.insert(Constr::NotSubtype(ty1.clone(), ty2.clone()), *loc)?
                        }
                        None => return Ok(false),
                    }
                }
                Ok(true)
            }
            (Type::Ext(eid1, _), Type::Ext(eid2, _)) if eid1 == eid2 => Ok(true),
            (Type::Ext(eid1, _), Type::Ext(eid2, _))
                if eid1.name.id() == eid2.name.id()
                    && eid1.name.is_downcast_subtarget()
                    && eid2.name.is_downcast_target() =>
            {
                Ok(true)
            }
            (_, Type::Ext(..)) => Ok(false),
            (Type::Ext(eid1, ty1), ty2) if !eid1.name.is_any_target() => {
                self.judge_subtype(ty1, ty2, base_differs, loc, constrs, stack)
            }
            _ => Ok(false),
        }
    }
    /// Judges whether `ty1` can be cast as `ty2` at the location.
    /// If `base_differs` is true, base types do not have the subtype relation each other.
    /// `stack` is internally used for avoiding infinite loop.
    pub fn judge_cast(
        &self,
        ty1: &Type,
        ty2: &Type,
        base_differs: bool,
        loc: &Loc,
        constrs: &mut Option<&mut Constrs>,
    ) -> Result<bool, String> {
        let mut stack = Vec::new();
        match (ty1, ty2) {
            (Type::Ptr(_, rty1), Type::Ptr(_, rty2)) => {
                stack.push((rty1.as_ref().clone(), rty2.as_ref().clone()));
                if !self.judge_subtype(rty1, rty2, base_differs, loc, constrs, &mut stack)? {
                    match constrs {
                        Some(constrs) => {
                            constrs.insert(Constr::Cast(ty1.clone(), ty2.clone()), *loc)?
                        }
                        None => return Ok(false),
                    }
                }
                Ok(true)
            }
            (ty1, ty2) => self.judge_subtype(ty1, ty2, base_differs, loc, constrs, &mut stack),
        }
    }
    /// Judges the given term at the location.
    pub fn judge_term(
        &mut self,
        term: JudgeTerm,
        loc: &Loc,
        constrs: &mut Constrs,
    ) -> Result<(), String> {
        match term {
            JudgeTerm::Cast(ty1, ty2) => {
                if !self.judge_cast(&ty1, &ty2, false, loc, &mut Some(constrs))? {
                    return Err(format!("cannot cast {} as {}", ty1, ty2));
                }
                Ok(())
            }
            JudgeTerm::Load(dst, src) => match &src {
                Type::Ptr(_, srcty) => {
                    if !self.judge_cast(srcty, &dst, false, loc, &mut Some(constrs))? {
                        constrs.insert(Constr::Load(dst, src.clone()), *loc)?;
                    }
                    Ok(())
                }
                _ => Err(format!("cannot load {} from {}", dst, src)),
            },
            JudgeTerm::Memcpy(dst, src, len) => {
                let dstty = match &dst {
                    Type::Ptr(_, ty) => ty,
                    _ => return Err(format!("illegal memcpy destination type {}", dst)),
                };
                let srcty = match &src {
                    Type::Ptr(_, ty) => ty,
                    _ => return Err(format!("illegal memcpy source type {}", src)),
                };
                self.insert_effect(*loc, EffectKind::Memcpy(dst.clone(), src.clone(), len));
                if let Size::Const(_) = len {
                    if let Some(dstsize) = dstty.size(self) {
                        if dstsize == len
                            && srcty.try_to_ptr_ext_ident(self).is_some()
                                == dstty.try_to_ptr_ext_ident(self).is_some()
                            && !dstty.contains_ext(self)?
                            && self.judge_cast(srcty, dstty, false, loc, &mut Some(constrs))?
                        {
                            return Ok(());
                        }
                    }
                }
                constrs.insert(Constr::Memcpy(dst.clone(), src.clone(), len), *loc)?;
                Ok(())
            }
        }
    }
    /// Judges whether values with the target type may be overwritten by values with the type at the location.
    pub fn judge_overwrite(&self, target: &Type, ty: &Type, loc: &Loc) -> Result<bool, String> {
        if self.judge_cast(target, ty, false, loc, &mut None)? {
            return Ok(true);
        }
        match ty.normalize(self)? {
            Type::Vector(_, _, ty) | Type::Array(_, ty) => self.judge_overwrite(target, ty, loc),
            Type::Struct(fields) => {
                for field in fields {
                    if self.judge_overwrite(target, field, loc)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }
    /// Judges whether values with the target types may be modified by the effect at the location.
    pub fn judge_effect_modifies(&self, effect: &Effect, target: &Type, loc: &Loc) -> bool {
        for (kind, l) in effect.iter() {
            match l.cmp_in_block(loc) {
                // The effect kind is set before than loc, hence does not interfere.
                // NOTICE that the effect kind does not interfere itself.
                Some(d) if d <= 0 => continue,
                _ => {}
            }
            match kind {
                EffectKind::CallGlobal(_) | EffectKind::CallIndirect => return true,
                EffectKind::Memcpy(dst, ..) => match dst {
                    Type::Ptr(_, dst) => {
                        if let Ok(true) = self.judge_overwrite(target, dst, loc) {
                            return true;
                        }
                    }
                    _ => unreachable!("{}: {}", loc, kind),
                },
            }
        }
        false
    }
    /// Judges whether pointers with the target type may be modified by the effect at the location.
    pub fn judge_effect_modifies_ptr(&self, effect: &Effect, target: &Type, loc: &Loc) -> bool {
        if let Type::Ptr(_, ty) = target {
            return self.judge_effect_modifies(effect, ty, loc);
        }
        false
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::fmt::DisplayMapIter;
    use crate::llir::abi::DataLayout;
    use crate::llir::interp::rtti::{ExtIdent, ExtName};
    use crate::llir::parser::Parser as LLIRParser;
    use crate::llir::syntax::{GlobalIdent, Label, LocalIdent};
    use crate::symbol::Ident;
    use crate::typechk::syntax::{AllocKind, JudgeTerm, ValueExt};
    pub fn prepare_typedefs(names: &str) -> Typedefs<ExtIdent> {
        let database = btree_map![
            LocalIdent::from("altloop1") => LLIRParser::new_type("{ %altloop2* }"),
            LocalIdent::from("altloop2") => LLIRParser::new_type("{ %altloop1* }"),
            LocalIdent::from("int") => LLIRParser::new_type("i32"),
            LocalIdent::from("tuple2") => LLIRParser::new_type("{ i32, i32 }"),
            LocalIdent::from("tuple21") => LLIRParser::new_type("{ %tuple2, i32 }"),
            LocalIdent::from("tuple3") => LLIRParser::new_type("{ i32, i32, i32 }"),
            LocalIdent::from("selfloop") => LLIRParser::new_type("{ %selfloop*, %selfloop* }"),
            LocalIdent::from("tuple2-cast-tag") => LLIRType::Ext(
                ExtIdent{name: ExtName::CastTag(Ident::from("tuple2-tag"), 0), appid: 1, offset: 0},
                Box::new(LLIRParser::new_type("i32")),
            ),
            LocalIdent::from("tuple2-cast-target") => LLIRType::Ext(
                ExtIdent{name: ExtName::CastTarget(Ident::from("tuple2-tag")), appid: 1, offset: 0},
                Box::new(LLIRParser::new_type("{ %tuple2-cast-tag, i32 }")),
            ),
            LocalIdent::from("tuple2-downcast-tag") => LLIRType::Ext(
                ExtIdent{name: ExtName::DowncastTag(Ident::from("tuple2-tag"), 0), appid: 2, offset: 0},
                Box::new(LLIRParser::new_type("i32")),
            ),
            LocalIdent::from("tuple2-downcast-target") => LLIRType::Ext(
                ExtIdent{name: ExtName::DowncastTarget(Ident::from("tuple2-tag")), appid: 2, offset: 0},
                Box::new(LLIRParser::new_type("{ %tuple2-downcast-tag, i32 }")),
            ),
            LocalIdent::from("tuple2-downcast-subtarget") => LLIRType::Ext(
                ExtIdent{name: ExtName::DowncastSubtarget(Ident::from("tuple2-tag"), 0), appid: 2, offset: 0},
                Box::new(LLIRParser::new_type("{ %tuple2-downcast-tag, i32, i32 }")),
            ),
            LocalIdent::from("tuple3-cast-tag") => LLIRType::Ext(
                ExtIdent{name: ExtName::CastTag(Ident::from("tuple3-tag"), 0), appid: 3, offset: 0},
                Box::new(LLIRParser::new_type("i32")),
            )
        ];
        let mut typedefs = Typedefs::empty();
        if names == "" {
            return typedefs;
        }
        for name in names.split(",").collect::<Vec<_>>() {
            let name = LocalIdent::from(name);
            let ty = database.get(&name).expect(&name.to_string());
            typedefs.insert(name, ty.clone());
        }
        typedefs
    }
    pub fn prepare_typeset(names: &'static str) -> BTreeMap<&'static str, Type> {
        let database = btree_map![
            "!alloca8" => Type::Poison(AllocKind::Alloca, Size::Const(8)),
            "!alloca16" => Type::Poison(AllocKind::Alloca, Size::Const(16)),
            "!mallocdyn" => Type::Poison(AllocKind::Dynamic(global_ident!("malloc")), Size::Dynamic),
            "!nullptr" => Type::Nullptr,
            "!pad4" => Type::Pad(4),
            "!tuple2" => Type::Name(LocalIdent::from("tuple2"))
        ];
        let mut typeset = BTreeMap::new();
        if names == "" {
            return typeset;
        }
        for name in names.split(",").collect::<Vec<_>>() {
            typeset.insert(name, database.get(&name).expect(&name).clone());
        }
        typeset
    }
    pub fn new_type(
        input: &str,
        loc: &Loc,
        env: &mut TypeEnv,
        typeset: &BTreeMap<&'static str, Type>,
    ) -> Type {
        match typeset.get(input) {
            Some(ty) => ty.clone(),
            None => {
                let ty = LLIRParser::new_type(input);
                env.intern_fresh_llir_type(&ty, loc).expect(input)
            }
        }
    }
    pub fn prepare_typeenv(typedefs: &Typedefs<ExtIdent>) -> TypeEnv {
        let mut env = TypeEnv::empty(DataLayout::lp64());
        let loc = Loc::new(
            GlobalIdent::from("main"),
            Label::from(LocalIdent::from("0")),
            0,
        );
        for name in typedefs.calc_order().unwrap().iter() {
            let prototype = typedefs.get(name).expect(&name.to_string());
            let ty = env
                .intern_fresh_llir_type(prototype, &loc)
                .expect(&name.to_string());
            env.define_type(*name, prototype.clone(), ty)
                .expect(&name.to_string());
        }
        env
    }
    #[test]
    fn intern_fresh_llir_type() {
        for (expected, input) in vec![
            ("Ok(void)", "void"),
            ("Ok(i1)", "i1"),
            ("Ok(i8)", "i8"),
            ("Ok(i16)", "i16"),
            ("Ok(i32)", "i32"),
            ("Ok(i64)", "i64"),
            ("Ok(f32)", "float"),
            ("Ok(f64)", "double"),
            ("Ok(f128)", "x86_fp80"),
            ("Ok(*<?4>i32)", "i32*"),
            ("Ok(*<?4>*<?5>i32)", "i32**"),
            ("Ok(<4>i32)", "<4 x i32>"),
            ("Ok(<vscale*4>i32)", "<vscale x 4 x i32>"),
            ("Ok([4]i32)", "[4 x i32]"),
            ("Ok({})", "{}"),
            (
                "Ok({i64, i16, pad(2), [2]i32, pad(4)})",
                "{ i64, i16, [2 x i32] }",
            ),
            ("Ok({i64, i16, [2]i32})", "<{ i64, i16, [2 x i32] }>"),
            ("Ok({i32, i32, i32})", "<{ { i32, i32 }, i32 }>"),
            ("Ok({i64, i16, i8, pad(1), pad(4)})", "{i64, {i16, i8}}"),
            ("Ok(i32 ())", "i32 ()"),
            ("Ok(i32 (...))", "i32 (...)"),
            ("Ok(i32 (i64, ...))", "i32 (i64, ...)"),
            ("Ok(i32 (i16, i8, ...))", "i32 (i16, i8, ...)"),
            ("Ok(void)", "opaque"),
            ("Ok({i32, i32})", "%tuple2"),
            ("Ok({*<?2>%selfloop, *<?3>%selfloop})", "%selfloop"),
            ("Ok({*<?0>%altloop2})", "%altloop1"),
            ("Ok({*<?1>%altloop1})", "%altloop2"),
            ("Err(cannot intern metadata type)", "metadata i32"),
            (
                "Ok(!tuple2-tag.cast-target@1+0({%tuple2-cast-tag, i32}))",
                "%tuple2-cast-target",
            ),
        ] {
            let mut env = prepare_typeenv(&prepare_typedefs(
                "tuple2,selfloop,altloop1,altloop2,tuple2-cast-tag,tuple2-cast-target",
            ));
            let ty = LLIRParser::new_type(input);
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let got = match env.intern_fresh_llir_type(&ty, &loc) {
                Ok(ty) => format!("Ok({})", ty),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn intern_value() {
        let locals = btree_map![
            "li32" => "i32",
            "lpqi32" => "[4 x i32]*",
            "lptuple2" => "%tuple2*",
            "lptuple21" => "%tuple21*",
            "lptuple2-cast-target" => "%tuple2-cast-target*",
            "lptuple2-downcast-target" => "%tuple2-downcast-target*",
            "lptuple2-downcast-subtarget" => "%tuple2-downcast-subtarget*",
            "lptuple3" => "%tuple3*",
            "lalloca8" => "!alloca8",
            "lmallocdyn" => "!mallocdyn"
        ];
        let globals = btree_map!["gi64" => "i64"];
        for (expected, input) in vec![
            // basic constants
            ("Ok(nullptr; [])", "i8* null"),
            ("Ok(void; [])", "i32 undef"), // undef cannot be used in outer context
            ("Ok(i1; [])", "i1 false"),
            ("Ok(i1; [])", "i1 true"),
            ("Ok(i8; [])", "i8 8"),
            ("Ok(i16; [])", "i16 16"),
            ("Ok(i32; [])", "i32 32"),
            ("Ok(i64; [])", "i64 64"),
            ("Ok(f32; [])", "float 32.32"),
            ("Ok(f64; [])", "double 64.64"),
            ("Ok(f128; [])", "x86_fp80 0xK7FFF8000000000000000"),
            // vectors
            ("Ok(<0>void; [])", "<0 x i32> <>"),
            ("Ok(<1>i32; [])", "<1 x i32> <i32 1>"),
            ("Ok(<2>i32; [])", "<2 x i32> <i32 1, i32 2>"),
            ("Ok(<2>i32; [@main%0#0: f64 is cast as i32])", "<2 x i32> <i32 1, double 2>"),
            // array constants
            ("Ok([3]i8; [])", r#"[3 x i8] c"CAD""#),
            // arrays
            ("Ok([0]void; [])", "[0 x i32] []"),
            ("Ok([1]i32; [])", "[1 x i32] [i32 1]"),
            ("Ok([2]i32; [])", "[2 x i32] [i32 1, i32 2]"),
            ("Ok([2]i32; [@main%0#0: f64 is cast as i32])", "[2 x i32] [i32 1, double 2]"),
            // structs
            ("Ok({}; [])", "{} {}"),
            (
                "Ok({i64, i16, pad(2), [2]i32, pad(4)}; [])",
                "{ i64, i16, [2 x i32]} { i64 1, i16 2, [2 x i32] [i32 3, i32 4] }"
            ),
            (
                "Ok({i64, i16, [2]i32}; [])",
                "<{ i64, i16, [2 x i32]}> <{ i64 1, i16 2, [2 x i32] [i32 3, i32 4] }>"
            ),
            (
                "Ok({i32, pad(4), i64, i32}; [@main%0#0: {i32, pad(4), i64} is cast as {i32, i32}])",
                "<{ { %int, i32 }, i32 }> <{ { %int, i32 } { i32 1, i64 2 }, i32 3 }>"
            ),
            ("Ok({i64, i16, i8, pad(1), pad(4)}; [])", "{i64, {i16, i8}} {i64 1, {i16, i8} {i16 2, i8 3}}"),
            // local variables
            ("Ok(i32; [])", "i32 %li32"),
            // global variables
            ("Ok(i64; [])", "i64 @gi64"),
            // aggegate operators: extractvalue
            ("Ok(i32; [])", "i32 extractvalue ([2 x i32] { i32 1, i32 2 }, 1)"),
            (
                "Err(out-of-bound offset 8 in [2]i32 with size 8)",
                "i32 extractvalue ([3 x i32] [i32 1, i32 2], 2)"
            ),
            (
                "Err(in-bound offset 2 in [2]i32 with element size 4)",
                "i8 extractvalue ([8 x i8] [i32 1, i32 2], 2)"
            ),
            ("Ok(f32; [])", "float extractvalue ({ i32, float } { i32 1, float 2.0 }, 1)"),
            (
                "Err(in-bound offset 4 in {i64, f32, pad(4)})",
                "float extractvalue ({ i32, float } { i64 1, float 2.0 }, 1)"
            ),
            (
                "Err(out-of-bound offset 8 in {i32, f32})",
                "float extractvalue ({ i32, float, float } { i32 1, float 2.0 }, 2)"
            ),
            ("Err(illegal base type i32)", "void extractvalue (i32 0, 1)"),
            // aggregate operators: insertvalue
            ("Ok([2]i32; [])", "[2 x i32] insertvalue ([2 x i32] undef, i32 3, 1)"),
            ("Ok({i32, f32}; [])", "{ i32, float } insertvalue ({ i32, float } undef, float 3.0, 1)"),
            (
                "Ok({i32, f32}; [@main%0#0: i64 is cast as f32])",
                "{ i32, float } insertvalue ({ i32, float } undef, i64 2, 1)"
            ),
            // binary operators
            ("Ok(i32; [])", "i32 add (i32 %li32, i32 2)"),
            ("Err(cannot operate i32 and i64)", "i32 add (i32 %li32, i64 2)"),
            ("Ok(i32; [@main%0#0: nullptr is cast as i32])", "i32 add (i32 null, i32 1)"),
            ("Ok(i32; [@main%0#0: nullptr is cast as i32])", "i32 add (i32 1, i32 null)"),
            // comparison operators
            ("Ok(i1; [])", "i1 icmp eq (i32 %li32, i32 0)"),
            ("Err(cannot compare i32 and i64)", "i1 icmp eq (i32 %li32, i64 0)"),
            ("Ok(i1; [@main%0#0: nullptr is cast as i32])", "i1 icmp eq (i32 null, i32 0)"),
            ("Ok(i1; [@main%0#0: nullptr is cast as i32])", "i1 icmp eq (i32 0, i32 null)"),
            // conversion operators: bitcast on poison types (tests ValueExt::CollapsePoison also)
            (
                "Ok(*<?7>i64; [@main%0#0: *<?7>i64 is allocated with alloca as normal object])",
                "i64* bitcast (i8* %lalloca8 to i64*)"
            ),
            ("Err(cannot cast poison(alloca, 8) as i64)", "i64 bitcast (i8* %lalloca8 to i64)"),
            (
                "Ok(*<?7>[4]i64; [@main%0#0: allocation size of *<?7>[4]i64 does not match with poison with size 8])",
                "[4 x i64]* bitcast (i8* %lalloca8 to [4 x i64]*)"
            ),
            (
                "Ok(*<?7><vscale*4>i64; [@main%0#0: allocation size of *<?7><vscale*4>i64 does not match with poison with size 8])",
                "i64** bitcast (i8* %lalloca8 to <vscale x 4 x i64>*)"
            ),
            (
                "Ok(*<?7>i64; [@main%0#0: allocation size of *<?7>i64 does not match with poison with dynamic size])",
                "i64* bitcast (i8* %lmallocdyn to i64*)"
            ),
            (
                "Ok(*<?7>%tuple2-cast-target; [@main%0#0: *<?7>%tuple2-cast-target is allocated with alloca as containing extension types])",
                "i32* bitcast (i8* %lalloca8 to %tuple2-cast-target*)"
            ),
            // conversion operators: inttoptr
            ("Ok(*<?7>i8; [@main%0#0: i64 is cast as *<?7>i8])", "i8* inttoptr (i64 64 to i8*)"),
            // conversion operators: others (no problem with this alone)
            ("Ok(i64; [])", "i64 ptrtoint (i8* null to i64)"),
            ("Ok(i32; [])", "i32 trunc (i64 64 to i32)"),
            // getelementptrs: on arrays
            ("Ok(*<?0>i32; [])", "i32* getelementptr ([4 x i32], [4 x i32]* %lpqi32, i32 0, i32 2)"),
            (
                "Ok(*<?0>i32; [@main%0#0: out-of-bound offset 16 in *<?0>[4]i32])",
                "i32* getelementptr ([4 x i32], [4 x i32]* %lpqi32, i32 0, i32 4)"
            ),
            (
                "Ok(*<?0>i32; [@main%0#0: out-of-bound offset -4 in *<?0>[4]i32])",
                "i32* getelementptr ([4 x i32], [4 x i32]* %lpqi32, i32 0, i32 -1)"
            ),
            (
                "Ok(*<?0>i32; [@main%0#0: out-of-bound offset 0+4*(i32 %li32) in *<?0>[4]i32])",
                "i32* getelementptr ([4 x i32], [4 x i32]* %lpqi32, i32 0, i32 %li32)"
            ),
            (
                "Ok(*<?0>i32; [@main%0#0: non-zero index 0+16*(i32 %li32) from *<?0>[4]i32])",
                "i32* getelementptr ([4 x i32], [4 x i32]* %lpqi32, i32 %li32, i32 0)"
            ),
            // getelementptrs: on structs
            ("Ok(*<?5>i32; [])", "i32* getelementptr (%tuple21, %tuple21* %lptuple21, i32 0, i32 1)"),
            ("Err(illegal index 2 in base type %tuple21)", "i32* getelementptr (%tuple21, %tuple21* %lptuple21, i32 0, i32 2)"),
            ("Err(illegal index -1 in base type %tuple21)", "i32* getelementptr (%tuple21, %tuple21* %lptuple21, i32 0, i32 -1)"),
            ("Err(illegal index %li32 in base type %tuple21)", "i32* getelementptr (%tuple21, %tuple21* %lptuple21, i32 0, i32 %li32)"),
            ("Ok(*<?5>i32; [@main%0#0: non-zero index 0+12*(i32 %li32) from *<?5>%tuple21])", "i32* getelementptr (%tuple21, %tuple21* %lptuple21, i32 %li32, i32 1)"),
            // getelementptrs: on unexpected base pointer types
            (
                "Ok(*<?1>i32; [@main%0#0: *<?1>%tuple2 is cast as *<?7>%tuple21])",
                "i32* getelementptr (%tuple21, %tuple21* %lptuple2, i32 0, i32 1)"
            ),
            (
                "Err(illegal base pointer type i32)",
                "i32* getelementptr (%tuple21, %tuple21* %li32, i32 0, i32 1)"
            ),
            // getelementptrs: on refinement annotated types
            (
                "Ok(*<?2>!tuple2-tag.cast-tag0@1+0(i32); [])",
                "i32* getelementptr (%tuple2-cast-target, %tuple2-cast-target* %lptuple2-cast-target, i32 0, i32 0)"
            ),
            (
                "Ok(*<?2>i32; [@main%0#0: escape i32 from *<?2>%tuple2-cast-target at offset 4 via getelementptr])",
                "i32* getelementptr (%tuple2-cast-target, %tuple2-cast-target* %lptuple2-cast-target, i32 0, i32 1)"
            ),
            (
                "Ok(*<?4>i32; [@main%0#0: *<?4>%tuple2-downcast-target is cast as *<?7>%tuple3])",
                "i32* getelementptr (%tuple3, %tuple3* %lptuple2-downcast-target, i32 0, i32 0)"
            ),
            (
                "Ok(*<?4>i32; [@main%0#0: *<?4>%tuple2-downcast-target is cast as *<?7>%tuple3])",
                "i32* getelementptr (%tuple3, %tuple3* %lptuple2-downcast-target, i32 0, i32 1)"
            ),
            (
                "Ok(*<?4>i32; [@main%0#0: *<?4>%tuple2-downcast-target is cast as *<?7>%tuple3, @main%0#0: escape i32 from *<?4>%tuple2-downcast-target at offset 8 via getelementptr])",
                "i32* getelementptr (%tuple3, %tuple3* %lptuple2-downcast-target, i32 0, i32 2)"
            ),
            (
                "Ok(*<?4>!tuple2-tag.downcast-tag0@2+0(i32); [])",
                "i32* getelementptr (%tuple2-downcast-target, %tuple2-downcast-target* %lptuple2-downcast-target, i32 0, i32 0)"
            ),
            (
                "Ok(*<?4>i32; [])",
                "i32* getelementptr (%tuple2-downcast-target, %tuple2-downcast-target* %lptuple2-downcast-target, i32 0, i32 1)"
            ),
            // unary operators
            ("Ok(f64; [])", "double fneg (double 1)"),
            ("Ok(f64; [@main%0#0: nullptr is cast as f64])", "double fneg (double null)"),
            // vector operators: extractelement
            ("Ok(i64; [])", "i64 extractelement <2 x i64> <i64 1, i64 2>, i32 0"),
            ("Err(cannot cast nullptr as i32)", "i64 extractelement <2 x i64> <i64 1, i64 2>, i32 null"),
            ("Err(illegal value: i64)", "void extractelement i64 3, i32 0"),
            // vector operators: insertelement
            ("Ok(<2>i64; [])", "<2 x i64> insertelement <2 x i64> <i64 1, i64 2>, i64 3, i32 0"),
            ("Err(cannot cast nullptr as i64)", "<2 x i64> insertelement <2 x i64> <i64 1, i64 2>, i64 null, i32 0"),
            ("Err(cannot cast nullptr as i32)", "<2 x i64> insertelement <2 x i64> <i64 1, i64 2>, i64 3, i32 null"),
            ("Ok(<2>i64; [])", "<2 x i64> insertelement <2 x i64> undef, i64 3, i32 0"),
            // vector operators: shufflevector
            ("Ok(<3>i64; [])", "<3 x i64> shufflevector <2 x i64> <i64 1, i64 2>, <1 x i64> <i64 3>, <3 x i32> <i32 1, i32 2, i32 0>"),
            ("Ok(<3>i64; [])", "<3 x i64> shufflevector <2 x i64> undef, <1 x i64> undef, <3 x i32> zeroinitializer"),
            ("Err(illegal v1 type i64)", "void shufflevector i64 1, <1 x i64> undef, <3 x i32> zeroinitializer"),
            ("Err(illegal v2 type i64)", "void shufflevector <2 x i64> undef, i64 2, <3 x i32> zeroinitializer"),
            ("Err(illegal mask type <3>i64)", "void shufflevector <2 x i64> undef, <1 x i64> undef, <3 x i64> zeroinitializer"),
            // zeroinitializers
            ("Err(illegal zeroinitializer)", "void zeroinitializer"), // illegal in outer context
            // block addresses
            ("Ok(*<?7>i8; [])", "i8* blockaddress(@func, %1)"),
            // metadatas
            ("Err(cannot intern metadata value !1)", "metadata !1"),
        ] {
            let mut env = prepare_typeenv(&prepare_typedefs("int,tuple2,tuple21,tuple2-cast-tag,tuple2-cast-target,tuple2-downcast-tag,tuple2-downcast-target,tuple2-downcast-subtarget,tuple3"));
            let typeset = prepare_typeset("!alloca8,!mallocdyn");
            let loc = Loc::new(GlobalIdent::from("main"), Label::from(LocalIdent::from("0")), 0);
            for (name, ty) in &locals {
                let ty = new_type(ty, &loc, &mut env, &typeset);
                let varname = VarName::Local(LocalIdent::from(*name), loc.func);
                env.declare_var(varname, ty).expect(name);
            }
            for (name, ty) in &globals {
                let ty = new_type(ty, &loc, &mut env, &typeset);
                let varname = VarName::Global(GlobalIdent::from(*name));
                env.declare_var(varname, ty).expect(name);
            }
            let tyval = LLIRParser::new_typed_value(input);
            let mut constrs = Constrs::empty();
            let got = match env.intern_value_expr(InternMode::Define, &tyval.1, &loc, &mut constrs) {
                Ok(ty) => format!("Ok({}; {})", ty, constrs),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn intern_value_ext() {
        for (expected_declare, expected_define, val) in vec![
            (
                "Ok(*<?0>i32; [@main%0#0: *<?0>i32 is allocated with alloca as normal object])",
                "Ok(*<?1>i32; [@main%0#0: *<?0>i32 is allocated with alloca as normal object, @main%0#0: *<?1>i32 is allocated with alloca as normal object])",
                ValueExt::Alloc(AllocKind::Alloca, LLIRParser::new_type("i32"))
            ),
            (
                "Ok(*<?0>%tuple2-cast-target; [@main%0#0: *<?0>%tuple2-cast-target is allocated with alloca as containing extension types])",
                "Ok(*<?1>%tuple2-cast-target; [@main%0#0: *<?0>%tuple2-cast-target is allocated with alloca as containing extension types, @main%0#0: *<?1>%tuple2-cast-target is allocated with alloca as containing extension types])",
                ValueExt::Alloc(
                    AllocKind::Alloca,
                    LLIRParser::new_type("%tuple2-cast-target")
                )
            ),
            (
                "Ok(*<?0>i32 (i64, i16); [])",
                "Err(intern declare-func(i32, [i64, i16], false) in define mode)",
                ValueExt::DeclareFunc(Type::I(32), vec![Type::I(64), Type::I(16)], false)
            ),
            (
                "Ok(*<?0>i32 (i64, i16, ...); [@main%0#0: variadic function *<?0>i32 (i64, i16, ...)])",
                "Err(intern declare-func(i32, [i64, i16], true) in define mode)",
                ValueExt::DeclareFunc(Type::I(32), vec![Type::I(64), Type::I(16)], true)
            ),
            (
                "Ok(*<?0>i32; [])",
                "Err(intern declare-global(i32) in define mode)",
                ValueExt::DeclareGlobal(LLIRParser::new_type("i32"))
            ),
            (
                "Err(intern define-global([1024 x i8], zeroinitializer) in declare mode)",
                "Ok(*<?0>[1024]i8; [])",
                ValueExt::DefineGlobal(
                    LLIRParser::new_type("[1024 x i8]"),
                    LLIRParser::new_value("zeroinitializer")
                )
            ),
        ] {
            let mut env = prepare_typeenv(&prepare_typedefs("tuple2,tuple2-cast-tag,tuple2-cast-target"));
            let loc = Loc::new(GlobalIdent::from("main"), Label::from(LocalIdent::from("0")), 0);
            let mut constrs = Constrs::empty();
            let got = match env.intern_value_ext(InternMode::Declare, val.clone(), &loc, &mut constrs) {
                Ok(ty) => format!("Ok({}; {})", ty, constrs),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected_declare, got, "{} in declare mode", val);
            let got = match env.intern_value_ext(InternMode::Define, val.clone(), &loc, &mut constrs) {
                Ok(ty) => format!("Ok({}; {})", ty, constrs),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected_define, got, "{} in define mode", val);
        }
    }
    #[test]
    fn judge_term_cast() {
        for (expected, (ty1str, ty2str)) in vec![
            // basic types
            ("Ok([])", ("i32", "i32")),
            ("Ok([])", ("i64", "i32")),
            ("Ok([])", ("float", "i32")),
            ("Ok([])", ("i32", "float")),
            ("Ok([])", ("double", "i64")),
            ("Ok([])", ("i64", "double")),
            ("Ok([])", ("i32", "%int")),
            ("Ok([])", ("%int", "i32")),
            ("Err(cannot cast void as i32)", ("void", "i32")),
            ("Err(cannot cast i32 as void)", ("i32", "void")),
            ("Err(cannot cast i32 as i64)", ("i32", "i64")),
            ("Err(cannot cast f64 as f32)", ("double", "float")),
            ("Err(cannot cast f32 as f64)", ("float", "double")),
            ("Err(cannot cast i64 as f32)", ("i64", "float")),
            ("Err(cannot cast f64 as i32)", ("double", "i32")),
            // vector types
            ("Ok([])", ("i64", "<0 x i8>")),
            ("Ok([])", ("<5 x i8>", "<3 x i8>")),
            ("Err(cannot cast <5>i8 as <7>i8)", ("<5 x i8>", "<7 x i8>")),
            ("Ok([])", ("<5 x i8>", "i8")),
            ("Ok([])", ("i8", "<1 x i8>")),
            // array types
            ("Ok([])", ("i64", "[0 x i8]")),
            ("Ok([])", ("[5 x i8]", "[3 x i8]")),
            ("Err(cannot cast [5]i8 as [7]i8)", ("[5 x i8]", "[7 x i8]")),
            ("Ok([])", ("[5 x i8]", "i8")),
            ("Ok([])", ("i8", "[1 x i8]")),
            // struct types
            ("Ok([])", ("i64", "{}")),
            ("Ok([])", ("%tuple3", "%tuple2")),
            ("Err(cannot cast {i32, i32} as {i32, i32, i32})", ("%tuple2", "%tuple3")),
            ("Ok([])", ("{ i32, i8, i8 }", "{ i32, i8 }")), // ignore trailing padding
            ("Err(cannot cast {[4]i32, i64} as {[2]i32, i64})", ("{ [4 x i32], i64 }", "{ [2 x i32], i64 }")),
            ("Ok([])", ("{ i64, i32 }", "i64")),
            ("Ok([])", ("i64", "{ i64 }")),
            // function types
            // NOTE: LLVM Clang actually emits functions as destructuring structure arguments
            //   and reconstructing them in local variable ...
            ("Ok([])", ("i32 (i32)", "i32 ({ i32, i32 })")),
            (
                "Err(cannot cast i32 ({i32, i32}) as i32 (i32))",
                ("i32 ({ i32, i32 })", "i32 (i32)"),
            ),
            ("Ok([])", ("{ i32, i32 } (i32)", "i32 (i32)")),
            (
                "Err(cannot cast i32 (i32) as {i32, i32} (i32))",
                ("i32 (i32)", "{ i32, i32 } (i32)"),
            ),
            ("Ok([])", ("i32 (i64, ...)", "i32 (i64, ...)")),
            (
                "Err(cannot cast i32 (i64) as i32 (i64, ...))",
                ("i32 (i64)", "i32 (i64, ...)"),
            ),
            (
                "Err(cannot cast i32 (i64, ...) as i32 (i64))",
                ("i32 (i64, ...)", "i32 (i64)"),
            ),
            // null pointer types
            ("Ok([])", ("!nullptr", "i8*")),
            // padding types
            ("Err(cannot cast pad(4) as i32)", ("!pad4", "i32")),
            ("Err(cannot cast i32 as pad(4))", ("i32", "!pad4")),
            // poison types
            ("Err(cannot cast poison(alloca, 16) as *<?2>i8)", ("!alloca16", "i8*")),
            ("Err(cannot cast *<?2>i8 as poison(alloca, 16))", ("i8*", "!alloca16")),
            // pointer types
            ("Ok([])", ("i32*", "i32*")),
            ("Ok([])", ("i32**", "i32**")),
            ("Ok([@main%0#0: *<?2>i32 is cast as *<?3>i64])", ("i32*", "i64*")),
            ("Ok([@main%0#0: *<?3>i32 is not subtype of *<?5>i64])", ("i32**", "i64**")),
            (
                "Ok([@main%0#0: *<?2>{i32, i32, i32} is not subtype of *<?3>{i32, i32}])",
                ("{ i64, { i32, i32, i32 }* }", "{ i64, { i32, i32 }* }"),
            ),
            ("Ok([])", ("%altloop1*", "%altloop2*")), // avoid infinite loop
            // refinement annotated types
            ("Ok([])", ("%tuple2-cast-tag", "%tuple2-cast-tag")),
            ("Err(cannot cast !tuple3-tag.cast-tag0@3+0(i32) as !tuple2-tag.cast-tag0@1+0(i32))", ("%tuple3-cast-tag", "%tuple2-cast-tag")),
            ("Ok([])", ("%tuple2-downcast-subtarget", "%tuple2-downcast-target")), // upcast from subtarget permitted
            (
                "Err(cannot cast !tuple2-tag.downcast-target@2+0({%tuple2-downcast-tag, i32}) as !tuple2-tag.downcast-subtarget0@2+0({%tuple2-downcast-tag, i32, i32}))",
                ("%tuple2-downcast-target", "%tuple2-downcast-subtarget")
            ), // any downcast forbidden
            (
                "Err(cannot cast {i32, i32} as !tuple2-tag.cast-target@1+0({%tuple2-cast-tag, i32}))",
                ("%tuple2", "%tuple2-cast-target"),
            ), // target cast forbidden because its underlying type varies.
            (
                "Err(cannot cast i32 as !tuple2-tag.cast-tag0@1+0(i32))",
                ("i32", "%tuple2-cast-tag"),
            ), // any downcast forbidden
            (
                "Err(cannot cast !tuple2-tag.cast-target@1+0({%tuple2-cast-tag, i32}) as {i32, i32})",
                ("%tuple2-cast-target", "%tuple2"),
            ), // target cast forbidden because its underlying type varies.
            ("Ok([])", ("%tuple2-cast-tag", "i32")), // other any upcast permitted
        ] {
            let mut env = prepare_typeenv(&prepare_typedefs(
                "int,tuple2,tuple3,altloop1,altloop2,tuple2-cast-tag,tuple2-cast-target,tuple3-cast-tag,tuple2-downcast-tag,tuple2-downcast-target,tuple2-downcast-subtarget",
            ));
            let typeset = prepare_typeset("!nullptr,!pad4,!alloca16");
            let loc = Loc::new(GlobalIdent::from("main"), Label::from(LocalIdent::from("0")), 0);
            let ty1 = new_type(ty1str, &loc, &mut env, &typeset);
            let ty2 = new_type(ty2str, &loc, &mut env, &typeset);
            let term = JudgeTerm::Cast(ty1, ty2);
            let mut constrs = Constrs::empty();
            let got = match env.judge_term(term, &loc, &mut constrs) {
                Ok(()) => format!("Ok({})", constrs),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "({}, {})", ty1str, ty2str);
        }
    }
    #[test]
    fn judge_term_load() {
        for (expected, (dst, src)) in vec![
            ("Ok([])", ("i32", "i32*")),
            ("Ok([])", ("i32*", "i32**")),
            ("Ok([@main%0#0: load i32 from *<?0>void])", ("i32", "void*")),
            ("Err(cannot load i32 from i64)", ("i32", "i64")),
        ] {
            let mut env = prepare_typeenv(&prepare_typedefs(""));
            let typeset = prepare_typeset("");
            let loc = Loc::new(
                GlobalIdent::from("main"),
                Label::from(LocalIdent::from("0")),
                0,
            );
            let dstty = new_type(dst, &loc, &mut env, &typeset);
            let srcty = new_type(src, &loc, &mut env, &typeset);
            let term = JudgeTerm::Load(dstty, srcty);
            let mut constrs = Constrs::empty();
            let got = match env.judge_term(term, &loc, &mut constrs) {
                Ok(()) => format!("Ok({})", constrs),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "({}, {})", dst, src);
        }
    }
    #[test]
    fn judge_term_memcpy() {
        for (expected, (dst, src, len)) in vec![
            (
                "Ok([]; [@main%0#0 -> effect[memcpy(*<?0>%tuple2, *<?1>%tuple3, Const(8))@main%0#0]])",
                ("%tuple2*", "%tuple3*", Size::Const(8))
            ),
            (
                "Ok([@main%0#0: memcpy *<?1>%tuple3 to *<?0>%tuple2 with length 12]; [@main%0#0 -> effect[memcpy(*<?0>%tuple2, *<?1>%tuple3, Const(12))@main%0#0]])",
                ("%tuple2*", "%tuple3*", Size::Const(12))
            ),
            (
                "Ok([@main%0#0: memcpy *<?1>%tuple2 to *<?0>%tuple3 with length 12]; [@main%0#0 -> effect[memcpy(*<?0>%tuple3, *<?1>%tuple2, Const(12))@main%0#0]])",
                ("%tuple3*", "%tuple2*", Size::Const(12))
            ),
            (
                "Ok([@main%0#0: memcpy *<?1>%tuple2 to *<?0>%tuple3 with length 8]; [@main%0#0 -> effect[memcpy(*<?0>%tuple3, *<?1>%tuple2, Const(8))@main%0#0]])",
                ("%tuple3*", "%tuple2*", Size::Const(8))
            ),
            (
                "Ok([@main%0#0: memcpy *<?2>*<?3>%tuple3 to *<?0>*<?1>%tuple2 with length 64]; [@main%0#0 -> effect[memcpy(*<?0>*<?1>%tuple2, *<?2>*<?3>%tuple3, Const(64))@main%0#0]])",
                ("%tuple2**", "%tuple3**", Size::Const(64))
            ),
            (
                "Ok([@main%0#0: memcpy *<?2>*<?3>%tuple3 to *<?0>*<?1>%tuple2 with dynamic length]; [@main%0#0 -> effect[memcpy(*<?0>*<?1>%tuple2, *<?2>*<?3>%tuple3, Dynamic)@main%0#0]])",
                ("%tuple2**", "%tuple3**", Size::Dynamic)
            ),
            (
                "Err(illegal memcpy destination type {i32, i32})",
                ("%tuple2", "%tuple3*", Size::Dynamic)
            ),
            (
                "Err(illegal memcpy source type {i32, i32, i32})",
                ("%tuple2*", "%tuple3", Size::Dynamic)
            ),
            (
                "Ok([@main%0#0: memcpy *<?1>i32 to *<?0>%tuple2-cast-tag with length 4]; [@main%0#0 -> effect[memcpy(*<?0>%tuple2-cast-tag, *<?1>i32, Const(4))@main%0#0]])",
                ("%tuple2-cast-tag*", "i32*", Size::Const(4))
            ),
            (
                "Ok([]; [@main%0#0 -> effect[memcpy(*<?0>i32, *<?1>%tuple2-cast-tag, Const(4))@main%0#0]])",
                ("i32*", "%tuple2-cast-tag*", Size::Const(4))
            ),
            (
                "Ok([@main%0#0: memcpy *<?2>*<?3>%tuple2-cast-tag to *<?0>*<?1>i32 with length 8]; [@main%0#0 -> effect[memcpy(*<?0>*<?1>i32, *<?2>*<?3>%tuple2-cast-tag, Const(8))@main%0#0]])",
                ("i32**", "%tuple2-cast-tag**", Size::Const(8))
            ),
            // NOTICE that copy between the same refined types may break the invariance.
            (
                "Ok([@main%0#0: memcpy *<?1>%tuple2-cast-tag to *<?0>%tuple2-cast-tag with length 4]; [@main%0#0 -> effect[memcpy(*<?0>%tuple2-cast-tag, *<?1>%tuple2-cast-tag, Const(4))@main%0#0]])",
                ("%tuple2-cast-tag*", "%tuple2-cast-tag*", Size::Const(4))
            ),
        ] {
            let mut env = prepare_typeenv(&prepare_typedefs("tuple2,tuple3,tuple2-cast-tag"));
            let typeset = prepare_typeset("");
            let loc = Loc::new(GlobalIdent::from("main"), Label::from(LocalIdent::from("0")), 0);
            let dstty = new_type(dst, &loc, &mut env, &typeset);
            let srcty = new_type(src, &loc, &mut env, &typeset);
            let term = JudgeTerm::Memcpy(dstty, srcty, len);
            let mut constrs = Constrs::empty();
            let result = match env.judge_term(term, &loc, &mut constrs) {
                Ok(()) => format!(
                    "Ok({}; {})",
                    constrs,
                    DisplayMapIter("[", env.effectset().iter(), " -> ", ", ", "]")
                ),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, result, "({}, {}, {:?})", dst, src, len);
        }
    }
}
