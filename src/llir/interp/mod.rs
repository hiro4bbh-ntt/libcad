//! The interpreter of LLIR.

use crate::llir::abi::{DataLayout, GetelementptrResult};
use crate::llir::syntax::{
    BinOpArgs, BinOpcode, CallBody, Callee, CmpOpArgs, CmpOpcode, ConvOpArgs, ConvOpcode,
    GlobalIdent, IcmpCond, Insn, Loc, LocalIdent, ParamValue, Type as LLIRType, TypedValue,
    Typedefs, Value, WrapMode,
};
use std::cmp;
use std::collections::BTreeMap;
use std::fmt;
use std::mem;

pub mod rtti;
pub mod syntax;
use rtti::{ExtIdent, ExtName};
use syntax::{Addr, Const, Cont, Effect, Error, Func, PoisonVal, Region, State, Val};

/// A view on a value.
#[derive(Clone, Debug)]
pub struct ValView {
    val: Val,
    offset: i64,
    size: i64,
    pad: bool,
}

impl ValView {
    /// Returns a new view on an empty value.
    pub fn empty() -> ValView {
        ValView {
            val: Val::empty(),
            offset: 0,
            size: 0,
            pad: false,
        }
    }
    /// Returns the value.
    pub fn val(&self) -> &Val {
        &self.val
    }
    /// Returns the offset of the view.
    pub fn offset(&self) -> i64 {
        self.offset
    }
    /// Returns the size of the view.
    pub fn size(&self) -> i64 {
        self.size
    }
    /// Returns the pair of the index and the offset delta from the offset of the view.
    pub fn index_delta(&self) -> Result<(usize, i64), Error> {
        if self.offset >= 0 {
            let mut p = 0;
            for (i, c) in self.val.iter().enumerate() {
                let delta = self.offset - p;
                if delta < 0 {
                    continue;
                }
                let size = c.size();
                if delta < size {
                    return Ok((i, delta));
                }
                p += size;
            }
        }
        Err(Error::OutOfBoundInRegion(self.clone()))
    }
    /// Returns a `n`-bit integer with the index and offset delta read from the offset of the view.
    pub fn try_read_int(&self, n: i64) -> Result<(i64, usize, i64), Error> {
        assert!((1..=64).contains(&n), "unsupported read i{} value", n);
        let (idx, delta) = self.index_delta()?;
        let shift = delta * 8;
        let mask = match n {
            64 => !0u64,
            _ => ((1 << n) - 1) << shift,
        };
        let x = match self.val.get(idx) {
            Some(Const::I1(b, true)) if shift + n <= 1 => match b {
                true => 1,
                false => 0,
            },
            Some(Const::I8(x, m)) if shift + n <= 8 && mask & (*m as u64) == mask => {
                *x as i64 >> shift
            }
            Some(Const::I16(x, m)) if shift + n <= 16 && mask & (*m as u64) == mask => {
                *x as i64 >> shift
            }
            Some(Const::I32(x, m)) if shift + n <= 32 && mask & (*m as u64) == mask => {
                *x as i64 >> shift
            }
            Some(Const::I64(x, m)) if shift + n <= 64 && mask & *m == mask => *x >> shift,
            _ => return Err(Error::ReadInt(self.clone(), n)),
        };
        let x = match n >= 64 {
            true => x,
            false => x & ((1 << n) - 1),
        };
        Ok((x, idx, delta))
    }
    /// Returns the `i1` value read from the offset of the view.
    pub fn try_read_i1(&self) -> Result<bool, Error> {
        Ok(self.try_read_int(1)?.0 != 0)
    }
    /// Returns the `i8` value read from the offset of the view.
    pub fn try_read_i8(&self) -> Result<i8, Error> {
        Ok(self.try_read_int(8)?.0 as i8)
    }
    /// Returns the `i16` value read from the offset of the view.
    pub fn try_read_i16(&self) -> Result<i16, Error> {
        Ok(self.try_read_int(16)?.0 as i16)
    }
    /// Returns the `i32` value read from the offset of the view.
    pub fn try_read_i32(&self) -> Result<i32, Error> {
        Ok(self.try_read_int(32)?.0 as i32)
    }
    /// Returns the `i64` value read from the offset of the view.
    pub fn try_read_i64(&self) -> Result<i64, Error> {
        Ok(self.try_read_int(64)?.0)
    }
    /// Returns the `float` value read from the offset of the view.
    pub fn try_read_float(&self) -> Result<f32, Error> {
        let (idx, delta) = self.index_delta()?;
        if delta == 0 {
            if let Some(Const::Float(Some(n))) = self.val.get(idx) {
                return Ok(*n);
            }
        }
        Err(Error::TryTo(self.clone(), LLIRType::Float))
    }
    /// Returns the `double` value read from the offset of the view.
    pub fn try_read_double(&self) -> Result<f64, Error> {
        let (idx, delta) = self.index_delta()?;
        if delta == 0 {
            if let Some(Const::Double(Some(n))) = self.val.get(idx) {
                return Ok(*n);
            }
        }
        Err(Error::TryTo(self.clone(), LLIRType::Double))
    }
    /// Returns an address read from the offset of the view.
    pub fn try_read_addr_of(&self, ty: &LLIRType<ExtIdent>) -> Result<&Addr, Error> {
        let (idx, delta) = self.index_delta()?;
        if delta == 0 {
            if let Some(Const::Addr(Some(a))) = self.val.get(idx) {
                return Ok(a);
            }
        }
        Err(Error::TryTo(
            self.clone(),
            LLIRType::Ptr(Box::new(ty.clone())),
        ))
    }
    /// Returns a value read from the offset of the view.
    pub fn try_read(&self, ty: &LLIRType<ExtIdent>) -> Result<Val, Error> {
        match ty {
            LLIRType::I1 => Ok(Val::from(Const::I1(self.try_read_i1()?, true))),
            LLIRType::I8 => Ok(Val::from(Const::I8(self.try_read_i8()?, !0))),
            LLIRType::I16 => Ok(Val::from(Const::I16(self.try_read_i16()?, !0))),
            LLIRType::I32 => Ok(Val::from(Const::I32(self.try_read_i32()?, !0))),
            LLIRType::I64 => Ok(Val::from(Const::I64(self.try_read_i64()?, !0))),
            LLIRType::Float => Ok(Val::from(Const::Float(Some(self.try_read_float()?)))),
            LLIRType::Double => Ok(Val::from(Const::Double(Some(self.try_read_double()?)))),
            LLIRType::Ptr(ty) => Ok(Val::from(Const::Addr(Some(
                self.try_read_addr_of(ty)?.clone(),
            )))),
            _ => Err(Error::CastAs(self.clone(), ty.clone())),
        }
    }
    fn push(&mut self, c: Const) {
        self.size += c.size();
        self.val.push(c);
    }
    /// Pushes the padding for alignment.
    pub fn push_pad(&mut self, align: i64) {
        let n = (self.size + align - 1) / align * align - self.size;
        if n > 0 {
            self.push(Const::Pad(n));
        }
        self.pad = false;
    }
    /// Pushes the constant with optional padding.
    pub fn push_const(&mut self, c: Const, pad: bool) {
        if pad {
            self.push_pad(c.align());
        }
        self.push(c);
        self.pad = true;
    }
    /// Pushes the value with optional padding.
    pub fn push_val(&mut self, v: Val, pad: bool) {
        for c in v.into_iter() {
            self.push_const(c, pad);
        }
    }
    /// Pushes the undefined value with the given type and optional padding.
    pub fn push_undef(
        &mut self,
        ty: &LLIRType<ExtIdent>,
        pad: bool,
        typedefs: &Typedefs<ExtIdent>,
    ) -> Result<(), Error> {
        match ty.normalize(typedefs) {
            Ok(LLIRType::I1) => self.push_const(Const::I1(false, false), pad),
            Ok(LLIRType::I8) => self.push_const(Const::I8(0, 0), pad),
            Ok(LLIRType::I16) => self.push_const(Const::I16(0, 0), pad),
            Ok(LLIRType::I32) => self.push_const(Const::I32(0, 0), pad),
            Ok(LLIRType::I64) => self.push_const(Const::I64(0, 0), pad),
            Ok(LLIRType::Float) => self.push_const(Const::Float(None), pad),
            Ok(LLIRType::Double) => self.push_const(Const::Double(None), pad),
            Ok(LLIRType::Ptr(_)) => self.push_const(Const::Addr(None), pad),
            Ok(LLIRType::Vector(false, n, ty)) | Ok(LLIRType::Array(n, ty)) => {
                for _ in 0..*n {
                    self.push_undef(ty, pad, typedefs)?;
                }
            }
            Ok(LLIRType::Struct(packed, tys)) => {
                let mut ipad = pad;
                for ty in tys {
                    self.push_undef(ty, ipad, typedefs)?;
                    ipad = !*packed;
                }
            }
            Ok(LLIRType::Ext(ExtIdent { name, .. }, ty)) => match name {
                ExtName::CastTarget(_) | ExtName::RestrictBase(_) => {
                    return Err(Error::Unsupported(format!(
                        "cannot allocate unsupported type {}",
                        ty
                    )))
                }
                _ => return self.push_undef(ty, pad, typedefs),
            },
            Ok(_) => return Err(Error::Unsupported(format!("cannot allocate type {}", ty))),
            Err(_) => return Err(Error::TypeNotFound(ty.clone())),
        }
        Ok(())
    }
    /// Returns the number of bytes as writing the `in` value `x` at the offset of the view.
    pub fn write_int(&mut self, x: i64, n: i64) -> Result<i64, Error> {
        assert!((1..=64).contains(&n), "unsupported write i{} value", n);
        let (idx, delta) = self.index_delta()?;
        let shift = delta * 8;
        let mask = match n >= 64 {
            true => !0i64,
            false => ((1 << n) - 1) << shift,
        };
        let x = (x << shift) & mask;
        // TODO: FIXME: consider the case overwriting partially undefined values.
        match self.val.get_mut(idx) {
            Some(Const::I1(b, mb)) if shift + n <= 1 => {
                *b = x != 0;
                *mb = true;
            }
            Some(Const::I8(y, my)) if shift + n <= 8 => {
                *y = (*y & !mask as i8) | x as i8;
                *my |= mask as u8;
            }
            Some(Const::I16(y, my)) if shift + n <= 16 => {
                *y = (*y & !mask as i16) | x as i16;
                *my |= mask as u16;
            }
            Some(Const::I32(y, my)) if shift + n <= 32 => {
                *y = (*y & !mask as i32) | x as i32;
                *my |= mask as u32;
            }
            Some(Const::I64(y, my)) if shift + n <= 64 => {
                *y = (*y & !mask as i64) | x;
                *my |= mask as u64;
            }
            _ => return Err(Error::WriteInt(self.clone(), n)),
        }
        Ok(n / 8)
    }
    /// Returns the number of bytes as writing the `float` value `x` at the offset of the view.
    pub fn write_float(&mut self, x: f32) -> Result<i64, Error> {
        let (idx, delta) = self.index_delta()?;
        if delta == 0 {
            if let Some(Const::Float(y)) = self.val.get_mut(idx) {
                *y = Some(x);
                return Ok(4);
            }
        }
        Err(Error::WriteConst(self.clone(), Const::Float(Some(x))))
    }
    /// Returns the number of bytes as writing the `double` value `x` at the offset of the view.
    pub fn write_double(&mut self, x: f64) -> Result<i64, Error> {
        let (idx, delta) = self.index_delta()?;
        if delta == 0 {
            if let Some(Const::Double(y)) = self.val.get_mut(idx) {
                *y = Some(x);
                return Ok(8);
            }
        }
        Err(Error::WriteConst(self.clone(), Const::Double(Some(x))))
    }
    /// Returns the number of bytes as writing the address `addr` at the offset of the view.
    pub fn write_addr(&mut self, addr: Addr) -> Result<i64, Error> {
        let (idx, delta) = self.index_delta()?;
        if delta == 0 {
            if let Some(Const::Addr(y)) = self.val.get_mut(idx) {
                *y = Some(addr);
                return Ok(8);
            }
        }
        Err(Error::WriteConst(self.clone(), Const::Addr(Some(addr))))
    }
    /// Returns the number of bytes as writing the constant with size at the offset of the view.
    pub fn write_const(&mut self, c: &Const, size: i64) -> Result<i64, Error> {
        match c {
            Const::I1(b, true) => match b {
                true => self.write_int(1, cmp::min(8, size * 8)),
                false => self.write_int(0, cmp::min(8, size * 8)),
            },
            Const::I8(n, mn) if *mn == !0 => self.write_int(*n as u8 as i64, cmp::min(8, size * 8)),
            Const::I16(n, mn) if *mn == !0 => {
                self.write_int(*n as u16 as i64, cmp::min(16, size * 8))
            }
            Const::I32(n, mn) if *mn == !0 => {
                self.write_int(*n as u32 as i64, cmp::min(32, size * 8))
            }
            Const::I64(n, mn) if *mn == !0 => self.write_int(*n, cmp::min(64, size * 8)),
            Const::Float(Some(n)) if size == 4 => self.write_float(*n),
            Const::Double(Some(n)) if size == 8 => self.write_double(*n),
            Const::Addr(Some(addr)) if size == 8 => self.write_addr(addr.clone()),
            _ => Err(Error::WriteConst(self.clone(), c.clone())),
        }
    }
    /// Returns the number of bytes as writing the value with size at the offset of the view.
    pub fn write_val(&mut self, v: &Val, size: i64) -> Result<(), Error> {
        if v.size() < size {
            return Err(Error::OutOfBoundInVal(v.clone(), size));
        }
        let mut p = 0;
        for c in v.iter() {
            let n = self.write_const(c, size - p)?;
            self.offset += n;
            p += n;
        }
        Ok(())
    }
    /// Returns the value.
    pub fn into_val(mut self) -> Val {
        if self.pad {
            self.push_pad(self.val.align());
        }
        self.val
    }
}

impl fmt::Display for ValView {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}[{}..]", self.val, self.offset)
    }
}

#[derive(Clone, Debug)]
struct Frame {
    loc: Loc,
    res: Option<LocalIdent>,
    allocaidx: usize,
    locals: BTreeMap<LocalIdent, Val>,
}

/// An interpreter.
#[derive(Clone, Debug)]
pub struct Interp {
    datalayout: DataLayout,
    typedefs: Typedefs<ExtIdent>,
    funcs: BTreeMap<GlobalIdent, Func>,
    globals: BTreeMap<GlobalIdent, Val>,
    allocas: Vec<(bool, Val)>,
    heap: Vec<(bool, PoisonVal)>,
    stack: Vec<Frame>,
    locals: BTreeMap<LocalIdent, Val>,
    state: State,
}

impl Interp {
    /// Returns a new interpreter with the given data layout and typedef list.
    pub fn new(datalayout: DataLayout, typedefs: Typedefs<ExtIdent>) -> Interp {
        Interp {
            datalayout,
            typedefs,
            funcs: BTreeMap::new(),
            globals: BTreeMap::new(),
            allocas: Vec::new(),
            heap: Vec::new(),
            stack: Vec::new(),
            locals: BTreeMap::new(),
            state: State::NotStarted,
        }
    }
    /// Returns the data layout.
    pub fn datalayout(&self) -> &DataLayout {
        &self.datalayout
    }
    /// Returns the typedef list.
    pub fn typedefs(&self) -> &Typedefs<ExtIdent> {
        &self.typedefs
    }
    /// Returns the function by name.
    pub fn func(&self, name: &GlobalIdent) -> Result<&Func, Error> {
        match self.funcs.get(name) {
            Some(func) => Ok(func),
            None => Err(Error::FuncNotFound(*name)),
        }
    }
    /// Defines the function.
    pub fn define_func(&mut self, name: GlobalIdent, func: Func) -> Result<(), Error> {
        if self.globals.contains_key(&name) || self.funcs.contains_key(&name) {
            return Err(Error::RedefineGlobal(name));
        }
        self.funcs.insert(name, func);
        Ok(())
    }
    /// Returns the value of the global variable.
    pub fn global(&self, name: &GlobalIdent) -> Result<Val, Error> {
        if let Some(obj) = self.globals.get(name) {
            return Ok(obj.clone());
        }
        if self.funcs.contains_key(name) {
            let addr = Addr {
                region: Region::GlobalFunc(*name),
                offset: 0,
            };
            return Ok(Val::from(Const::Addr(Some(addr))));
        }
        Err(Error::GlobalNotFound(*name))
    }
    /// Defines the global variable with the value.
    pub fn define_global(&mut self, name: GlobalIdent, obj: Val) -> Result<(), Error> {
        if self.globals.contains_key(&name) || self.funcs.contains_key(&name) {
            return Err(Error::RedefineGlobal(name));
        }
        self.globals.insert(name, obj);
        Ok(())
    }
    /// Returns a new `alloca` region with the value.
    pub fn alloca(&mut self, val: Val) -> Region {
        let id = self.allocas.len();
        self.allocas.push((true, val));
        Region::Alloca(id)
    }
    /// Returns the value view by alloca-ed index and offset.
    pub fn deref_alloca(&self, id: usize, offset: i64) -> Result<ValView, Error> {
        match self.allocas.get(id) {
            Some((true, val)) => Ok(val.clone().into_view(offset)),
            Some((false, _)) => Err(Error::UseAfterFree(Addr {
                region: Region::Alloca(id),
                offset,
            })),
            None => Err(Error::AddrNotFound(Addr {
                region: Region::Alloca(id),
                offset,
            })),
        }
    }
    /// Stores the value view to the `alloca`-ed region with the given index.
    pub fn store_to_alloca(&mut self, v: Val, id: usize) -> Result<(), Error> {
        match self.allocas.get_mut(id) {
            Some((true, t)) => {
                *t = v;
                Ok(())
            }
            Some((false, _)) => Err(Error::UseAfterFree(Addr {
                region: Region::Alloca(id),
                offset: 0,
            })),
            None => Err(Error::AddrNotFound(Addr {
                region: Region::Alloca(id),
                offset: 0,
            })),
        }
    }
    /// Returns a new `malloc` region.
    pub fn malloc(&mut self, size: i64) -> Result<Region, Error> {
        if size < 0 {
            return Err(Error::MallocSize(size));
        }
        let id = self.heap.len();
        self.heap.push((true, PoisonVal::Poison(size)));
        Ok(Region::Heap(id))
    }
    /// Returns the value view by malloc-ed index and offset.
    pub fn deref_heap(&self, id: usize, offset: i64) -> Result<ValView, Error> {
        match self.heap.get(id) {
            Some((true, PoisonVal::Val(val))) => Ok(val.clone().into_view(offset)),
            Some((true, PoisonVal::Poison(size))) => Err(Error::DerefPoison(
                Addr {
                    region: Region::Heap(id),
                    offset,
                },
                *size,
            )),
            Some((false, _)) => Err(Error::UseAfterFree(Addr {
                region: Region::Heap(id),
                offset,
            })),
            None => Err(Error::AddrNotFound(Addr {
                region: Region::Heap(id),
                offset,
            })),
        }
    }
    /// Stores the value view to the `malloc`-ed region with the given index.
    pub fn store_to_heap(&mut self, v: Val, id: usize) -> Result<(), Error> {
        match self.heap.get_mut(id) {
            Some((true, PoisonVal::Val(t))) => {
                *t = v;
                Ok(())
            }
            Some((true, PoisonVal::Poison(size))) => Err(Error::DerefPoison(
                Addr {
                    region: Region::Heap(id),
                    offset: 0,
                },
                *size,
            )),
            Some((false, _)) => Err(Error::UseAfterFree(Addr {
                region: Region::Heap(id),
                offset: 0,
            })),
            None => Err(Error::AddrNotFound(Addr {
                region: Region::Heap(id),
                offset: 0,
            })),
        }
    }
    /// Returns the value view by dereferences the given address.
    pub fn deref_addr(&self, addr: &Addr) -> Result<ValView, Error> {
        match addr {
            Addr {
                region: Region::Alloca(id),
                offset,
            } => self.deref_alloca(*id, *offset),
            Addr {
                region: Region::Heap(id),
                offset,
            } => self.deref_heap(*id, *offset),
            _ => Err(Error::Deref(addr.clone())),
        }
    }
    /// Collapses the poison region at the given address with the given type.
    pub fn bitcast_poison(&mut self, addr: &Addr, ty: &LLIRType<ExtIdent>) -> Result<(), Error> {
        if let Addr {
            region: Region::Heap(id),
            offset: 0,
        } = addr
        {
            if let Some((true, PoisonVal::Poison(size))) = self.heap.get(*id) {
                if self.datalayout().sizeof_type(ty, self.typedefs()) == Some(*size) {
                    let v = Val::undef(ty, self.typedefs())?;
                    self.heap.insert(*id, (true, PoisonVal::Val(v)));
                    return Ok(());
                }
            }
        }
        Err(Error::BitcastPoison(addr.clone(), ty.clone()))
    }
    /// Stores the value to the region.
    pub fn store_to(&mut self, val: Val, region: &Region) -> Result<(), Error> {
        match region {
            Region::Alloca(id) => self.store_to_alloca(val, *id),
            Region::Heap(id) => self.store_to_heap(val, *id),
            _ => Err(Error::Deref(Addr {
                region: region.clone(),
                offset: 0,
            })),
        }
    }
    /// Returns the value of the local variable.
    pub fn local(&self, name: &LocalIdent) -> Result<&Val, Error> {
        match self.locals.get(name) {
            Some(obj) => Ok(obj),
            None => Err(Error::LocalNotFound(*name)),
        }
    }
    /// Sets the value to the local variable.
    pub fn set_local(&mut self, name: LocalIdent, obj: Val) -> Result<(), Error> {
        self.locals.insert(name, obj);
        Ok(())
    }
    /// Pushes the result of binary operation.
    pub fn push_binop_value(
        &self,
        view: &mut ValView,
        opcode: BinOpcode,
        view1: &ValView,
        view2: &ValView,
        pad: bool,
    ) -> Result<(), Error> {
        if let BinOpcode::Add(Some(WrapMode::Nsw)) = opcode {
            if let Ok(x1) = view1.try_read_i32() {
                if let Ok(x2) = view2.try_read_i32() {
                    let y = match x1.checked_add(x2) {
                        Some(y) => y,
                        None => return Err(Error::OverflowSignedIntAdd(32, x1 as i64, x2 as i64)),
                    };
                    view.push_const(Const::I32(y, !0), pad);
                    return Ok(());
                }
            }
        }
        if let BinOpcode::Fsub = opcode {
            if let Ok(x1) = view1.try_read_float() {
                if let Ok(x2) = view2.try_read_float() {
                    view.push_const(Const::Float(Some(x1 - x2)), pad);
                    return Ok(());
                }
            }
            if let Ok(x1) = view1.try_read_double() {
                if let Ok(x2) = view2.try_read_double() {
                    view.push_const(Const::Double(Some(x1 - x2)), pad);
                    return Ok(());
                }
            }
        }
        Err(Error::Unsupported(format!(
            "cannot eval {} {}, {}",
            opcode, view1, view2
        )))
    }
    /// Pushes the result of comparison operation.
    pub fn push_cmpop_value(
        &self,
        view: &mut ValView,
        opcode: CmpOpcode,
        view1: &ValView,
        view2: &ValView,
        pad: bool,
    ) -> Result<(), Error> {
        if let CmpOpcode::Icmp(cond) = opcode {
            if let Ok(x1) = view1.try_read_i32() {
                if let Ok(x2) = view2.try_read_i32() {
                    let res = match cond {
                        IcmpCond::Eq => x1 == x2,
                        IcmpCond::Ne => x1 != x2,
                        _ => unimplemented!("{}", cond),
                    };
                    view.push_const(Const::I1(res, true), pad);
                    return Ok(());
                }
            }
        }
        Err(Error::Unsupported(format!(
            "cannot eval {} {}, {}",
            opcode, view1, view2
        )))
    }
    /// Pushes the value.
    pub fn push_value(
        &self,
        view: &mut ValView,
        ty: Option<&LLIRType<ExtIdent>>,
        val: &Value<ExtIdent>,
        pad: bool,
    ) -> Result<(), Error> {
        match val {
            Value::Null => match ty {
                Some(LLIRType::Ptr(_)) | None => view.push_const(
                    Const::Addr(Some(Addr {
                        region: Region::Null,
                        offset: 0,
                    })),
                    pad,
                ),
                Some(ty) => {
                    return Err(Error::MalformedValue(format!(
                        "illegal null of type {}",
                        ty
                    )))
                }
            },
            Value::False => view.push_const(Const::I1(false, true), pad),
            Value::True => view.push_const(Const::I1(true, true), pad),
            Value::I8(n) => view.push_const(Const::I8(*n, !0), pad),
            Value::I16(n) => view.push_const(Const::I16(*n, !0), pad),
            Value::I32(n) => view.push_const(Const::I32(*n, !0), pad),
            Value::I64(n) => view.push_const(Const::I64(*n, !0), pad),
            Value::Float(s) => match s.parse::<f32>() {
                Ok(n) => view.push_const(Const::Float(Some(n)), pad),
                Err(err) => return Err(Error::MalformedValue(format!("{} in {}", err, val))),
            },
            Value::Double(s) => match s.parse::<f64>() {
                Ok(n) => view.push_const(Const::Double(Some(n)), pad),
                Err(err) => return Err(Error::MalformedValue(format!("{} in {}", err, val))),
            },
            Value::Vector(tyvals) | Value::Array(tyvals) => {
                for TypedValue(ty, val) in tyvals {
                    self.push_value(view, Some(ty), val, pad)?;
                }
            }
            Value::Struct(packed, tyvals) => {
                let mut ipad = false;
                for TypedValue(ty, val) in tyvals {
                    self.push_value(view, Some(ty), val, ipad)?;
                    ipad = !*packed;
                }
            }
            Value::LocalRef(name) => view.push_val(self.local(name)?.clone(), pad),
            Value::GlobalRef(name) => view.push_val(self.global(name)?, pad),
            Value::BinOp(args) => {
                let BinOpArgs {
                    opcode,
                    left: TypedValue(leftty, leftval),
                    right: TypedValue(rightty, rightval),
                } = args.as_ref();
                let leftview = self.eval_value(Some(leftty), leftval)?.into_view(0);
                let rightview = self.eval_value(Some(rightty), rightval)?.into_view(0);
                self.push_binop_value(view, *opcode, &leftview, &rightview, pad)?;
            }
            Value::CmpOp(args) => {
                let CmpOpArgs {
                    opcode,
                    left: TypedValue(leftty, leftval),
                    right: TypedValue(rightty, rightval),
                } = args.as_ref();
                let leftview = self.eval_value(Some(leftty), leftval)?.into_view(0);
                let rightview = self.eval_value(Some(rightty), rightval)?.into_view(0);
                self.push_cmpop_value(view, *opcode, &leftview, &rightview, pad)?;
            }
            Value::ConvOp(args) => {
                let ConvOpArgs {
                    opcode,
                    srctyval: TypedValue(srcty, srcval),
                    dstty,
                } = args.as_ref();
                let srcv = self.eval_value(Some(srcty), srcval)?;
                match opcode {
                    // Cannot process poisons at this bitcast (see eval_insn).
                    ConvOpcode::Bitcast => view.push_val(srcv, pad),
                    _ => {
                        return Err(Error::Unsupported(format!(
                            "cannot eval {} {} to {}",
                            opcode, srcv, dstty
                        )));
                    }
                }
            }
            Value::Getelementptr(args) => {
                let GetelementptrResult {
                    index: mut i,
                    offset: o,
                    ..
                } = match self.datalayout().getelementptr(args, self.typedefs()) {
                    Ok(res) => res,
                    Err(err) => return Err(Error::Getelementptr(err)),
                };
                i.add(&o);
                let mut offset = i.base();
                for (scale, TypedValue(ty, val)) in i.terms() {
                    let view = self.eval_value(None, val)?.into_view(0);
                    offset += scale * view.try_read(ty)?.try_to_i64()?;
                }
                let v = self.eval_value(Some(&args.base_ptr.0), &args.base_ptr.1)?;
                let addr = v
                    .into_view(0)
                    .try_read_addr_of(&args.base_ty)?
                    .rebase(offset);
                view.push_const(Const::Addr(Some(addr)), pad);
            }
            _ => return Err(Error::Unsupported(format!("cannot eval value {}", val))),
        }
        Ok(())
    }
    /// Returns an evaluated value.
    pub fn eval_value(
        &self,
        ty: Option<&LLIRType<ExtIdent>>,
        val: &Value<ExtIdent>,
    ) -> Result<Val, Error> {
        let mut view = ValView::empty();
        self.push_value(&mut view, ty, val, false)?;
        Ok(view.into_val())
    }
    /// Evaluates the instruction and returns the caused effect.
    pub fn eval_insn(&self, insn: &Insn<ExtIdent>) -> Result<Effect, Error> {
        match insn {
            Insn::Alloca { res, ty, .. } => {
                Ok(Effect::Alloca(*res, Val::undef(ty, self.typedefs())?))
            }
            Insn::Br(label) => Ok(Effect::Cont(Cont::Goto(*label))),
            Insn::BrI1(val, label1, label0) => {
                match self.eval_value(None, val)?.into_view(0).try_read_i1()? {
                    true => Ok(Effect::Cont(Cont::Goto(*label1))),
                    false => Ok(Effect::Cont(Cont::Goto(*label0))),
                }
            }
            Insn::Call {
                res,
                body:
                    CallBody {
                        ret,
                        callee: Callee::Value(calleeval),
                        args,
                        ..
                    },
                ..
            } => {
                match calleeval {
                    Value::GlobalRef(global_ident!("_Znwm"))
                    | Value::GlobalRef(global_ident!("malloc"))
                        if args.len() == 1 =>
                    {
                        if let LLIRType::Ptr(_) = &ret.ty {
                            if let Some(res) = res {
                                let argview = self.eval_value(None, &args[0].1)?.into_view(0);
                                let size = argview.try_read(&(args[0].0).ty)?.try_to_i64()?;
                                return Ok(Effect::Malloc(*res, size));
                            }
                        }
                    }
                    Value::GlobalRef(name) if name.is_dbg_intr() => {
                        return Ok(Effect::DbgIntr(*name))
                    }
                    _ => {}
                }
                let calleeview = self.eval_value(None, calleeval)?.into_view(0);
                let name = match calleeview.try_read_addr_of(&LLIRType::Void) {
                    Ok(Addr {
                        region: Region::GlobalFunc(name),
                        offset: 0,
                    }) => *name,
                    _ => return Err(Error::Callee(calleeview.into_val())),
                };
                let mut vs = Vec::with_capacity(args.len());
                for ParamValue(_, val) in args {
                    vs.push(self.eval_value(None, val)?);
                }
                Ok(Effect::Cont(Cont::Call(*res, name, vs)))
            }
            Insn::Load {
                res,
                ty,
                src: TypedValue(_, srcval),
                ..
            } => {
                let srcview = self.eval_value(None, srcval)?.into_view(0);
                let srcaddr = match srcview.try_read_addr_of(ty) {
                    Ok(addr) => addr,
                    _ => return Err(Error::LoadFrom(srcview.into_val())),
                };
                let view = self.deref_addr(srcaddr)?;
                let v = view.try_read(ty)?;
                Ok(Effect::SetLocal(*res, v))
            }
            Insn::Ret(None) => Ok(Effect::Cont(Cont::Ret(None))),
            Insn::Ret(Some(TypedValue(_, val))) => {
                Ok(Effect::Cont(Cont::Ret(Some(self.eval_value(None, val)?))))
            }
            Insn::Store {
                src: TypedValue(_, srcval),
                dst: TypedValue(dstty, dstval),
                ..
            } => {
                let (size, ty) = match dstty {
                    LLIRType::Ptr(ty) => match Val::undef(ty, self.typedefs()) {
                        Ok(v) => (v.size(), ty),
                        Err(_) => return Err(Error::StoreTarget(dstty.clone())),
                    },
                    _ => return Err(Error::StoreTarget(dstty.clone())),
                };
                let dstview = self.eval_value(None, dstval)?.into_view(0);
                let dstaddr = match dstview.try_read_addr_of(ty) {
                    Ok(addr) => addr,
                    Err(_) => return Err(Error::StoreTo(dstview.into_val())),
                };
                let mut view = self.deref_addr(dstaddr)?;
                view.write_val(&self.eval_value(None, srcval)?, size)?;
                Ok(Effect::StoreTo(view.into_val(), dstaddr.region.clone()))
            }
            Insn::Value(name, val) => {
                if let Value::ConvOp(args) = val {
                    let ConvOpArgs {
                        opcode,
                        srctyval: TypedValue(srcty, srcval),
                        dstty,
                    } = args.as_ref();
                    if let ConvOpcode::Bitcast = opcode {
                        let srcv = self.eval_value(Some(srcty), srcval)?;
                        // Process at most one poison in one insn with an effect ...
                        if let LLIRType::Ptr(ty) = dstty {
                            if let Ok(addr) = srcv.into_view(0).try_read_addr_of(ty) {
                                let ty = ty.as_ref().clone();
                                return Ok(Effect::CollapsePoison(*name, addr.clone(), ty));
                            }
                        }
                    }
                }
                Ok(Effect::SetLocal(*name, self.eval_value(None, val)?))
            }
            _ => Err(Error::Unsupported(format!("cannot eval insn {}", insn))),
        }
    }
    /// Returns the stack trace.
    pub fn stacktrace(&self) -> Result<Vec<Loc>, Error> {
        let mut trace = Vec::with_capacity(1 + self.stack.len());
        trace.push(self.state().loc()?);
        for ctx in self.stack.iter().rev() {
            trace.push(ctx.loc);
        }
        Ok(trace)
    }
    /// Returns the state.
    pub fn state(&self) -> &State {
        &self.state
    }
    /// Returns the next instruction.
    pub fn insn(&self) -> Result<&Insn<ExtIdent>, Error> {
        let loc = self.state().loc()?;
        let func = self.func(&loc.func)?;
        func.insn(&loc.block, loc.insnidx)
    }
    /// Enters into a new call stack frame by the function call.
    pub fn enter(
        &mut self,
        res: Option<LocalIdent>,
        funcname: GlobalIdent,
        args: Vec<Val>,
    ) -> Result<(), Error> {
        let func = self.func(&funcname)?;
        let blockname = func.entryname()?;
        if func.args().len() != args.len() {
            return Err(Error::ArgsUnmatched(
                func.name(),
                func.args().len(),
                args.len(),
            ));
        }
        let mut locals = BTreeMap::new();
        for (i, v) in args.into_iter().enumerate() {
            locals.insert(func.args()[i], v);
        }
        self.stack.push(Frame {
            loc: self.state().loc()?,
            allocaidx: self.allocas.len(),
            res,
            locals: mem::replace(&mut self.locals, locals),
        });
        self.state = State::At(Loc::new(funcname, blockname, 0));
        Ok(())
    }
    /// Leaves from the current call frame.
    pub fn leave(&mut self, ret: Option<Val>) -> Result<(), Error> {
        let frame = match self.stack.pop() {
            Some(frame) => frame,
            None => {
                self.state = State::Finished(ret);
                return Ok(());
            }
        };
        for i in (frame.allocaidx)..self.allocas.len() {
            self.allocas.get_mut(i).unwrap().0 = false;
        }
        let _ = mem::replace(&mut self.locals, frame.locals);
        match frame.res {
            Some(name) => match ret {
                Some(v) => self.set_local(name, v)?,
                None => return Err(Error::RetValExpected(name)),
            },
            None => {
                if let Some(v) = ret {
                    return Err(Error::RetValUnexpected(v));
                }
            }
        }
        self.state = State::At(frame.loc);
        Ok(())
    }
    /// Starts the execution by calling the function without any arguments.
    pub fn start(&mut self, funcname: GlobalIdent) -> Result<(), Error> {
        match self.state() {
            State::NotStarted => {}
            State::At(loc) => return Err(Error::AlreadyStarted(*loc)),
            State::Finished(res) => return Err(Error::Finished(res.clone())),
        }
        let blockname = self.func(&funcname)?.entryname()?;
        self.state = State::At(Loc::new(funcname, blockname, 0));
        Ok(())
    }
    /// Steps the interpreter.
    pub fn step(&mut self) -> Result<Effect, Error> {
        let effect = self.eval_insn(self.insn()?)?;
        self.state.step()?;
        match &effect {
            Effect::Alloca(name, val) => {
                let region = self.alloca(val.clone());
                self.set_local(
                    *name,
                    Val::from(Const::Addr(Some(Addr { region, offset: 0 }))),
                )?;
            }
            Effect::CollapsePoison(name, Addr { region, offset }, ty) => {
                let addr = Addr {
                    region: region.clone(),
                    offset: *offset,
                };
                if let Region::Heap(idx) = region {
                    if *offset == 0 {
                        match self.heap.get(*idx) {
                            Some((true, PoisonVal::Poison(n))) => {
                                if self.datalayout().sizeof_type(ty, self.typedefs()) != Some(*n) {
                                    return Err(Error::PoisonSizeUnmatched(ty.clone(), *n, addr));
                                }
                                let v = Val::undef(ty, self.typedefs())?;
                                self.heap.insert(*idx, (true, PoisonVal::Val(v)));
                            }
                            Some((true, PoisonVal::Val(_))) => {
                                return Err(Error::CollapsePoison(ty.clone(), addr));
                            }
                            Some((false, _)) => return Err(Error::UseAfterFree(addr)),
                            None => return Err(Error::AddrNotFound(addr)),
                        }
                    }
                }
                self.set_local(*name, Val::from(Const::Addr(Some(addr))))?;
            }
            Effect::Cont(Cont::Call(res, funcname, args)) => {
                self.enter(*res, *funcname, args.clone())?
            }
            Effect::Cont(Cont::Goto(label)) => self.state.goto(*label)?,
            Effect::Cont(Cont::Ret(ret)) => self.leave(ret.clone())?,
            Effect::DbgIntr(_) => {}
            Effect::Malloc(name, size) => {
                let region = self.malloc(*size)?;
                self.set_local(
                    *name,
                    Val::from(Const::Addr(Some(Addr { region, offset: 0 }))),
                )?;
            }
            Effect::SetLocal(name, v) => self.set_local(*name, v.clone())?,
            Effect::StoreTo(val, region) => self.store_to(val.clone(), region)?,
        }
        Ok(effect)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fmt::DisplayIter;
    use crate::llir::parser::Parser as LLIRParser;
    use crate::llir::syntax::Blocks;
    fn new_interp() -> Interp {
        let datalayout = DataLayout::lp64();
        let typedefs = Typedefs::new(btree_map![
            LocalIdent::from("tuple2i") => LLIRParser::new_type("{i32, i32}")
        ]);
        let mut interp = Interp::new(datalayout, typedefs);
        let globals = btree_map![
            "true" => Val::from(Const::I1(true, true))
        ];
        for (name, val) in globals {
            interp
                .define_global(GlobalIdent::from(name), val)
                .expect(name);
        }
        let funcs = btree_map![
            "main" => Func::parse(r#"define i32 @main() {
                ret i32 0
            }"#),
            "ret_alloca" => Func::parse(r#"define i32* @ret_alloca(i32) {
                %2 = alloca i32
                store i32 %0, i32* %2
                ret i32* %2
            }"#),
            "deref_inner_alloca" => Func::parse(r#"define i32 @deref_inner_alloca() {
                %1 = call i32* @ret_alloca(i32 1)
                %2 = load i32, i32* %1
                ret i32 %2
            }"#),
            "store_float" => Func::parse(r#"define void @store_float(float*, i1) {
                br i1 %1, label %3, label %4
            3:
                store float 1.0, float* %0
                br label %5
            4:
                store float 2.0, float* %0
                br label %5
            5:
                ret void
            }"#),
            "sub_stored_floats" => Func::parse(r#"define float @sub_stored_floats() {
                %1 = alloca float
                %2 = alloca float
                call void @store_float(float* %1, i1 true)
                call void @store_float(float* %2, i1 false)
                %3 = load float, float* %1
                %4 = load float, float* %2
                ret i32 fsub float %3, %4
            }"#),
            "malloc_tuple2i" => Func::parse(r#"define %tuple2i* @malloc_tuple2i() {
                %1 = call i8* @malloc(i64 8)
                %2 = bitcast i8* %1 to %tuple2i*
                ret %tuple2i* %2
            }"#),
            "malloc_overflow" => Func::parse(r#"define i64* @malloc_overflow() {
                %1 = call i8* @malloc(i64 2)
                %2 = bitcast i8* %1 to i64*
                ret i64* %2
            }"#),
            "malloc_underflow" => Func::parse(r#"define i64* @malloc_underflow() {
                %1 = call i8* @malloc(i64 16)
                %2 = bitcast i8* %1 to i64*
                ret i64* %2
            }"#),
            "f0" => Func::new(
                GlobalIdent::from("f0"),
                vec![],
                Blocks::empty(),
            ),
            "f1" => Func::new(
                GlobalIdent::from("f0"),
                vec![LocalIdent::from("0")],
                Blocks::empty(),
            ),
            "g2" => Func::new(
                GlobalIdent::from("g2"),
                vec![LocalIdent::from("0"), LocalIdent::from("1")],
                Blocks::empty(),
            )
        ];
        for (name, func) in funcs {
            interp
                .define_func(GlobalIdent::from(name), func)
                .expect(name);
        }
        interp
    }
    fn enter_dummy(interp: &mut Interp) {
        let mut locals = btree_map![
            "true" => Val::from(Const::I1(true, true)),
            "one" => Val::from(Const::I32(1, !0)),
            "pi" => Val::from(Const::Float(Some(3.14)))
        ];
        let allocas = vec![
            ("alloca-i32", Val::from(Const::I32(255, !0))),
            (
                "alloca-tuple2i",
                Val::new(vec![Const::I32(1, !0), Const::I32(2, !0)]),
            ),
            (
                "alloca-tuple2f",
                Val::new(vec![Const::Float(Some(1.0)), Const::Float(Some(2.0))]),
            ),
            (
                "alloca-tuple2d",
                Val::new(vec![Const::Double(Some(1.0)), Const::Double(Some(2.0))]),
            ),
            (
                "alloca-tuple2a",
                Val::new(vec![
                    Const::Addr(Some(Addr {
                        region: Region::Null,
                        offset: 1,
                    })),
                    Const::Addr(Some(Addr {
                        region: Region::Null,
                        offset: 2,
                    })),
                ]),
            ),
            ("alloca-i32p", Val::from(Const::I32(0x1200, 0xff00))),
        ];
        for (name, val) in allocas {
            let addr = Addr {
                region: interp.alloca(val),
                offset: 0,
            };
            locals.insert(name, Val::from(Const::Addr(Some(addr))));
        }
        let heap = vec![("malloc-i32", LLIRType::I32)];
        for (name, ty) in heap {
            let size = interp
                .datalayout()
                .sizeof_type(&ty, interp.typedefs())
                .expect(name);
            let addr = Addr {
                region: interp.malloc(size).expect(name),
                offset: 0,
            };
            interp.bitcast_poison(&addr, &ty).expect(name);
            locals.insert(name, Val::from(Const::Addr(Some(addr))));
        }
        locals.insert(
            "malloc-poison32",
            Val::from(Const::Addr(Some(Addr {
                region: interp.malloc(32).unwrap(),
                offset: 0,
            }))),
        );
        for (name, val) in locals {
            interp.set_local(LocalIdent::from(name), val).expect(name);
        }
    }
    #[test]
    fn eval_value() {
        for (expected, input) in vec![
            // basic constants
            ("Ok(<i1 false>)", "i1 false"),
            ("Ok(<i1 true>)", "i1 true"),
            // vector constants (also tests typed basic constants)
            ("Ok(<i8 1, i8 2, i8 3>)", "<3 x i8> <i8 1, i8 2, i8 3>"),
            // array constants (also tests typed basic constants)
            (
                "Ok(<i16 1, i16 2, i16 3>)",
                "[3 x i8] [i16 1, i16 2, i16 3]",
            ),
            // struct constants (also tests typed basic constants)
            (
                "Ok(<i64 1, i8 2, !pad 1, i16 3, !pad 4>)",
                "{i64, i8, i16} {i64 1, i8 2, i16 3}",
            ),
            (
                "Ok(<i64 1, i16 2, i8 3, !pad 5>)",
                "{i64, {i16, i8}} {i64 1, {i16, i8} {i16 2, i8 3}}",
            ),
            (
                "Ok(<float 1, double 2>)",
                "<{float, double}> <{float 1.0, double 2.0}>",
            ),
            // null pointer constants
            ("Ok(<null+0>)", "void* null"),
            // binops
            ("Ok(<i32 3>)", "i32 add nsw (i32 1, i32 2)"),
            (
                "Err(overflow add i32 2147483647, 1)",
                "i32 add nsw (i32 2147483647, i32 1)",
            ),
            ("Ok(<float -1>)", "float fsub (float 1, float 2)"),
            ("Ok(<double -1>)", "double fsub (double 1, double 2)"),
            (
                "Err(cannot eval fsub <float 1>[0..], <double 2>[0..])",
                "void fsub (float 1, double 2)",
            ),
            // cmpops
            ("Ok(<i1 true>)", "i1 icmp eq i32 1, 1"),
            ("Ok(<i1 false>)", "i1 icmp ne i32 1, 1"),
            (
                "Err(cannot eval icmp eq <i1 true>[0..], <i32 1>[0..])",
                "i1 icmp eq i32 %true, 1",
            ),
            // convops: bitcast
            ("Ok(<null+0>)", "i32* bitcast i64* null to i32*"),
            (
                "Ok(<heap#2+0>)",
                "i32* bitcast i8* %malloc-poison32 to [8 x i32]*",
            ),
            // getelementptrs: won't check any alignments or bounds
            (
                "Ok(<alloca#1+4>)",
                "i32* getelementptr %tuple2i, %tuple2i* %alloca-tuple2i, i32 0, i32 1",
            ),
            (
                "Ok(<alloca#1+8>)",
                "i32* getelementptr %tuple2i, %tuple2i* %alloca-tuple2i, i32 %one, i32 0",
            ),
            (
                "Ok(<alloca#1-8>)",
                "{i32, i32}* getelementptr %tuple2i, %tuple2i* %alloca-tuple2i, i32 -1",
            ),
            // local variables
            ("Ok(<i1 true>)", "i1 %true"),
            ("Err(%undef is not found)", "void %undef"),
            // global variables
            ("Ok(<i1 true>)", "i1 @true"),
            ("Ok(<@f0+0>)", "void* @f0"),
            ("Err(@undef is not found)", "void @undef"),
        ] {
            let TypedValue(ty, val) = LLIRParser::new_typed_value(input);
            let mut interp = new_interp();
            enter_dummy(&mut interp);
            let got = match interp.eval_value(Some(&ty), &val) {
                Ok(val) => format!("Ok({})", val),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn eval_insn() {
        for (expected, input) in vec![
            // alloca
            ("Ok(alloca(%1, <i32 undef@0xffffffff(0)>))", "%1 = alloca i32"),
            (
                "Ok(alloca(%1, <i32 undef@0xffffffff(0), i32 undef@0xffffffff(0)>))",
                "%1 = alloca <2 x i32>",
            ),
            (
                "Ok(alloca(%1, <i32 undef@0xffffffff(0), i32 undef@0xffffffff(0)>))",
                "%1 = alloca [2 x i32]",
            ),
            (
                "Ok(alloca(%1, <i64 undef@0xffffffffffffffff(0), i8 undef@0xff(0), !pad 1, i16 undef@0xffff(0), !pad 4>))",
                "%1 = alloca {i64, i8, i16}",
            ),
            (
                "Ok(alloca(%1, <i64 undef@0xffffffffffffffff(0), i16 undef@0xffff(0), i8 undef@0xff(0), !pad 5>))",
                "%1 = alloca {i64, {i16, i8}}",
            ),
            ("Ok(alloca(%1, <void* undef>))", "%1 = alloca i32*"),
            // br
            ("Ok(goto(label %1))", "br label %1"),
            ("Ok(goto(label %1))", "br i1 true, label %1, label %2"),
            ("Ok(goto(label %2))", "br i1 false, label %1, label %2"),
            ("Ok(goto(label %1))", "br i1 %one, label %1, label %2"),
            (
                "Err(cannot read i1 value at <float 3.14>[0..])",
                "br i1 %pi, label %1, label %2",
            ),
            // call
            ("Ok(call(none, @f0, []))", "call void @f0()"),
            ("Ok(call(none, @f1, [<i32 1>]))", "call void @f1(i32 1)"),
            (
                "Ok(call(%1, @g2, [<i32 1>, <float 2>]))",
                "%1 = call i32 @g2(i32 1, float 2.0)",
            ),
            ("Err(cannot call <i1 true>)", "call void %true()"),
            // call: memory allocations
            ("Ok(malloc(%1, 64))", "%1 = call i8* @_Znwm(i64 64)"),
            ("Ok(malloc(%1, 32))", "%1 = call i8* @malloc(i32 32)"),
            // load: basic types
            (
                "Ok(define-local(%1, <i32 255>))",
                "%1 = load i32, i32* %alloca-i32",
            ),
            (
                "Ok(define-local(%1, <i8 -1>))",
                "%1 = load i8, i8* %alloca-i32",
            ),
            (
                "Err(cannot read i64 value at <i32 255>[0..])",
                "%1 = load i64, i64* %alloca-i32",
            ),
            (
                "Err(cannot load value from <i1 true>)",
                "%1 = load i64, i64* %true",
            ),
            (
                "Err(cannot read i32 value at <i32 undef@0xffffffff(0)>[0..])",
                "%1 = load i32, i32* %malloc-i32",
            ),
            (
                "Err(cannot deref addr heap#2+0 containing poison with size 32)",
                "%1 = load i32, i32* %malloc-poison32",
            ),
            // load: getelementptr: ints
            (
                "Ok(define-local(%1, <i32 1>))",
                "%1 = load i32, i32* getelementptr ({i32, i32}, {i32, i32}* %alloca-tuple2i, i32 0, i32 0)",
            ),
            (
                "Ok(define-local(%1, <i32 2>))",
                "%1 = load i32, i32* getelementptr ({i32, i32}, {i32, i32}* %alloca-tuple2i, i32 0, i32 1)",
            ),
            (
                "Ok(define-local(%1, <i16 0>))",
                "%1 = load i16, i16* getelementptr (i16, i16* %alloca-tuple2i, i32 1)",
            ),
            (
                "Err(cannot read i16 value at <i32 1, i32 2>[3..])",
                "%1 = load i16, i16* getelementptr (i8, i8* %alloca-tuple2i, i32 3)",
            ),
            (
                "Ok(define-local(%1, <i8 18>))",
                "%1 = load i8, i8* getelementptr (i8, i8* %alloca-i32p, i32 1)",
            ),
            (
                "Err(cannot read i8 value at <i32 undef@0xffff00ff(4608)>[0..])",
                "%1 = load i8, i8* getelementptr (i8, i8* %alloca-i32p, i32 0)",
            ),
            (
                "Err(cannot read i16 value at <i32 undef@0xffff00ff(4608)>[0..])",
                "%1 = load i16, i16* getelementptr (i16, i16* %alloca-i32p, i32 0)",
            ),
            // load: getelementptr: floats
            (
                "Ok(define-local(%1, <float 1>))",
                "%1 = load float, float* getelementptr ({float, float}, {float, float}* %alloca-tuple2f, i32 0, i32 0)",
            ),
            (
                "Ok(define-local(%1, <float 2>))",
                "%1 = load float, float* getelementptr ({float, float}, {float, float}* %alloca-tuple2f, i32 0, i32 1)",
            ),
            (
                "Err(cannot convert <float 1, float 2>[1..] to value with type float)",
                "%1 = load float, float* getelementptr (i8, i8* %alloca-tuple2f, i32 1)",
            ),
            // load: getelementptr: doubles
            (
                "Ok(define-local(%1, <double 1>))",
                "%1 = load double, double* getelementptr ({double, double}, {double, double}* %alloca-tuple2d, i32 0, i32 0)",
            ),
            (
                "Ok(define-local(%1, <double 2>))",
                "%1 = load double, double* getelementptr ({double, double}, {double, double}* %alloca-tuple2d, i32 0, i32 1)",
            ),
            (
                "Err(cannot convert <double 1, double 2>[1..] to value with type double)",
                "%1 = load double, double* getelementptr (i8, i8* %alloca-tuple2d, i32 1)",
            ),
            // load: getelementptr: addrs
            (
                "Ok(define-local(%1, <null+1>))",
                "%1 = load void*, void** getelementptr ({void*, void*}, {void*, void*}* %alloca-tuple2a, i32 0, i32 0)",
            ),
            (
                "Ok(define-local(%1, <null+2>))",
                "%1 = load void*, void** getelementptr ({void*, void*}, {void*, void*}* %alloca-tuple2a, i32 0, i32 1)",
            ),
            (
                "Err(cannot convert <null+1, null+2>[1..] to value with type i32*)",
                "%1 = load i32*, void** getelementptr (i8, i8* %alloca-tuple2a, i32 1)",
            ),
            // ret
            ("Ok(ret())", "ret void"),
            ("Ok(ret(<i32 1>))", "ret i32 1"),
            ("Ok(ret(<i1 true>))", "ret i32 %true"),
            // store: basic types
            (
                "Ok(store-to(<i32 257>, alloca#0))",
                "store i32 257, i32* %alloca-i32",
            ),
            (
                "Ok(store-to(<i32 255>, alloca#0))",
                "store i8 -1, i8* %alloca-i32",
            ),
            (
                "Err(cannot write i64 value at <i32 255>[0..])",
                "store i64 4294967297, i64* %alloca-i32",
            ),
            (
                "Ok(store-to(<i32 -1>, alloca#0))",
                "store i64 -1, i32* %alloca-i32",
            ),
            (
                "Ok(store-to(<i32 -1>, alloca#0))",
                "store i64 4294967295, i32* %alloca-i32",
            ),
            (
                "Err(cannot store value to <i1 true>)",
                "store i32 257, i32* %true",
            ),
            (
                "Err(illegal store target type opaque*)",
                "store i64 4294967297, opaque* %alloca-i32",
            ),
            (
                "Ok(store-to(<i32 257>, heap#0))",
                "store i32 257, i32* %malloc-i32",
            ),
            (
                "Err(cannot deref addr heap#2+0 containing poison with size 32)",
                "store i32 257, i32* %malloc-poison32",
            ),
            // store: getelementptr: ints
            (
                "Ok(store-to(<i32 10, i32 2>, alloca#1))",
                "store i32 10, i32* getelementptr ({i32, i32}, {i32, i32}* %alloca-tuple2i, i32 0, i32 0)",
            ),
            (
                "Ok(store-to(<i32 1, i32 20>, alloca#1))",
                "store i32 20, i32* getelementptr ({i32, i32}, {i32, i32}* %alloca-tuple2i, i32 0, i32 1)",
            ),
            (
                "Ok(store-to(<i32 65537, i32 2>, alloca#1))",
                "store i16 1, i16* getelementptr (i16, i16* %alloca-tuple2i, i32 1)",
            ),
            (
                "Err(cannot write i16 value at <i32 1, i32 2>[3..])",
                "store i16 1, i16* getelementptr (i8, i8* %alloca-tuple2i, i32 3)",
            ),
            (
                "Ok(store-to(<i32 undef@0xffff00ff(2560)>, alloca#5))",
                "store i8 10, i8* getelementptr (i8, i8* %alloca-i32p, i32 1)",
            ),
            (
                "Ok(store-to(<i32 undef@0x000000ff(659968)>, alloca#5))",
                "store i16 10, i16* getelementptr (i16, i16* %alloca-i32p, i32 1)",
            ),
            (
                "Ok(store-to(<i32 10>, alloca#5))",
                "store i32 10, i32* getelementptr (i32, i32* %alloca-i32p, i32 0)",
            ),
            // store: getelementptr: floats
            (
                "Ok(store-to(<float 10, float 2>, alloca#2))",
                "store float 10, float* getelementptr ({float, float}, {float, float}* %alloca-tuple2f, i32 0, i32 0)",
            ),
            (
                "Ok(store-to(<float 1, float 20>, alloca#2))",
                "store float 20, float* getelementptr ({float, float}, {float, float}* %alloca-tuple2f, i32 0, i32 1)",
            ),
            (
                "Err(cannot write <float 1, float 2>[1..] with float 1)",
                "store float 1, float* getelementptr (i8, i8* %alloca-tuple2f, i32 1)",
            ),
            // store: getelementptr: doubles
            (
                "Ok(store-to(<double 10, double 2>, alloca#3))",
                "store double 10, double* getelementptr ({double, double}, {double, double}* %alloca-tuple2d, i32 0, i32 0)",
            ),
            (
                "Ok(store-to(<double 1, double 20>, alloca#3))",
                "store double 20, double* getelementptr ({double, double}, {double, double}* %alloca-tuple2d, i32 0, i32 1)",
            ),
            (
                "Err(cannot write <double 1, double 2>[1..] with double 1)",
                "store double 1, float* getelementptr (i8, i8* %alloca-tuple2d, i32 1)",
            ),
            // store: getelementptr: addrs
            (
                "Ok(store-to(<null+0, null+2>, alloca#4))",
                "store void* null, void** getelementptr ({void*, void*}, {void*, void*}* %alloca-tuple2a, i32 0, i32 0)",
            ),
            (
                "Ok(store-to(<null+1, null+0>, alloca#4))",
                "store void* null, void** getelementptr ({void*, void*}, {void*, void*}* %alloca-tuple2a, i32 0, i32 1)",
            ),
            (
                "Err(cannot write <null+1, null+2>[1..] with null+0)",
                "store void *null, void** getelementptr (i8, i8* %alloca-tuple2a, i32 1)",
            ),
            // value
            (
                "Ok(define-local(%1, <float -1>))",
                "%1 = fsub float 1.0, 2.0",
            ),
            // value: bitcast for poisons
            (
                "Ok(collapse-poison(%1, heap#2+0, [8 x i32]))",
                "%1 = bitcast i8* %malloc-poison32 to [8 x i32]*",
            ),
        ] {
            let mut parser = LLIRParser::new(input, "input").expect(input);
            let (insn, _) = parser.parse_insn().expect(input).expect(input);
            let mut interp = new_interp();
            enter_dummy(&mut interp);
            let got = match interp.eval_insn(&insn) {
                Ok(val) => format!("Ok({})", val),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn interp_run() {
        for (expected, funcname) in vec![
            ("Some(<i32 0>)", "main"),
            (
                "@deref_inner_alloca%0#1: cannot use alloca#0+0 after free",
                "deref_inner_alloca",
            ),
            ("Some(<float -1>)", "sub_stored_floats"),
            ("Some(<heap#0+0>)", "malloc_tuple2i"),
            (
                "@malloc_overflow%0#2: type i64 unmatches poison with size 2 at heap#0+0",
                "malloc_overflow",
            ),
            (
                "@malloc_underflow%0#2: type i64 unmatches poison with size 16 at heap#0+0",
                "malloc_underflow",
            ),
        ] {
            let mut interp = new_interp();
            interp.start(GlobalIdent::from(funcname)).expect(funcname);
            loop {
                if let Err(err) = interp.step() {
                    let trace = interp.stacktrace().expect(funcname);
                    let got = format!("{}: {}", DisplayIter("", trace.iter(), "/", ""), err);
                    assert_eq!(expected, got, "{}", funcname);
                    break;
                }
                if let State::Finished(res) = interp.state() {
                    let got = match res {
                        Some(v) => format!("Some({})", v),
                        None => format!("None"),
                    };
                    assert_eq!(expected, got, "{}", funcname);
                    break;
                }
            }
        }
    }
}
