//! The ABI emulation module of LLIR.

use crate::llir::syntax::{ExtIdent, GetelementptrArgs, Type, TypedValue, Typedefs};
use std::collections::BTreeMap;
use std::fmt;

/// An affine expression `base + prod(scale*tyval)`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AffineExpr<I: ExtIdent> {
    base: i64,
    terms: Vec<(i64, TypedValue<I>)>,
}

impl<I: ExtIdent> AffineExpr<I> {
    /// Returns a new affine expression `base`.
    pub fn new(base: i64) -> AffineExpr<I> {
        AffineExpr {
            base,
            terms: Vec::new(),
        }
    }
    /// Returns the base.
    pub fn base(&self) -> i64 {
        self.base
    }
    /// Returns the linear terms `[(scale, tyval)]`.
    pub fn terms(&self) -> &[(i64, TypedValue<I>)] {
        &self.terms
    }
    /// Adds the constant to the base.
    pub fn add_const(&mut self, c: i64) {
        self.base += c;
    }
    /// Adds the linear term to the expression.
    pub fn add_scaled(&mut self, scale: i64, tyval: &TypedValue<I>) {
        match tyval.1.try_to_i64() {
            Some(val) => self.base += val * scale,
            None => {
                for term in &mut self.terms {
                    if &term.1 == tyval {
                        term.0 += scale;
                        return;
                    }
                }
                self.terms.push((scale, tyval.clone()));
            }
        }
    }
    /// Adds the other to the expression.
    pub fn add(&mut self, other: &AffineExpr<I>) {
        self.add_const(other.base);
        for (scale, tyval) in &other.terms {
            self.add_scaled(*scale, tyval);
        }
    }
    /// Returns the base if the expression is constant.
    /// Otherwise returns `None`.
    pub fn try_to_i64(&self) -> Option<i64> {
        if self.terms.is_empty() {
            return Some(self.base);
        }
        None
    }
}

impl<I: ExtIdent> fmt::Display for AffineExpr<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.base)?;
        for (scale, tyval) in &self.terms {
            write!(f, "{:+}*({})", scale, tyval)?;
        }
        Ok(())
    }
}

/// A result of `getelementptr` instruction.
#[derive(Clone, Debug)]
pub struct GetelementptrResult<I: ExtIdent> {
    /// The index in the form of an affine expression.
    pub index: AffineExpr<I>,
    /// The offset in the form of an affine expression.
    pub offset: AffineExpr<I>,
    /// The type of the result pointer.
    pub ty: Type<I>,
}

/// A data layout.
#[derive(Clone, Debug, PartialEq)]
pub struct DataLayout {
    is_little: bool,
    mangling: String,
    pointers: BTreeMap<u32, (u32, u32, u32, u32)>,
    int_aligns: BTreeMap<u32, u32>,
    float_aligns: BTreeMap<u32, u32>,
    native_int_widths: Vec<u32>,
    stack_align: Option<u32>,
}

impl DataLayout {
    /// Returns a parsed data layout (`target datalayout` in LLIR).
    pub fn parse(s: &str) -> Result<DataLayout, String> {
        let mut datalayout = DataLayout {
            is_little: false,
            mangling: String::from(""),
            pointers: BTreeMap::new(),
            int_aligns: BTreeMap::new(),
            float_aligns: BTreeMap::new(),
            native_int_widths: Vec::new(),
            stack_align: None,
        };
        for spec in s.split('-') {
            if datalayout.parse_spec(spec).is_none() {
                return Err(format!("unsupported spec {:?}", spec));
            }
        }
        Ok(datalayout)
    }
    /// Returns a data layout representing that of LP64 ABI (`target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"`)
    pub fn lp64() -> DataLayout {
        DataLayout::parse("e-m:o-i64:64-f80:128-n8:16:32:64-S128").unwrap()
    }
    fn parse_ints(spec: &str) -> Option<Vec<u32>> {
        let mut v = Vec::new();
        for s in spec.split(':') {
            v.push(s.parse::<u32>().ok()?);
        }
        Some(v)
    }
    fn parse_spec(&mut self, spec: &str) -> Option<()> {
        if spec == "E" || spec == "e" {
            self.is_little = spec == "e";
        } else if let Some(argstr) = spec.strip_prefix('f') {
            let args = Self::parse_ints(argstr)?;
            match args.len() {
                2 => self.float_aligns.insert(args[0], args[1]),
                _ => return None,
            };
        } else if let Some(argstr) = spec.strip_prefix('i') {
            let args = Self::parse_ints(argstr)?;
            match args.len() {
                2 => self.int_aligns.insert(args[0], args[1]),
                _ => return None,
            };
        } else if let Some(argstr) = spec.strip_prefix("m:") {
            self.mangling = String::from(argstr);
        } else if let Some(argstr) = spec.strip_prefix('n') {
            let mut args = Self::parse_ints(argstr)?;
            self.native_int_widths.append(&mut args);
        } else if let Some(argstr) = spec.strip_prefix('p') {
            let args = Self::parse_ints(argstr)?;
            let info = match args.len() {
                3 => (args[1], args[2], args[1], args[1]),
                4 => (args[1], args[2], args[3], args[1]),
                5 => (args[1], args[2], args[3], args[1]),
                _ => return None,
            };
            self.pointers.insert(args[0], info);
        } else if let Some(argstr) = spec.strip_prefix('S') {
            let args = Self::parse_ints(argstr)?;
            self.stack_align = match args.len() {
                1 => Some(args[0]),
                _ => return None,
            };
        } else {
            return None;
        }
        Some(())
    }
    /// Returns the alignment in byte of type `i$size`.
    pub fn alignof_int(&self, size: u32) -> u32 {
        match self.int_aligns.get(&size) {
            Some(n) => (*n + 7) / 8,
            None => (size + 7) / 8,
        }
    }
    /// Returns the alignment in byte of the type.
    pub fn alignof_type<I: ExtIdent>(&self, ty: &Type<I>, typedefs: &Typedefs<I>) -> Option<i64> {
        match ty {
            Type::Void | Type::Opaque | Type::Func(_) | Type::Metadata => None,
            Type::I1 => Some(self.alignof_int(1) as i64),
            Type::I8 => Some(self.alignof_int(8) as i64),
            Type::I16 => Some(self.alignof_int(16) as i64),
            Type::I32 => Some(self.alignof_int(32) as i64),
            Type::I64 => Some(self.alignof_int(64) as i64),
            Type::Float => Some(4),
            Type::Double => Some(8),
            Type::X86Fp80 => Some(16),
            Type::Ptr(_) => Some(self.alignof_int(64) as i64),
            Type::Vector(_, n, ty) => Some(*n as i64 * self.alignof_type(ty, typedefs)?),
            Type::Array(_, ty) => self.alignof_type(ty, typedefs),
            Type::Struct(false, fields) => match fields.first() {
                Some(first) => self.alignof_type(first, typedefs),
                None => Some(1),
            },
            Type::Struct(true, _) => Some(1),
            Type::Name(sym) => self.alignof_type(typedefs.get(sym)?, typedefs),
            Type::Ext(_, orig) => self.alignof_type(orig, typedefs),
        }
    }
    /// Returns the pair of the field index and the field offset in the (packed) struct of `fields` at offset.
    pub fn field_at<I: ExtIdent>(
        &self,
        packed: bool,
        fields: &[Type<I>],
        offset: i64,
        typedefs: &Typedefs<I>,
    ) -> Option<(usize, i64)> {
        let mut delta = 0;
        for (i, field) in fields.iter().enumerate() {
            if !packed {
                let align = self.alignof_type(field, typedefs)?;
                delta = (delta + align - 1) / align * align;
            }
            if offset < delta {
                return None;
            }
            let size = self.sizeof_type(field, typedefs)?;
            if delta <= offset && offset < delta + size {
                return Some((i, delta));
            }
            delta += size;
        }
        None
    }
    /// Returns the field offset in the (packed) struct of `fields` by field index.
    pub fn offsetof_field<I: ExtIdent>(
        &self,
        packed: bool,
        fields: &[Type<I>],
        idx: usize,
        typedefs: &Typedefs<I>,
    ) -> Option<i64> {
        if idx > fields.len() {
            return None;
        }
        let mut offset = 0;
        for (i, field) in fields.iter().enumerate() {
            if !packed {
                let align = self.alignof_type(field, typedefs)?;
                offset = (offset + align - 1) / align * align;
            }
            if i >= idx {
                break;
            }
            offset += self.sizeof_type(field, typedefs)?;
        }
        if !packed && idx == fields.len() && !fields.is_empty() {
            let align = self.alignof_type(&fields[0], typedefs)?;
            offset = (offset + align - 1) / align * align;
        }
        Some(offset)
    }
    /// Returns the size of the type.
    pub fn sizeof_type<I: ExtIdent>(&self, ty: &Type<I>, typedefs: &Typedefs<I>) -> Option<i64> {
        match ty {
            Type::Void | Type::Opaque | Type::Func(_) | Type::Metadata => None,
            Type::I1 => Some(1),
            Type::I8 => Some(1),
            Type::I16 => Some(2),
            Type::I32 => Some(4),
            Type::I64 => Some(8),
            Type::Float => Some(4),
            Type::Double => Some(8),
            Type::X86Fp80 => Some(16),
            Type::Ptr(_) => Some(8),
            Type::Vector(false, n, ty) => Some(*n as i64 * self.sizeof_type(ty, typedefs)?),
            Type::Vector(true, _, _) => None,
            Type::Array(n, ty) => Some(*n as i64 * self.sizeof_type(ty, typedefs)?),
            Type::Struct(packed, fields) => {
                self.offsetof_field(*packed, fields, fields.len(), typedefs)
            }
            Type::Name(sym) => self.sizeof_type(typedefs.get(sym)?, typedefs),
            Type::Ext(_, orig) => self.sizeof_type(orig, typedefs),
        }
    }
    /// Returns the result of instruction `extractvalue` that is a pair of the offset and the type.
    pub fn extractvalue<'a, 'b, I: ExtIdent>(
        &self,
        basety0: &'a Type<I>,
        args: &[u32],
        typedefs: &'b Typedefs<I>,
    ) -> Result<(usize, &'b Type<I>), String>
    where
        'a: 'b,
    {
        if args.is_empty() {
            return Ok((0, basety0));
        }
        let basety = basety0.normalize(typedefs)?;
        let index = args[0] as usize;
        match basety {
            Type::Array(n, ty) => {
                if index >= *n as usize {
                    return Err(format!(
                        "out-of-bound index {} in base type {}",
                        index, basety0
                    ));
                }
                let size = self.sizeof_type(ty, typedefs).unwrap();
                let (o, ty) = self.extractvalue(ty, &args[1..], typedefs)?;
                Ok((size as usize * index + o, ty))
            }
            Type::Struct(packed, fields) => {
                if index >= fields.len() {
                    return Err(format!(
                        "out-of-bound index {} in base type {}",
                        index, basety0
                    ));
                };
                let delta = self
                    .offsetof_field(*packed, fields, index, typedefs)
                    .unwrap();
                let (o, ty) = self.extractvalue(&fields[index], &args[1..], typedefs)?;
                Ok((delta as usize + o, ty))
            }
            Type::Ext(_, orig) => self.extractvalue(orig, args, typedefs),
            _ => Err(format!("illegal base type {}", basety0)),
        }
    }
    fn do_getelementptr<'a, 'b, I: ExtIdent>(
        &self,
        offset: &mut AffineExpr<I>,
        base_ty0: &'a Type<I>,
        args: &[(bool, TypedValue<I>)],
        typedefs: &'b Typedefs<I>,
    ) -> Result<&'b Type<I>, String>
    where
        'a: 'b,
    {
        if args.is_empty() {
            return Ok(base_ty0);
        }
        let base_ty = base_ty0.normalize(typedefs)?;
        match base_ty {
            Type::Ptr(_) => {
                // Indexing into vector type is not recommended.
                // https://llvm.org/docs/GetElementPtr.html#can-gep-index-into-vector-elements
                return Err(format!("cannot index into pointer type {}", base_ty0));
            }
            Type::Vector(..) => return Err(format!("cannot index into vector type {}", base_ty0)),
            Type::Array(_, ty) => {
                let size = self.sizeof_type(ty, typedefs).unwrap();
                offset.add_scaled(size, &args[0].1);
                self.do_getelementptr(offset, ty, &args[1..], typedefs)
            }
            Type::Struct(packed, fields) => {
                let index = match (args[0].1).1.try_to_i64() {
                    Some(index) if 0 <= index && (index as usize) < fields.len() => index as usize,
                    _ => {
                        return Err(format!(
                            "illegal index {} in base type {}",
                            (args[0].1).1,
                            base_ty0
                        ))
                    }
                };
                let o = self
                    .offsetof_field(*packed, fields, index, typedefs)
                    .unwrap();
                offset.add_const(o);
                self.do_getelementptr(offset, &fields[index], &args[1..], typedefs)
            }
            Type::Name(name) => unreachable!("{}", name),
            Type::Ext(_, orig) => self.do_getelementptr(offset, orig, args, typedefs),
            _ => Err(format!("cannot index into type {}", base_ty0)),
        }
    }
    /// Returns the result of instruction `getelementptr`.
    pub fn getelementptr<I: ExtIdent>(
        &self,
        args: &GetelementptrArgs<I>,
        typedefs: &Typedefs<I>,
    ) -> Result<GetelementptrResult<I>, String> {
        let size = match self.sizeof_type(&args.base_ty, typedefs) {
            Some(size) => size,
            None => return Err(format!("size of base type {} is unknown", args.base_ty)),
        };
        let mut index = AffineExpr::new(0);
        match args.indices.get(0) {
            Some(i) => index.add_scaled(size, &i.1),
            None => return Err("empty index".to_string()),
        }
        let mut offset = AffineExpr::new(0);
        let ty = self.do_getelementptr(&mut offset, &args.base_ty, &args.indices[1..], typedefs)?;
        Ok(GetelementptrResult {
            index,
            offset,
            ty: Type::Ptr(Box::new(ty.clone())),
        })
    }
}

impl fmt::Display for DataLayout {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", if self.is_little { "e" } else { "E" })?;
        write!(f, "-m:{}", self.mangling)?;
        if !self.pointers.is_empty() {
            for (n, info) in self.pointers.iter() {
                write!(f, "-p{}:{}:{}:{}:{}", n, info.0, info.1, info.2, info.3)?;
            }
        }
        if !self.int_aligns.is_empty() {
            write!(f, "-i")?;
            for (k, v) in self.int_aligns.iter() {
                write!(f, "{}:{}", k, v)?;
            }
        }
        if !self.float_aligns.is_empty() {
            write!(f, "-f")?;
            for (k, v) in self.float_aligns.iter() {
                write!(f, "{}:{}", k, v)?;
            }
        }
        if !self.native_int_widths.is_empty() {
            write!(f, "-n")?;
            for (i, v) in self.native_int_widths.iter().enumerate() {
                if i > 0 {
                    write!(f, ":")?;
                }
                write!(f, "{}", v)?;
            }
        }
        if let Some(stack_align) = self.stack_align {
            write!(f, "-S{}", stack_align)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fmt::DisplayIter;
    use crate::llir::parser::Parser;
    use crate::llir::syntax::{ExtIdentUnit, Insn, LocalIdent, Value};
    #[test]
    fn format_affine_expr() {
        for (expected, input) in vec![
            (
                "4",
                AffineExpr::<ExtIdentUnit> {
                    base: 4,
                    terms: vec![],
                },
            ),
            (
                "-4+8*(i32 %1)-16*(i64 %2)",
                AffineExpr::<ExtIdentUnit> {
                    base: -4,
                    terms: vec![
                        (
                            8,
                            TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("1"))),
                        ),
                        (
                            -16,
                            TypedValue(Type::I64, Value::LocalRef(LocalIdent::from("2"))),
                        ),
                    ],
                },
            ),
        ] {
            assert_eq!(expected, input.to_string());
        }
    }
    #[test]
    fn affine_expr_add() {
        let mut offset = AffineExpr::<ExtIdentUnit>::new(4);
        offset.add_scaled(-4, &TypedValue(Type::I64, Value::I64(2)));
        offset.add_scaled(
            4,
            &TypedValue(Type::I32, Value::LocalRef(LocalIdent::from("1"))),
        );
        offset.add_scaled(
            -16,
            &TypedValue(Type::I64, Value::LocalRef(LocalIdent::from("2"))),
        );
        offset.add_scaled(
            4,
            &TypedValue(Type::I64, Value::LocalRef(LocalIdent::from("1"))),
        );
        assert_eq!("-4+4*(i32 %1)-16*(i64 %2)+4*(i64 %1)", offset.to_string());
        offset.add(&offset.clone());
        assert_eq!("-8+8*(i32 %1)-32*(i64 %2)+8*(i64 %1)", offset.to_string());
    }
    #[test]
    fn format_data_layout() {
        for (expected, input) in vec![
            (
                "e-m:o-i64:64-f80:128-n8:16:32:64-S128",
                DataLayout {
                    is_little: true,
                    mangling: String::from("o"),
                    pointers: btree_map![],
                    int_aligns: btree_map![64 => 64],
                    float_aligns: btree_map![80 => 128],
                    native_int_widths: vec![8, 16, 32, 64],
                    stack_align: Some(128),
                }
            ),
            (
                "e-m:o-p270:32:32:32:32-p271:32:32:32:32-p272:64:64:64:64-i64:64-f80:128-n8:16:32:64-S128",
                DataLayout {
                    is_little: true,
                    mangling: String::from("o"),
                    pointers: btree_map![270 => (32, 32, 32, 32), 271 => (32, 32, 32, 32), 272 => (64, 64, 64, 64)],
                    int_aligns: btree_map![64 => 64],
                    float_aligns: btree_map![80 => 128],
                    native_int_widths: vec![8, 16, 32, 64],
                    stack_align: Some(128),
                }
            ),
        ] {
            assert_eq!(expected, input.to_string());
        }
    }
    #[test]
    fn parse_data_layout() {
        for (expected, input) in vec![
            ("e-m:o-i64:64-f80:128-n8:16:32:64-S128", "e-m:o-i64:64-f80:128-n8:16:32:64-S128"),
            ("e-m:o-p270:32:32:32:32-p271:32:32:32:32-p272:64:64:64:64-i64:64-f80:128-n8:16:32:64-S128",
            "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"),
        ] {
            let got = DataLayout::parse(input).expect(input);
            assert_eq!(expected, got.to_string(), "{}", input);
        }
    }
    fn new_typedefs() -> Typedefs<ExtIdentUnit> {
        Typedefs::new(btree_map![
            LocalIdent::from("int") => Parser::new_type("i32"),
            LocalIdent::from("tuple2") => Parser::new_type("{ i32, i32 }"),
            LocalIdent::from("tuple3") => Parser::new_type("{ %tuple2, i32 }"),
            LocalIdent::from("tuple2ext") => Type::Ext(
                ExtIdentUnit(),
                Box::new(Parser::new_type("{ i64, i64 }")),
            )
        ])
    }
    #[test]
    fn typeenv_alignof_type() {
        let datalayout = DataLayout::lp64();
        let typedefs = new_typedefs();
        for (expected, input) in vec![
            (None, Type::Void),
            (Some(1), Type::I1),
            (Some(1), Type::I8),
            (Some(2), Type::I16),
            (Some(4), Type::I32),
            (Some(8), Type::I64),
            (Some(4), Type::Float),
            (Some(8), Type::Double),
            (Some(16), Type::X86Fp80),
            (Some(8), Type::Ptr(Box::new(Type::I8))),
            (Some(16), Type::Vector(false, 4, Box::new(Type::I32))),
            (Some(16), Type::Vector(true, 4, Box::new(Type::I32))),
            (Some(4), Type::Array(4, Box::new(Type::I32))),
            (Some(1), Type::Struct(false, vec![])),
            (Some(4), Type::Struct(false, vec![Type::I32, Type::I64])),
            (Some(1), Type::Struct(true, vec![Type::I32, Type::I64])),
            (None, Type::Opaque),
            (None, Parser::new_type("i32 (void)")),
            (Some(4), Parser::new_type("%int")),
            (None, Type::Metadata),
            (Some(8), Type::Ext(ExtIdentUnit(), Box::new(Type::I64))),
        ] {
            let got = datalayout.alignof_type(&input, &typedefs);
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn datalayout_field_at() {
        let datalayout = DataLayout::lp64();
        let typedefs = new_typedefs();
        let fields1 = vec![Type::I8, Type::I16, Type::I32];
        for (expected, packed, fields, offset) in vec![
            (None, false, &vec![], 0),
            (None, true, &vec![], 0),
            (Some((0, 0)), false, &fields1, 0),
            (None, false, &fields1, 1),
            (Some((1, 2)), false, &fields1, 2),
            (Some((1, 2)), false, &fields1, 3),
            (Some((2, 4)), false, &fields1, 4),
            (None, false, &fields1, 8),
            (Some((0, 0)), true, &fields1, 0),
            (Some((1, 1)), true, &fields1, 1),
            (Some((1, 1)), true, &fields1, 2),
            (Some((2, 3)), true, &fields1, 3),
            (None, true, &fields1, 7),
        ] {
            let got = datalayout.field_at(packed, fields, offset, &typedefs);
            assert_eq!(
                expected,
                got,
                "({}, {}, {})",
                packed,
                DisplayIter("[", fields.iter(), ", ", "]"),
                offset
            );
        }
    }
    #[test]
    fn data_layout_offsetof_field() {
        let datalayout = DataLayout::lp64();
        let typedefs = new_typedefs();
        let fields1 = vec![Type::I8, Type::I16, Type::I32];
        let fields2 = vec![Type::I32, Type::I16, Type::I8];
        for (expected, packed, fields, offset) in vec![
            (Some(0), false, &vec![], 0),
            (None, false, &vec![], 1),
            (Some(0), true, &vec![], 0),
            (None, true, &vec![], 1),
            (Some(0), false, &fields1, 0),
            (Some(2), false, &fields1, 1),
            (Some(4), false, &fields1, 2),
            (Some(8), false, &fields1, 3),
            (None, false, &fields1, 4),
            (Some(0), true, &fields1, 0),
            (Some(1), true, &fields1, 1),
            (Some(3), true, &fields1, 2),
            (Some(7), true, &fields1, 3),
            (None, true, &fields1, 4),
            (Some(0), false, &fields2, 0),
            (Some(4), false, &fields2, 1),
            (Some(6), false, &fields2, 2),
            (Some(8), false, &fields2, 3),
            (None, false, &fields2, 4),
            (Some(0), true, &fields2, 0),
            (Some(4), true, &fields2, 1),
            (Some(6), true, &fields2, 2),
            (Some(7), true, &fields2, 3),
            (None, true, &fields2, 4),
        ] {
            let got = datalayout.offsetof_field(packed, fields, offset, &typedefs);
            assert_eq!(
                expected,
                got,
                "({}, {}, {})",
                packed,
                DisplayIter("[", fields.iter(), ", ", "]"),
                offset
            );
        }
    }
    #[test]
    fn data_layout_sizeof_type() {
        let datalayout = DataLayout::lp64();
        let typedefs = new_typedefs();
        for (expected, input) in vec![
            (None, Type::Void),
            (Some(1), Type::I1),
            (Some(1), Type::I8),
            (Some(2), Type::I16),
            (Some(4), Type::I32),
            (Some(8), Type::I64),
            (Some(4), Type::Float),
            (Some(8), Type::Double),
            (Some(16), Type::X86Fp80),
            (Some(8), Type::Ptr(Box::new(Type::I8))),
            (Some(16), Type::Vector(false, 4, Box::new(Type::I32))),
            (None, Type::Vector(true, 4, Box::new(Type::I32))),
            (Some(16), Type::Struct(false, vec![Type::I32, Type::I64])),
            (Some(12), Type::Struct(true, vec![Type::I32, Type::I64])),
            (None, Type::Opaque),
            (None, Parser::new_type("i32 (void)")),
            (Some(4), Parser::new_type("%int")),
            (None, Type::Metadata),
            (Some(8), Type::Ext(ExtIdentUnit(), Box::new(Type::I64))),
        ] {
            let got = datalayout.sizeof_type(&input, &typedefs);
            assert_eq!(expected, got, "{}", input);
        }
    }
    #[test]
    fn data_layout_extractvalue() {
        let datalayout = DataLayout::lp64();
        let typedefs = new_typedefs();
        for (expected, basety, args) in vec![
            // structs
            ("Ok((4, i32))", "%tuple2", vec![1]),
            (
                "Err(out-of-bound index 2 in base type %tuple2)",
                "%tuple2",
                vec![2],
            ),
            ("Err(illegal base type i32)", "%tuple2", vec![0, 0]),
            // arrays
            ("Ok((4, i32))", "[2 x i32]", vec![1]),
            (
                "Err(out-of-bound index 2 in base type [2 x i32])",
                "[2 x i32]",
                vec![2],
            ),
            ("Err(illegal base type i32)", "[2 x i32]", vec![0, 0]),
            // extended types
            ("Ok((8, i64))", "%tuple2ext", vec![1]),
            // other types
            ("Err(illegal base type i32)", "i32", vec![1]),
        ] {
            let basety = Parser::new_type(basety);
            let got = match datalayout.extractvalue(&basety, &args, &typedefs) {
                Ok((o, ty)) => format!("Ok(({}, {}))", o, ty),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "({}, {:?})", basety, args);
        }
    }
    #[test]
    fn data_layout_getelementptr() {
        let datalayout = DataLayout::lp64();
        let typedefs = new_typedefs();
        for (expected, insn) in vec![
            (
                "Err(size of base type void is unknown)",
                "%10 = getelementptr void, void* %0",
            ),
            (
                "Err(empty index)",
                "%10 = getelementptr %tuple2, %tuple2* %0",
            ),
            // structs
            (
                "Ok((16, 0, %tuple2*))",
                "%10 = getelementptr %tuple2, %tuple2* %0, i32 2",
            ),
            (
                "Ok((0+8*(i32 %1), 0, %tuple2*))",
                "%10 = getelementptr %tuple2, %tuple2* %0, i32 %1",
            ),
            (
                "Ok((16, 4, i32*))",
                "%10 = getelementptr %tuple2, %tuple2* %0, i32 2, i32 1",
            ),
            (
                "Err(illegal index -1 in base type %tuple2)",
                "%10 = getelementptr %tuple2, %tuple2* %0, i32 2, i32 -1",
            ),
            (
                "Err(illegal index 2 in base type %tuple2)",
                "%10 = getelementptr %tuple2, %tuple2* %0, i32 2, i32 2",
            ),
            (
                "Err(illegal index %1 in base type %tuple2)",
                "%10 = getelementptr %tuple2, %tuple2* %0, i32 2, i32 %1",
            ),
            (
                "Ok((24, 0, %tuple2*))",
                "%10 = getelementptr %tuple3, %tuple3* %0, i32 2, i32 0",
            ),
            (
                "Ok((24, 4, i32*))",
                "%10 = getelementptr %tuple3, %tuple3* %0, i32 2, i32 0, i32 1",
            ),
            (
                "Ok((16, 0, %tuple3**))",
                "%10 = getelementptr %tuple3*, %tuple3** %0, i32 2",
            ),
            // pointers in structs
            (
                "Err(cannot index into pointer type %tuple3*)",
                "%10 = getelementptr %tuple3*, %tuple3** %0, i32 2, i32 2",
            ),
            // arrays
            (
                "Ok((0, 8, i32*))",
                "%10 = getelementptr inbounds [4 x i32], [4 x i32]* %0, i64 0, i64 2",
            ),
            (
                "Ok((0, -4, i32*))",
                "%10 = getelementptr inbounds [4 x i32], [4 x i32]* %0, i64 0, i64 -1",
            ),
            (
                "Ok((0, 16, i32*))",
                "%10 = getelementptr inbounds [4 x i32], [4 x i32]* %0, i64 0, i64 4",
            ),
            (
                "Ok((0, 0+4*(i64 %1), i32*))",
                "%10 = getelementptr inbounds [4 x i32], [4 x i32]* %0, i64 0, i64 %1",
            ),
            // vectors
            (
                "Err(cannot index into vector type <4 x i32>)",
                "%10 = getelementptr inbounds <4 x i32>, <4 x i32>* %0, i64 0, i64 2",
            ),
            // extended types
            (
                "Ok((0, 8, i64*))",
                "%10 = getelementptr %tuple2ext, %tuple2ext* %0, i32 0, i32 1",
            ),
            // other types
            (
                "Err(cannot index into type i32)",
                "%10 = getelementptr i32, i32* %0, i32 0, i32 2",
            ),
        ] {
            let mut parser = Parser::new(insn, "source").expect(insn);
            let args = match parser.parse_insn().expect(insn).expect(insn) {
                (Insn::Value(_, Value::Getelementptr(args)), _) => args,
                (insn, _) => panic!("unexpected insn {}", insn),
            };
            let got = match datalayout.getelementptr(&args, &typedefs) {
                Ok(res) => format!("Ok(({}, {}, {}))", res.index, res.offset, res.ty),
                Err(err) => format!("Err({})", err),
            };
            assert_eq!(expected, got, "{}", insn);
        }
    }
}
