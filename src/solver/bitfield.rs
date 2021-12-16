//! The bit field module.

use crate::fmt::DisplayIter;
use crate::num::bitlsh;
use crate::ops::TotallyComparable;
use crate::solver::syntax::{Cond, CondConst, CondExpr, CondPred, CondVar};
use crate::solver::union_find::UnionFind;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A bit field.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitField<T: TotallyComparable> {
    tag: T,
    mask: u64,
}

impl<T: TotallyComparable> BitField<T> {
    /// Returns a new bit field with the given tag and mask.
    pub fn new(tag: T, mask: u64) -> BitField<T> {
        BitField { tag, mask }
    }
    /// Returns the tag.
    pub fn tag(&self) -> &T {
        &self.tag
    }
    /// Returns the mask.
    pub fn mask(&self) -> u64 {
        self.mask
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.mask == 0x0
    }
    /// Returns `true` if contained in the other.
    pub fn is_less(&self, other: &BitField<T>) -> bool {
        self.tag == other.tag && self.mask & other.mask == self.mask
    }
    /// Returns the intersection with the other.
    pub fn and(&self, other: &BitField<T>) -> BitField<T> {
        if self.tag() == other.tag() {
            return BitField::new(self.tag.clone(), self.mask & other.mask);
        }
        BitField::new(self.tag.clone(), 0x0)
    }
    /// Returns the intersection with the mask.
    pub fn and_mask(&self, mask: u64) -> BitField<T> {
        BitField::new(self.tag.clone(), self.mask & mask)
    }
    /// Returns the difference from the other.
    pub fn diff(&self, other: &BitField<T>) -> BitField<T> {
        if self.tag == other.tag {
            return BitField::new(self.tag.clone(), self.mask & !other.mask);
        }
        self.clone()
    }
}

impl<T: TotallyComparable> fmt::Display for BitField<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}&{:#x}", self.tag, self.mask)
    }
}

/// A bit field builder.
#[derive(Clone, Copy, Debug)]
pub struct BitFieldBuilder {
    mask: u64,
    shift: i64,
}

impl BitFieldBuilder {
    /// Returns a new bit field builder initialized with a full bit field.
    pub fn full() -> BitFieldBuilder {
        BitFieldBuilder { mask: !0, shift: 0 }
    }
    /// Returns the condition variable and a bit field built from the expression.
    pub fn build_from_condexpr(expr: &CondExpr) -> Option<BitField<CondExpr>> {
        let builder = BitFieldBuilder::full();
        builder
            .do_build_from_condexpr(expr)
            .map(|(expr, builder)| builder.into_bitfield(expr))
    }
    /// Returns the intersection with the number.
    pub fn and(self, n: u64) -> BitFieldBuilder {
        BitFieldBuilder {
            mask: self.mask & n,
            shift: self.shift,
        }
    }
    /// Returns the shifted to right by the number.
    pub fn lshr(self, n: u64) -> BitFieldBuilder {
        let shift = self.shift + (n as i64);
        BitFieldBuilder {
            mask: bitlsh(self.mask, n as i64),
            shift,
        }
    }
    /// Returns the shifted to left by the number.
    pub fn lshl(self, n: u64) -> BitFieldBuilder {
        let shift = self.shift - (n as i64);
        BitFieldBuilder {
            mask: bitlsh(self.mask, -(n as i64)),
            shift,
        }
    }
    /// Project the number onto.
    pub fn project_u64(&self, n: u64) -> u64 {
        bitlsh(n, self.shift) & self.mask
    }
    fn do_build_from_condexpr(self, expr: &CondExpr) -> Option<(CondExpr, BitFieldBuilder)> {
        match expr {
            CondExpr::Const(_) => None,
            CondExpr::Var(_) | CondExpr::Deref(_) => Some((expr.clone(), self)),
            CondExpr::Bitand(expr, val) => match val {
                CondConst::U64(n) => self.and(*n),
            }
            .do_build_from_condexpr(expr),
            CondExpr::Bitlshr(expr, val) => match val {
                CondConst::U64(n) => self.lshr(*n),
            }
            .do_build_from_condexpr(expr),
        }
    }
    /// Returns the built bit field.
    pub fn into_bitfield<T: TotallyComparable>(self, tag: T) -> BitField<T> {
        BitField::new(tag, self.mask)
    }
}

impl fmt::Display for BitFieldBuilder {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{{mask:{:#018x}, shift:{}}}", self.mask, self.shift)
    }
}

/// A set of bit fields.
#[derive(Clone, Debug)]
pub struct BitFieldSet(BTreeMap<CondExpr, u64>);

impl BitFieldSet {
    /// Returns a new empty bit field set.
    pub fn empty() -> BitFieldSet {
        BitFieldSet(BTreeMap::new())
    }
    /// Inserts the bit field.
    pub fn insert_bitfield(&mut self, bf: BitField<CondExpr>) {
        if let Some(mask) = self.0.get_mut(bf.tag()) {
            *mask |= bf.mask();
            return;
        }
        self.0.insert(bf.tag().clone(), bf.mask());
    }
    /// Inserts the bit field built from the expression.
    pub fn insert_condexpr(&mut self, expr: CondExpr) {
        if let Some(bf) = BitFieldBuilder::build_from_condexpr(&expr) {
            self.insert_bitfield(bf);
        }
    }
    /// Inserts the bit field built from the predicate.
    pub fn insert_condpred(&mut self, pred: CondPred) {
        match pred {
            CondPred::False | CondPred::True => {}
            CondPred::Eq(left, right) | CondPred::Neq(left, right) => {
                self.insert_condexpr(left);
                self.insert_condexpr(right);
            }
        }
    }
    /// Inserts the bit field built from the condition.
    pub fn insert_cond(&mut self, cond: Cond) {
        match cond {
            Cond::And(preds) => {
                for pred in preds {
                    self.insert_condpred(pred);
                }
            }
        }
    }
    /// Returns a condition of the equality on the bit fields.
    /// If `otherbaseid` is not larger enough, then returns `None`.
    pub fn gen_equation(&self, otherbaseid: usize) -> Option<Cond> {
        let mut cond = Cond::top();
        for (expr, mask) in self.0.iter() {
            let (id, var, othervar) = match expr {
                CondExpr::Var(var) => (
                    var.id(),
                    CondExpr::Var(CondVar::from(var.id())),
                    CondExpr::Var(CondVar::from(otherbaseid + var.id())),
                ),
                CondExpr::Deref(var) => (
                    var.id(),
                    CondExpr::Deref(CondVar::from(var.id())),
                    CondExpr::Deref(CondVar::from(otherbaseid + var.id())),
                ),
                expr => unreachable!("{}", expr),
            };
            if id >= otherbaseid {
                return None;
            }
            let left = CondExpr::Bitand(Box::new(var), CondConst::U64(*mask));
            let right = CondExpr::Bitand(Box::new(othervar), CondConst::U64(*mask));
            cond.conjunct(CondPred::Eq(left, right));
        }
        Some(cond)
    }
}

impl fmt::Display for BitFieldSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{{")?;
        for (i, (var, mask)) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} -> {:#018x}", var, mask)?;
        }
        write!(f, "}}")
    }
}

/// A constraint on bit fields.
#[derive(Clone, Debug, PartialEq)]
pub enum BitFieldConstr {
    /// `bv[$left] == $right`.
    EqU64(usize, u64),
    /// `bitwise_or($left) == bitwise_or($right)`.
    EqVar(Vec<usize>, Vec<usize>),
    /// `not and($constrs)`.
    NotAny(Vec<BitFieldConstr>),
}

impl BitFieldConstr {
    /// Inserts the set of the variable IDs into `varidset`.
    pub fn insert_varidset(&self, varidset: &mut BTreeSet<usize>) {
        match self {
            BitFieldConstr::EqU64(id, _) => {
                varidset.insert(*id);
            }
            BitFieldConstr::EqVar(left, right) => {
                for id in left {
                    varidset.insert(*id);
                }
                for id in right {
                    varidset.insert(*id);
                }
            }
            BitFieldConstr::NotAny(constrs) => {
                for constr in constrs {
                    constr.insert_varidset(varidset);
                }
            }
        }
    }
}

impl fmt::Display for BitFieldConstr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            BitFieldConstr::EqU64(var, val) => write!(f, "$bv{}=={:#x}", var, val),
            BitFieldConstr::EqVar(varset1, varset2) => {
                for (i, var) in varset1.iter().enumerate() {
                    if i > 0 {
                        write!(f, "|")?;
                    }
                    write!(f, "$bv{}", var)?;
                }
                write!(f, "==")?;
                for (i, var) in varset2.iter().enumerate() {
                    if i > 0 {
                        write!(f, "|")?;
                    }
                    write!(f, "$bv{}", var)?;
                }
                Ok(())
            }
            BitFieldConstr::NotAny(constrs) => {
                write!(f, "!({})", DisplayIter("", constrs.iter(), " && ", ""))
            }
        }
    }
}

/// A envrionment that is a partial map from the bit field IDs to the value.
#[derive(Clone, Debug)]
pub struct BitFieldEnv(Vec<Option<u64>>);

impl BitFieldEnv {
    /// Returns a new empty environment of the `len` bit fields.
    pub fn empty(len: usize) -> BitFieldEnv {
        BitFieldEnv(vec![None; len])
    }
    /// Returns an iterator on the values.
    pub fn iter(&self) -> impl Iterator<Item = &Option<u64>> {
        self.0.iter()
    }
    /// Returns the value of the `id`-th bit field.
    pub fn get(&self, id: usize) -> Option<u64> {
        if let Some(val) = self.0.get(id) {
            return *val;
        }
        None
    }
    /// Sets the value.
    pub fn set(&mut self, id: usize, val: Option<u64>) {
        self.0[id] = val;
    }
    /// Returns the valuation of the constraint.
    /// `None` means undefined.
    pub fn eval_constr(&self, constr: &BitFieldConstr) -> Option<bool> {
        match constr {
            BitFieldConstr::EqU64(var, val) => Some(self.get(*var)? == *val),
            BitFieldConstr::EqVar(vars1, vars2) => {
                let (mut val1, mut val2) = (0, 0);
                for var1 in vars1 {
                    val1 |= self.get(*var1)?;
                }
                for var2 in vars2 {
                    val2 |= self.get(*var2)?;
                }
                Some(val1 == val2)
            }
            BitFieldConstr::NotAny(constrs) => Some(!self.eval_constrs(constrs)?),
        }
    }
    /// Returns the valuation of the conjunction of the constraints.
    /// `None` means undefined.
    pub fn eval_constrs(&self, constrs: &[BitFieldConstr]) -> Option<bool> {
        for constr in constrs {
            match self.eval_constr(constr) {
                Some(true) => {}
                val => return val,
            }
        }
        Some(true)
    }
}

impl fmt::Display for BitFieldEnv {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{{")?;
        let mut first = true;
        for (var, val) in self.iter().enumerate() {
            if let Some(val) = val {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "$bf{}->{:#x}", var, val)?;
            }
        }
        write!(f, "}}")
    }
}

#[derive(Clone, Debug)]
struct BitFieldProjCtx<T: TotallyComparable> {
    constrs: Vec<BitFieldConstr>,
    remap: BTreeMap<BitField<T>, Vec<usize>>,
}

impl<T: TotallyComparable> BitFieldProjCtx<T> {
    fn new() -> BitFieldProjCtx<T> {
        BitFieldProjCtx {
            constrs: Vec::new(),
            remap: BTreeMap::new(),
        }
    }
    fn insert_remap(&mut self, bf: BitField<T>, sb: Vec<usize>) {
        if let Some(subbasis) = self.remap.get_mut(&bf) {
            for i in sb {
                if !subbasis.contains(&i) {
                    subbasis.push(i);
                }
            }
            return;
        }
        self.remap.insert(bf, sb);
    }
    fn into_constrs(self) -> Vec<BitFieldConstr> {
        self.constrs
    }
}

impl<T: TotallyComparable> Default for BitFieldProjCtx<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A basis of the space spanned by bit fields.
#[derive(Clone, Debug)]
pub struct BitFieldBasis<T: TotallyComparable>(Vec<BitField<T>>);

impl<T: TotallyComparable> BitFieldBasis<T> {
    /// Returns a new empty basis.
    pub fn empty() -> BitFieldBasis<T> {
        BitFieldBasis(Vec::new())
    }
    /// Returns the length.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Returns `true` if empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Returns the bit field by index.
    pub fn get(&self, id: usize) -> Option<&BitField<T>> {
        self.0.get(id)
    }
    /// Inserts the bit fields into the basis.
    pub fn insert(&mut self, mut bf: BitField<T>) {
        let mut difflist = Vec::new();
        for base in &mut self.0 {
            let a = bf.and(base);
            if !a.is_empty() {
                let b = base.diff(&bf);
                if !b.is_empty() {
                    difflist.push(b);
                }
                bf = bf.diff(base);
                *base = a;
            }
        }
        for base in difflist {
            self.0.push(base);
        }
        if !bf.is_empty() {
            self.0.push(bf);
        }
    }
}

impl BitFieldBasis<CondExpr> {
    /// Inserts the bit field built from the expression into the basis.
    pub fn insert_condexpr(&mut self, expr: &CondExpr) {
        if let Some(bf) = BitFieldBuilder::build_from_condexpr(expr) {
            self.insert(bf);
        }
    }
    /// Inserts the bit field built from the predicate into the basis.
    pub fn insert_condpred(&mut self, pred: &CondPred) {
        match pred {
            CondPred::False | CondPred::True => {}
            CondPred::Eq(left, right) | CondPred::Neq(left, right) => {
                self.insert_condexpr(left);
                self.insert_condexpr(right);
            }
        }
    }
    /// Inserts the bit field built from the condition into the basis.
    pub fn insert_cond(&mut self, cond: &Cond) {
        match cond {
            Cond::And(preds) => {
                for pred in preds {
                    self.insert_condpred(pred);
                }
            }
        }
    }
    fn project_bitfield(
        &self,
        bf: &BitField<CondExpr>,
        ctx: &BitFieldProjCtx<CondExpr>,
    ) -> Vec<usize> {
        let mut subbasis = Vec::new();
        for (base, basis) in ctx.remap.iter() {
            if !bf.and(base).is_empty() {
                subbasis.extend_from_slice(basis);
            }
        }
        for (idx, base) in self.0.iter().enumerate() {
            if !bf.and(base).is_empty() {
                subbasis.push(idx);
            }
        }
        subbasis
    }
    fn project_condexpr_pair_eqvar(
        &self,
        left: &CondExpr,
        lbuilder: BitFieldBuilder,
        right: &CondExpr,
        rbuilder: BitFieldBuilder,
        ctx: &mut BitFieldProjCtx<CondExpr>,
    ) -> Option<()> {
        match (left, lbuilder, right, rbuilder) {
            (var1 @ CondExpr::Var(_), v1builder, var2 @ CondExpr::Var(_), v2builder)
            | (var1 @ CondExpr::Deref(_), v1builder, var2 @ CondExpr::Deref(_), v2builder) => {
                let bf1 = v1builder.into_bitfield(var1.clone());
                let subbasis1 = self.project_bitfield(&bf1, ctx);
                let bf2 = v2builder.into_bitfield(var2.clone());
                let subbasis2 = self.project_bitfield(&bf2, ctx);
                let (bf, subbasis) = match (subbasis1.len(), subbasis2.len()) {
                    (l1, l2) if l1 > 0 && l2 > 0 => {
                        ctx.constrs
                            .push(BitFieldConstr::EqVar(subbasis1, subbasis2));
                        return Some(());
                    }
                    (l1, 0) if l1 > 0 => (bf2, subbasis1),
                    (0, l2) if l2 > 0 => (bf1, subbasis2),
                    (_, _) => return Some(()),
                };
                let mut mask = 0;
                for subbf in &subbasis {
                    mask |= self.get(*subbf).unwrap().mask();
                }
                ctx.insert_remap(bf.and_mask(mask), subbasis);
                Some(())
            }
            (CondExpr::Bitand(expr, maskexpr), vbuilder, other, obuilder)
            | (other, obuilder, CondExpr::Bitand(expr, maskexpr), vbuilder) => {
                let vbuilder = match maskexpr {
                    CondConst::U64(n) => vbuilder.and(*n),
                };
                self.project_condexpr_pair_eqvar(expr, vbuilder, other, obuilder, ctx)
            }
            (
                CondExpr::Bitlshr(v1expr, v1shiftexpr),
                v1builder,
                CondExpr::Bitlshr(v2expr, v2shiftexpr),
                v2builder,
            ) => {
                let v1builder = match v1shiftexpr {
                    CondConst::U64(n) => v1builder.lshr(*n),
                };
                let v2builder = match v2shiftexpr {
                    CondConst::U64(n) => v2builder.lshr(*n),
                };
                self.project_condexpr_pair_eqvar(v1expr, v1builder, v2expr, v2builder, ctx)
            }
            (CondExpr::Bitlshr(expr, shiftexpr), vbuilder, other, obuilder)
            | (other, obuilder, CondExpr::Bitlshr(expr, shiftexpr), vbuilder) => {
                let (vbuilder, obuilder) = match shiftexpr {
                    CondConst::U64(n) => (vbuilder.lshr(*n), obuilder.lshr(*n)),
                };
                self.project_condexpr_pair_eqvar(expr, vbuilder, other, obuilder, ctx)
            }
            _ => Some(()),
        }
    }
    fn project_condpred_eqvar(
        &self,
        pred: &CondPred,
        ctx: &mut BitFieldProjCtx<CondExpr>,
    ) -> Option<()> {
        match pred {
            CondPred::Eq(left, right) => self.project_condexpr_pair_eqvar(
                left,
                BitFieldBuilder::full(),
                right,
                BitFieldBuilder::full(),
                ctx,
            ),
            _ => Some(()),
        }
    }
    fn project_condexpr_pair(
        &self,
        negated: bool,
        left: &CondExpr,
        lbuilder: BitFieldBuilder,
        right: &CondExpr,
        rbuilder: BitFieldBuilder,
        ctx: &mut BitFieldProjCtx<CondExpr>,
    ) -> Option<()> {
        match (left, lbuilder, right, rbuilder) {
            (var @ CondExpr::Var(_), varbuilder, CondExpr::Const(val), valbuilder)
            | (CondExpr::Const(val), valbuilder, var @ CondExpr::Var(_), varbuilder)
            | (var @ CondExpr::Deref(_), varbuilder, CondExpr::Const(val), valbuilder)
            | (CondExpr::Const(val), valbuilder, var @ CondExpr::Deref(_), varbuilder) => {
                let val = match val {
                    CondConst::U64(n) => valbuilder.project_u64(*n),
                };
                let bf = varbuilder.into_bitfield(var.clone());
                let subbasis = self.project_bitfield(&bf, ctx);
                let mut constrs = Vec::with_capacity(subbasis.len());
                for bfidx in subbasis {
                    let bf = &self.0[bfidx];
                    let val = val & bf.mask();
                    constrs.push(BitFieldConstr::EqU64(bfidx, val));
                }
                match negated {
                    false => ctx.constrs.append(&mut constrs),
                    true => match constrs.is_empty() {
                        true => {}
                        false => ctx.constrs.push(BitFieldConstr::NotAny(constrs)),
                    },
                }
                Some(())
            }
            (CondExpr::Bitand(expr, maskexpr), vbuilder, other, obuilder)
            | (other, obuilder, CondExpr::Bitand(expr, maskexpr), vbuilder) => {
                let vbuilder = match maskexpr {
                    CondConst::U64(n) => vbuilder.and(*n),
                };
                self.project_condexpr_pair(negated, expr, vbuilder, other, obuilder, ctx)
            }
            (
                CondExpr::Bitlshr(v1expr, v1shiftexpr),
                v1builder,
                CondExpr::Bitlshr(v2expr, v2shiftexpr),
                v2builder,
            ) => {
                let v1builder = match v1shiftexpr {
                    CondConst::U64(n) => v1builder.lshr(*n),
                };
                let v2builder = match v2shiftexpr {
                    CondConst::U64(n) => v2builder.lshr(*n),
                };
                self.project_condexpr_pair(negated, v1expr, v1builder, v2expr, v2builder, ctx)
            }
            (CondExpr::Bitlshr(expr, shiftexpr), vbuilder, other, obuilder)
            | (other, obuilder, CondExpr::Bitlshr(expr, shiftexpr), vbuilder) => {
                let (vbuilder, obuilder) = match shiftexpr {
                    CondConst::U64(n) => (vbuilder.lshr(*n), obuilder.lshr(*n)),
                };
                self.project_condexpr_pair(negated, expr, vbuilder, other, obuilder, ctx)
            }
            _ => Some(()),
        }
    }
    fn project_condpred(&self, pred: &CondPred, ctx: &mut BitFieldProjCtx<CondExpr>) -> Option<()> {
        match pred {
            CondPred::False => None,
            CondPred::True => Some(()),
            CondPred::Eq(left, right) => self.project_condexpr_pair(
                false,
                left,
                BitFieldBuilder::full(),
                right,
                BitFieldBuilder::full(),
                ctx,
            ),
            CondPred::Neq(left, right) => self.project_condexpr_pair(
                true,
                left,
                BitFieldBuilder::full(),
                right,
                BitFieldBuilder::full(),
                ctx,
            ),
        }
    }
    fn project_cond(&self, cond: &Cond, ctx: &mut BitFieldProjCtx<CondExpr>) -> Option<()> {
        match cond {
            Cond::And(preds) => {
                for pred in preds {
                    self.project_condpred_eqvar(pred, ctx)?;
                }
                for pred in preds {
                    self.project_condpred(pred, ctx)?;
                }
                Some(())
            }
        }
    }
    /// Returns a constraint built from projection of the condition onto the basis.
    pub fn project_cond_into_constrs(&self, cond: &Cond) -> Option<Vec<BitFieldConstr>> {
        let mut ctx = BitFieldProjCtx::new();
        self.project_cond(cond, &mut ctx)?;
        Some(ctx.into_constrs())
    }
    /// Returns an iterator on the possible valuation of the condition on the basis.
    pub fn cond_iter<'a>(&'a self, cond: &Cond) -> Option<BitFieldBasisIter<'a, CondExpr>> {
        let constrs = self.project_cond_into_constrs(cond)?;
        Some(BitFieldBasisIter::new(self, constrs))
    }
}

impl<T: TotallyComparable> fmt::Display for BitFieldBasis<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", DisplayIter("<", self.0.iter(), ", ", ">"))
    }
}

#[derive(Clone, Debug)]
enum BitFieldBasisIterState {
    Start,
    Tick,
    End,
}

/// An iterator on the possible valuation on a basis.
#[derive(Clone, Debug)]
pub struct BitFieldBasisIter<'a, T: TotallyComparable> {
    basis: &'a BitFieldBasis<T>,
    constrs: Vec<BitFieldConstr>,
    eqset: UnionFind<usize>,
    env: BitFieldEnv,
    state: BitFieldBasisIterState,
    ranges: Vec<Option<(u64, u64)>>,
}

impl<'a, T: TotallyComparable> BitFieldBasisIter<'a, T> {
    fn new(basis: &'a BitFieldBasis<T>, constrs: Vec<BitFieldConstr>) -> BitFieldBasisIter<'a, T> {
        let mut eqset = UnionFind::empty();
        for constr in constrs.iter() {
            match constr {
                BitFieldConstr::EqVar(vars1, vars2) if vars1.len() == 1 && vars2.len() == 1 => {
                    eqset.union(&vars1[0], &vars2[0]);
                }
                _ => {}
            }
        }
        BitFieldBasisIter {
            basis,
            constrs,
            eqset,
            env: BitFieldEnv::empty(basis.len()),
            state: BitFieldBasisIterState::Start,
            ranges: Vec::with_capacity(basis.len()),
        }
    }
    /// Returns the current environment (valuation).
    pub fn env(&self) -> &BitFieldEnv {
        &self.env
    }
}

impl<'a, T: TotallyComparable> Iterator for BitFieldBasisIter<'a, T> {
    type Item = ();
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.state {
            BitFieldBasisIterState::Start => {
                let mut targetset = BTreeSet::new();
                for constr in &self.constrs {
                    constr.insert_varidset(&mut targetset);
                }
                for target in 0..self.basis.len() {
                    if !targetset.contains(&target) {
                        self.ranges.push(None);
                        continue;
                    }
                    let mut lower = 0x0u64;
                    let mut upper = self.basis.get(target).unwrap().mask();
                    for constr in &self.constrs {
                        match constr {
                            BitFieldConstr::EqU64(var, n) if *var == target => {
                                if lower <= *n && *n <= upper {
                                    lower = *n;
                                    upper = *n;
                                } else {
                                    self.state = BitFieldBasisIterState::End;
                                    return self.next();
                                }
                            }
                            _ => {}
                        }
                    }
                    self.ranges.push(Some((lower, upper)));
                    self.env.set(target, Some(lower));
                }
                self.state = BitFieldBasisIterState::Tick;
                if self.env.eval_constrs(&self.constrs) == Some(true) {
                    return Some(());
                }
                self.next()
            }
            BitFieldBasisIterState::Tick => loop {
                let mut ticked = false;
                for i in 0..self.basis.len() {
                    if let Some((loweri, upperi)) = self.ranges[i] {
                        let maski = self.basis.get(i).unwrap().mask();
                        let vali = self.env.get(i).unwrap();
                        let (vali, will_tick) = match self.eqset.find(&i) {
                            Some(j) if *j != i => continue,
                            _ => (vali, false),
                        };
                        if !(loweri <= vali && vali < upperi) {
                            self.env.set(i, Some(loweri));
                            continue;
                        }
                        let vali = match will_tick {
                            true => vali,
                            false => (vali | !maski).wrapping_add(1) & maski,
                        };
                        self.env.set(i, Some(vali));
                        ticked = true;
                        break;
                    }
                }
                if !ticked {
                    self.state = BitFieldBasisIterState::End;
                    return self.next();
                }
                for (s, t) in self.eqset.iter() {
                    self.env.set(*s, Some(self.env.get(*t).unwrap()));
                }
                if self.env.eval_constrs(&self.constrs) == Some(true) {
                    return Some(());
                }
            },
            BitFieldBasisIterState::End => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::sexpr::SExpr;
    #[test]
    fn bitfield() {
        assert_eq!("x&0xff", BitField::new("x", 0xff).to_string());
        assert_eq!(false, BitField::new("x", 0xff).is_empty());
        assert_eq!(true, BitField::new("x", 0x00).is_empty());
        assert_eq!(
            true,
            BitField::new("x", 0x0f).is_less(&BitField::new("x", 0xff))
        );
        assert_eq!(
            false,
            BitField::new("x", 0xff).is_less(&BitField::new("x", 0x0f))
        );
        assert_eq!(
            false,
            BitField::new("x", 0xff).is_less(&BitField::new("y", 0xff))
        );
        assert_eq!(
            BitField::new("x", 0x0f),
            BitField::new("x", 0xff).and(&BitField::new("x", 0x0f))
        );
        assert_eq!(
            BitField::new("x", 0x00),
            BitField::new("x", 0xff).and(&BitField::new("y", 0x0f))
        );
        assert_eq!(
            BitField::new("x", 0xf0),
            BitField::new("x", 0xff).diff(&BitField::new("x", 0x0f))
        );
        assert_eq!(
            BitField::new("x", 0xff),
            BitField::new("x", 0xff).diff(&BitField::new("y", 0x0f))
        );
    }
    #[test]
    fn bitfield_builder() {
        let expected_input_list = vec![
            // $0 == A => A maps to A
            (
                "{mask:0xffffffffffffffff, shift:0}",
                0xffffffffffffffff,
                "$&0xffffffffffffffff",
                BitFieldBuilder::full(),
            ),
            // $0 & 0xff == A => A maps to A&0xff
            (
                "{mask:0x00000000000000ff, shift:0}",
                0x00000000000000ff,
                "$&0xff",
                BitFieldBuilder::full().and(0xff),
            ),
            // $0 << 47 == A => A maps to (A<<47)&MASK
            (
                "{mask:0xffff800000000000, shift:47}",
                0xffff800000000000,
                "$&0xffff800000000000",
                BitFieldBuilder::full().lshr(47),
            ),
            (
                "{mask:0xf000000000000000, shift:47}",
                0xf000000000000000,
                "$&0xf000000000000000",
                BitFieldBuilder::full().lshr(47).and(0xf << 60),
            ),
            (
                "{mask:0x8000000000000000, shift:47}",
                0x8000000000000000,
                "$&0x8000000000000000",
                BitFieldBuilder::full().and(0x10000).lshr(47),
            ),
            (
                "{mask:0x000000000001ffff, shift:-47}",
                0x000000000001ffff,
                "$&0x1ffff",
                BitFieldBuilder::full().lshl(47),
            ),
            (
                "{mask:0x000000000001e000, shift:-47}",
                0x000000000001e000,
                "$&0x1e000",
                BitFieldBuilder::full().lshl(47).and(0x000000000001e000),
            ),
            (
                "{mask:0x0000000000010000, shift:-47}",
                0x0000000000010000,
                "$&0x10000",
                BitFieldBuilder::full().and(0x8000 << 48).lshl(47),
            ),
        ];
        for (expected, expected_proj, expected_bf, builder) in expected_input_list {
            assert_eq!(expected, builder.to_string());
            assert_eq!(expected_proj, builder.project_u64(!0), "{}", builder);
            assert_eq!(
                expected_bf,
                builder.into_bitfield("$").to_string(),
                "{}",
                builder
            );
        }
    }
    #[test]
    fn bitfield_constr() {
        assert_eq!("$bv0==0xff", BitFieldConstr::EqU64(0, 0xff).to_string());
        assert_eq!(
            "$bv0|$bv1==$bv2|$bv3",
            BitFieldConstr::EqVar(vec![0, 1], vec![2, 3]).to_string()
        );
        assert_eq!(
            "!($bv0==0xff && $bv0==$bv1)",
            BitFieldConstr::NotAny(vec![
                BitFieldConstr::EqU64(0, 0xff),
                BitFieldConstr::EqVar(vec![0], vec![1]),
            ])
            .to_string()
        );
    }
    #[test]
    fn bitfield_insert() {
        let mut bfset = BitFieldSet::empty();
        let input_list = vec![
            "false",
            "true",
            "(== (bitand $0 0xff) 0x00)",
            "(!= (bitlshr $0 47) 0x00000)",
            "(!= 0x00 (bitand (bitlshr (deref $1) 47) 0xff))",
        ];
        for input in input_list {
            let sexpr = SExpr::parse(input);
            let cond = Cond::try_parse(&sexpr).expect(&format!("{}", input));
            bfset.insert_cond(cond);
        }
        assert_eq!(
            "{$0 -> 0xffff8000000000ff, deref($1) -> 0x007f800000000000}",
            bfset.to_string()
        );
        let eqcond = bfset.gen_equation(10).unwrap();
        assert_eq!("and(eq(bitand($0, 0xffff8000000000ff), bitand($10, 0xffff8000000000ff)), eq(bitand(deref($1), 0x7f800000000000), bitand(deref($11), 0x7f800000000000)))", eqcond.to_string());
    }
    #[test]
    fn bitfield_env_eval() {
        let expected_input_list = vec![
            (Some(true), BitFieldConstr::EqU64(0, 0xff)),
            (Some(false), BitFieldConstr::EqU64(0, 0xf0)),
            (None, BitFieldConstr::EqU64(10, 0xf0)),
            (Some(true), BitFieldConstr::EqVar(vec![0], vec![1])),
            (Some(false), BitFieldConstr::EqVar(vec![0], vec![2])),
            (Some(true), BitFieldConstr::EqVar(vec![0, 3], vec![1, 3])),
            (None, BitFieldConstr::EqVar(vec![10], vec![0])),
            (None, BitFieldConstr::EqVar(vec![0], vec![10])),
            (
                Some(false),
                BitFieldConstr::NotAny(vec![
                    BitFieldConstr::EqU64(0, 0xff),
                    BitFieldConstr::EqVar(vec![0], vec![1]),
                ]),
            ),
            (
                Some(true),
                BitFieldConstr::NotAny(vec![
                    BitFieldConstr::EqU64(0, 0xff),
                    BitFieldConstr::EqVar(vec![0], vec![2]),
                ]),
            ),
            (
                None,
                BitFieldConstr::NotAny(vec![
                    BitFieldConstr::EqU64(0, 0xff),
                    BitFieldConstr::EqVar(vec![0], vec![10]),
                ]),
            ),
        ];
        let mut env = BitFieldEnv::empty(4);
        env.set(0, Some(0x00ff));
        env.set(1, Some(0x00ff));
        env.set(2, Some(0x0000));
        env.set(3, Some(0xf000));
        for (expected, input) in expected_input_list {
            assert_eq!(expected, env.eval_constr(&input), "{}", input);
        }
    }
    #[test]
    fn bitfield_basis_insert() {
        let expected_input_list = vec![
            (
                "<x&0xff, y&0xff>",
                vec![BitField::new("x", 0x0ff), BitField::new("y", 0x0ff)],
            ),
            (
                "<x&0xf0, x&0xf, x&0xf00>",
                vec![BitField::new("x", 0x0ff), BitField::new("x", 0xff0)],
            ),
        ];
        for (expected, input) in expected_input_list {
            let mut basis = BitFieldBasis::empty();
            for e in &input {
                basis.insert(e.clone());
            }
            assert_eq!(
                expected,
                basis.to_string(),
                "{}",
                DisplayIter("[", input.iter(), ", ", "]")
            );
        }
    }
    #[test]
    fn bitfield_basis_insert_cond() {
        let expected_input_list = vec![
            ("<>", "false"),
            ("<>", "true"),
            ("<$0&0xffffffffffffffff>", "(== $0 0x12)"),
            ("<deref($0)&0xffffffffffffffff>", "(!= (deref $0) 0x12)"),
            (
                "<$0&0xf0, $0&0xf, $0&0xf00>",
                "(and (== (bitand $0 0xff) 0x12) (== (bitand $0 0xff0) 0x340))",
            ),
            ("<$0&0xffff800000000000>", "(== (bitlshr $0 47) 0x12)"),
            // Regression 2021/4/1
            ("<$0&0xf0>", "(== (bitlshr (bitand $0 0xf0) 4) 1)"),
            ("<$0&0xf0>", "(== (bitand (bitlshr $0 4) 0x0f) 1)"),
        ];
        for (expected, input) in expected_input_list {
            let mut basis = BitFieldBasis::empty();
            let cond = Cond::try_parse(&SExpr::parse(&input)).expect(&format!("{}", input));
            basis.insert_cond(&cond);
            assert_eq!(expected, basis.to_string(), "{}", input);
        }
    }
    #[test]
    fn bitfield_basis_project_cond_into_constrs() {
        let expected_input_list = vec![
            ("None", "false"),
            ("Some([])", "true"),
            ("Some([$bv0==0x10, $bv1==0x2, $bv2==0x0])", "(== $0 0x12)"),
            (
                "Some([$bv3==0x10, $bv4==0x2, $bv5==0x0])",
                "(== (deref $0) 0x12)",
            ),
            (
                "Some([!($bv0==0x10 && $bv1==0x2 && $bv2==0x0)])",
                "(!= 0x12 $0)",
            ),
            (
                "Some([])",
                "(!= 0x12 $2)",
            ),
            (
                "Some([$bv0==0x10, $bv1==0x2])",
                "(== (bitand $0 0xff) 0x12)",
            ),
            (
                "Some([!($bv0==0x10 && $bv1==0x2)])",
                "(!= 0x12 (bitand $0 0xff))",
            ),
            ("Some([$bv1==0x2])", "(== (bitand $0 0x0f) 0x12)"),
            ("Some([$bv0==0x20, $bv2==0x100])", "(== (bitlshr $0 4) 0x12)"),
            (
                "Some([$bv6==$bv0|$bv1, $bv6==0x12])",
                "(and (== (bitand $1 0xff) 0x12) (== (bitand $0 0xff) (bitand $1 0xff)))",
            ),
            /* TODO: FIXME
            (
                "Some([$bv6==$bv0|$bv1, $bv6==0x12])",
                "(and (== (bitand $1 0xff) 0x12) (== $0 $1))",
            ),
            */
            ("Some([])", "(and (== $9 0x12) (== $8 $9))"),
            (
                "Some([$bv0==0x10, $bv1==0x2])",
                "(and (== (bitand $9 0xff) 0x12) (== (bitand $9 0xff) (bitand $0 0xff)))",
            ),
            (
                "Some([$bv0|$bv1==$bv6, $bv0==0x10, $bv1==0x2])",
                "(and (== (bitand $9 0xff) 0x12) (== (bitand $0 0xff) (bitand $9 0xff)) (== $1 (bitand $9 0xff)))",
            ),
            (
                "Some([$bv0|$bv2==$bv6, $bv6==0x120])",
                "(and (== (bitlshr $1 4) 0x12) (== (bitlshr $0 4) (bitlshr $1 4)))",
            ),
            // Regression 2021/3/26
            (
                "Some([$bv0==0x10])",
                "(== (bitand (bitlshr $0 4) 0x0f) 0x1)",
            ),
        ];
        for (expected, input) in expected_input_list {
            let mut basis = BitFieldBasis::empty();
            let basis_input =
                "(and (== (bitand $0 0xff) 0x12) (== (bitand $0 0xff0) 0x340) (== (bitand (deref $0) 0xff) 0x12) (== (bitand (deref $0) 0xff0) 0x340) (== $1 0x0))";
            let basis_cond = Cond::try_parse(&SExpr::parse(&basis_input)).unwrap();
            basis.insert_cond(&basis_cond);
            let cond = Cond::try_parse(&SExpr::parse(&input)).expect(&format!("{}", input));
            let result = match basis.project_cond_into_constrs(&cond) {
                Some(constrs) => format!("Some({})", DisplayIter("[", constrs.iter(), ", ", "]")),
                None => format!("None"),
            };
            assert_eq!(expected, result, "{}", input);
        }
    }
    #[test]
    fn bitfield_basis_iterate_cond() {
        let expected_input_list = vec![
            ("Some([{$bf0->0x10, $bf1->0x2, $bf2->0x0, $bf3->0x0}])", "(== $0 0x12)"),
            ("Some([])", "(and (== $0 0x12) (== $0 0x13))"),
            (
                "Some([{$bf0->0x10, $bf1->0x2, $bf2->0x0, $bf3->0x0}])",
                "(and (== $0 0x12) (!= $0 0x13))",
            ),
            ("Some([])", "(and (== $0 0x12) (!= $0 0x12))"),
            ("Some([{$bf1->0x0}, {$bf1->0x1}, {$bf1->0x3}, {$bf1->0x4}, {$bf1->0x5}, {$bf1->0x6}, {$bf1->0x7}, {$bf1->0x8}, {$bf1->0x9}, {$bf1->0xa}, {$bf1->0xb}, {$bf1->0xc}, {$bf1->0xd}, {$bf1->0xe}, {$bf1->0xf}])", "(!= (bitand $0 0x0f) 0x02)"),
            ("Some([{$bf0->0x0, $bf3->0x0}, {$bf0->0x10, $bf3->0x0}, {$bf0->0x30, $bf3->0x0}, {$bf0->0x40, $bf3->0x0}, {$bf0->0x50, $bf3->0x0}, {$bf0->0x60, $bf3->0x0}, {$bf0->0x70, $bf3->0x0}, {$bf0->0x80, $bf3->0x0}, {$bf0->0x90, $bf3->0x0}, {$bf0->0xa0, $bf3->0x0}, {$bf0->0xb0, $bf3->0x0}, {$bf0->0xc0, $bf3->0x0}, {$bf0->0xd0, $bf3->0x0}, {$bf0->0xe0, $bf3->0x0}, {$bf0->0xf0, $bf3->0x0}, {$bf0->0x0, $bf3->0x1000}, {$bf0->0x10, $bf3->0x1000}, {$bf0->0x20, $bf3->0x1000}, {$bf0->0x30, $bf3->0x1000}, {$bf0->0x40, $bf3->0x1000}, {$bf0->0x50, $bf3->0x1000}, {$bf0->0x60, $bf3->0x1000}, {$bf0->0x70, $bf3->0x1000}, {$bf0->0x80, $bf3->0x1000}, {$bf0->0x90, $bf3->0x1000}, {$bf0->0xa0, $bf3->0x1000}, {$bf0->0xb0, $bf3->0x1000}, {$bf0->0xc0, $bf3->0x1000}, {$bf0->0xd0, $bf3->0x1000}, {$bf0->0xe0, $bf3->0x1000}, {$bf0->0xf0, $bf3->0x1000}])", "(!= (bitand $0 0x10f0) 0x0020)"),
        ];
        for (expected, input) in expected_input_list {
            let mut basis = BitFieldBasis::empty();
            let basis_input =
                "(and (== (bitand $0 0xff) 0x12) (== (bitand $0 0xff0) 0x340) (== (bitand $0 0x1000) 0x1000) (== $1 0x0))";
            let basis_cond = Cond::try_parse(&SExpr::parse(&basis_input)).unwrap();
            basis.insert_cond(&basis_cond);
            let cond = Cond::try_parse(&SExpr::parse(&input)).expect(&format!("{}", input));
            let result = match basis.cond_iter(&cond) {
                Some(mut iter) => {
                    let mut result = String::from("Some([");
                    let mut first = true;
                    while iter.next().is_some() {
                        if !first {
                            result += ", ";
                        }
                        first = false;
                        result += &format!("{}", iter.env());
                    }
                    result + "])"
                }
                None => format!("None"),
            };
            assert_eq!(expected, result, "{}", input);
        }
    }
}
