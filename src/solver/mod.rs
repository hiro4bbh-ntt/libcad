//! The Model-Splitting Satisfiability Solver (MSSS).

pub mod bitfield;
pub mod syntax;
pub mod union_find;

use bitfield::BitFieldBasis;
use syntax::Cond;

/// A solver.
#[derive(Clone, Debug)]
pub struct Solver();

impl Solver {
    /// Returns a new solver.
    pub fn new() -> Solver {
        Solver()
    }
    /// Returns `true` if the left entails the right.
    pub fn entails_cond(&self, left: &Cond, right: &Cond) -> bool {
        let mut basis = BitFieldBasis::empty();
        basis.insert_cond(right);
        let mut left_iter = match basis.cond_iter(left) {
            Some(iter) => iter,
            // |- false -> P
            None => return true,
        };
        let right_constrs = match basis.project_cond_into_constrs(right) {
            Some(constrs) => constrs,
            // |- P -> false
            None => return left_iter.next().is_none(),
        };
        while left_iter.next().is_some() {
            if left_iter.env().eval_constrs(&right_constrs) != Some(true) {
                return false;
            }
        }
        true
    }
    /// Returns `true` if the condition is not semantically equal to `false`.
    pub fn satisfies_cond(&self, cond: &Cond) -> bool {
        let mut basis = BitFieldBasis::empty();
        basis.insert_cond(cond);
        match basis.cond_iter(cond) {
            Some(mut iter) => iter.next().is_some(),
            // C is `false`.
            None => false,
        }
    }
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::sexpr::SExpr;
    #[test]
    fn entails_cond() {
        let expected_input_list = vec![
            (false, ("(and)", "(== $0 0x01)")),
            (true, ("(and)", "(and)")),
            (true, ("(and (== $0 0x01))", "(== $0 0x01)")),
            (false, ("(and (== $0 0x01))", "(== $0 0x02)")),
            // NOTICE: LHS is equivalent to false.
            (true, ("(and (== $0 0x01) (== $0 0x02))", "(== $0 0x01)")),
            (true, ("(and false)", "(== $0 0x01)")),
            (false, ("(and (== $0 0x01))", "false")),
            (true, ("(and false)", "false")),
            (true, ("(and (== $0 0x81))", "(== (bitand $0 0x0f) 0x01)")),
            (false, ("(and (== $0 0x82))", "(== (bitand $0 0x0f) 0x01)")),
            (
                false,
                (
                    "(and (== (bitand $0 0xf0) 0x80))",
                    "(== (bitand $0 0x0f) 0x01)",
                ),
            ),
            (
                false,
                (
                    "(and (== $0 0x05) (!= $1 0x0c))",
                    "(== (bitand $0 0x0f) 0x01)",
                ),
            ),
            (
                true,
                (
                    "(and (== (bitand $1 0xff) 0x01) (== (bitand $0 0xff) (bitand $1 0xff)))",
                    "(and (== (bitand $0 0xff) 0x01) (== (bitand $1 0xff) 0x01))",
                ),
            ),
            (
                true,
                (
                    "(and (== (bitand $1 0xff) 0x01) (== (bitand $0 0xff) (bitand $1 0xff)))",
                    "(== (bitand $0 0xff) 0x01)",
                ),
            ),
            (
                true,
                (
                    "(and (== (bitand $1 0xff) 0x01) (== $0 $1))",
                    "(== (bitand $0 0xff) 0x01)",
                ),
            ),
            (
                true,
                (
                    "(and (== (bitand $1 0xff) 0x01) (== $0 $1))",
                    "(== (bitand $0 0x0f) 0x01)",
                ),
            ),
            (
                false,
                (
                    "(and (== (bitand $1 0xff) 0x02) (== (bitand $0 0xff) (bitand $1 0xff)))",
                    "(== (bitand $0 0xff) 0x01)",
                ),
            ),
            // Regression 2021/3/26
            (false, ("(and)", "(== (bitand (bitlshr $0 4) 0x0f) 0x1)")),
            (
                false,
                (
                    "(== (bitand (bitlshr $0 4) 0x0f) 0x2)",
                    "(== (bitand (bitlshr $0 4) 0x0f) 0x1)",
                ),
            ),
        ];
        for (expected, input) in expected_input_list {
            let solver = Solver::new();
            let (left, right) = (SExpr::parse(&input.0), SExpr::parse(&input.1));
            let left = Cond::try_parse(&left).expect(&format!("{}", left));
            let right = Cond::try_parse(&right).expect(&format!("{}", right));
            let result = solver.entails_cond(&left, &right);
            assert_eq!(expected, result, "{} -> {}", input.0, input.1);
        }
    }
    #[test]
    fn satisfies_cond() {
        let expected_input_list = vec![
            (false, "false"),
            (true, "(and)"),
            (false, "(and (== $0 1) (== $0 2))"),
            (
                false,
                "(and (== (bitlshr (bitand $0 0xf0) 4) 1) (== (bitand (bitlshr $0 4) 0x0f) 2))",
            ),
        ];
        for (expected, input) in expected_input_list {
            let solver = Solver::new();
            let cond = SExpr::parse(&input);
            let cond = Cond::try_parse(&cond).expect(&format!("{}", cond));
            let result = solver.satisfies_cond(&cond);
            assert_eq!(expected, result, "{}", input);
        }
    }
}
