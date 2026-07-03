//! Arithmetic constant folding — a subset of `arith_rewriter`
//! (`z3/src/ast/rewriter/arith_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! [`try_fold`] evaluates an arithmetic application whose arguments are all
//! numerals: `+`, `*`, `-` (n-ary and unary), and the `<=`/`<`/`>=`/`>`
//! comparisons, using `puremp`'s exact rational arithmetic. Non-constant
//! applications are left to the driver to rebuild.

use alloc::vec::Vec;

use puremp::Rational;

use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::ast::{AstId, DeclKind};
use crate::util::symbol::Symbol;

/// Try to fold an arithmetic application `decl(args)` with all-numeral operands.
/// Returns `None` if `decl` is not arithmetic, an operand is not a numeral, or
/// the op is not one this rewriter evaluates.
pub(crate) fn try_fold(m: &mut AstManager, decl: AstId, args: &[AstId]) -> Option<AstId> {
    let afid = m.get_family_id(Symbol::new("arith"))?;
    let d = m.func_decl(decl).expect("app decl");
    if d.info.family_id != afid {
        return None;
    }
    let kind = d.info.decl_kind;
    // Nullary arith apps (numerals, pi, e, …) have nothing to fold.
    if args.is_empty() {
        return None;
    }

    // All operands must be numerals to fold.
    let mut nums: Vec<Rational> = Vec::with_capacity(args.len());
    for &a in args {
        nums.push(m.as_numeral(a)?);
    }
    let is_int = m.is_int_sort(m.get_sort(args[0]));

    if kind == ArithOp::Add as DeclKind {
        let mut acc = nums[0].clone();
        for n in &nums[1..] {
            acc = &acc + n;
        }
        Some(m.mk_numeral(acc, is_int))
    } else if kind == ArithOp::Mul as DeclKind {
        let mut acc = nums[0].clone();
        for n in &nums[1..] {
            acc = &acc * n;
        }
        Some(m.mk_numeral(acc, is_int))
    } else if kind == ArithOp::Sub as DeclKind {
        let mut acc = nums[0].clone();
        for n in &nums[1..] {
            acc = &acc - n;
        }
        Some(m.mk_numeral(acc, is_int))
    } else if kind == ArithOp::Uminus as DeclKind {
        Some(m.mk_numeral(-&nums[0], is_int))
    } else if kind == ArithOp::Le as DeclKind {
        Some(bool_of(m, nums[0] <= nums[1]))
    } else if kind == ArithOp::Lt as DeclKind {
        Some(bool_of(m, nums[0] < nums[1]))
    } else if kind == ArithOp::Ge as DeclKind {
        Some(bool_of(m, nums[0] >= nums[1]))
    } else if kind == ArithOp::Gt as DeclKind {
        Some(bool_of(m, nums[0] > nums[1]))
    } else {
        None
    }
}

fn bool_of(m: &mut AstManager, b: bool) -> AstId {
    if b { m.mk_true() } else { m.mk_false() }
}

#[cfg(test)]
mod tests {
    use crate::ast::manager::AstManager;
    use crate::rewriter::simplify;

    #[test]
    fn folds_arithmetic_constants() {
        let mut m = AstManager::new();
        // (+ (* 2 3) 1) = 7
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        let one = m.mk_int(1);
        let prod = m.mk_mul(&[two, three]);
        let sum = m.mk_add(&[prod, one]);
        let seven = m.mk_int(7);
        assert_eq!(simplify(&mut m, sum), seven);
    }

    #[test]
    fn folds_comparisons_to_booleans() {
        let mut m = AstManager::new();
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        let le = m.mk_le(two, three);
        let gt = m.mk_gt(two, three);
        assert_eq!(simplify(&mut m, le), m.mk_true());
        assert_eq!(simplify(&mut m, gt), m.mk_false());
    }

    #[test]
    fn leaves_symbolic_arithmetic_alone() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let one = m.mk_int(1);
        // (+ x 1) has a non-numeral operand; unchanged.
        let sum = m.mk_add(&[x, one]);
        assert_eq!(simplify(&mut m, sum), sum);
    }

    #[test]
    fn folds_inside_a_larger_term() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        // (<= x (+ 2 3)) simplifies the numeral sum to (<= x 5)
        let five = m.mk_int(5);
        let sum = m.mk_add(&[two, three]);
        let le = m.mk_le(x, sum);
        let expected = m.mk_le(x, five);
        assert_eq!(simplify(&mut m, le), expected);
    }
}
