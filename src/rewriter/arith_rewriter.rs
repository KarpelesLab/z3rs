//! Arithmetic constant folding — a subset of `arith_rewriter`
//! (`z3/src/ast/rewriter/arith_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! `try_fold` evaluates an arithmetic application whose arguments are all
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

    let is_int = m.is_int_sort(m.get_sort(args[0]));

    // Collect like terms in a sum even when some operands are symbolic, so
    // cancelling / combining terms happens (e.g. x + (-x) + 3 → 3, 2x + 3x → 5x).
    if kind == ArithOp::Add as DeclKind && args.iter().any(|&a| m.as_numeral(a).is_none()) {
        return collect_sum(m, args, is_int);
    }

    // All remaining folds require every operand to be a numeral.
    let mut nums: Vec<Rational> = Vec::with_capacity(args.len());
    for &a in args {
        nums.push(m.as_numeral(a)?);
    }

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

/// Decompose an addend into `(base term, coefficient)`; `base == None` for a
/// pure numeral. Recognizes `(- t)` and `(* c t)` / `(* t c)` with a numeral
/// factor so their coefficients combine.
fn addend(m: &AstManager, a: AstId) -> (Option<AstId>, Rational) {
    if let Some(n) = m.as_numeral(a) {
        return (None, n);
    }
    if let Some(app) = m.app(a) {
        let kind = m
            .func_decl(app.decl)
            .map(|d| (d.info.family_id, d.info.decl_kind));
        let afid = m.get_family_id(Symbol::new("arith"));
        if let (Some(fid), Some(afid)) = (kind, afid)
            && fid.0 == afid
        {
            if fid.1 == ArithOp::Uminus as DeclKind && app.args.len() == 1 {
                let (b, c) = addend(m, app.args[0]);
                return (b, -&c);
            }
            if fid.1 == ArithOp::Mul as DeclKind && app.args.len() == 2 {
                if let Some(c) = m.as_numeral(app.args[0]) {
                    return (Some(app.args[1]), c);
                }
                if let Some(c) = m.as_numeral(app.args[1]) {
                    return (Some(app.args[0]), c);
                }
            }
        }
    }
    (Some(a), Rational::from_integer(puremp::Int::from(1)))
}

/// Rebuild a sum after collecting like terms; `None` if nothing changed.
fn collect_sum(m: &mut AstManager, args: &[AstId], is_int: bool) -> Option<AstId> {
    let mut coeffs: Vec<(AstId, Rational)> = Vec::new();
    let mut constant = Rational::from_integer(puremp::Int::from(0));
    for &a in args {
        let (base, c) = addend(m, a);
        match base {
            None => constant = &constant + &c,
            Some(t) => {
                if let Some(e) = coeffs.iter_mut().find(|(u, _)| *u == t) {
                    e.1 = &e.1 + &c;
                } else {
                    coeffs.push((t, c));
                }
            }
        }
    }
    let zero = Rational::from_integer(puremp::Int::from(0));
    let one = Rational::from_integer(puremp::Int::from(1));
    let mut parts: Vec<AstId> = Vec::new();
    for (t, c) in &coeffs {
        if *c == zero {
            continue; // cancelled
        } else if *c == one {
            parts.push(*t);
        } else {
            let k = m.mk_numeral(c.clone(), is_int);
            parts.push(m.mk_mul(&[k, *t]));
        }
    }
    if constant != zero || parts.is_empty() {
        parts.push(m.mk_numeral(constant, is_int));
    }
    Some(if parts.len() == 1 {
        parts[0]
    } else {
        m.mk_add(&parts)
    })
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
    fn collects_like_terms_in_sums() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        // x + (-x) + 3 = 3
        let neg_x = m.mk_uminus(x);
        let sum = m.mk_add(&[x, neg_x, three]);
        assert_eq!(simplify(&mut m, sum), three);
        // 2x + 3x = 5x
        let two = m.mk_int(2);
        let three2 = m.mk_int(3);
        let t1 = m.mk_mul(&[two, x]);
        let t2 = m.mk_mul(&[three2, x]);
        let sum2 = m.mk_add(&[t1, t2]);
        let five = m.mk_int(5);
        let expect = m.mk_mul(&[five, x]);
        assert_eq!(simplify(&mut m, sum2), expect);
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
