//! Negation normal form — a core of `nnf` (`z3/src/ast/normal_forms/nnf.{h,cpp}`,
//! Z3 4.17.0, MIT).
//!
//! [`to_nnf`] rewrites a boolean formula so that negation appears only on atoms,
//! using De Morgan's laws, double-negation elimination, and the implication
//! expansion `a => b ≡ ¬a ∨ b`. `ite`, `xor`, and `=` are treated as atoms here
//! (Z3 additionally expands these); that refinement comes later.

use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::BasicOp;
use crate::ast::manager::AstManager;
use crate::ast::{BASIC_FAMILY_ID, DeclKind};

/// Convert `e` to negation normal form.
pub fn to_nnf(m: &mut AstManager, e: AstId) -> AstId {
    nnf(m, e, false)
}

/// Rewrite `e` (optionally negated) into NNF.
fn nnf(m: &mut AstManager, e: AstId, negate: bool) -> AstId {
    if m.is_and(e) {
        let children = nnf_children(m, e, negate);
        // ¬(a ∧ b) = ¬a ∨ ¬b
        if negate {
            m.mk_or(&children)
        } else {
            m.mk_and(&children)
        }
    } else if m.is_or(e) {
        let children = nnf_children(m, e, negate);
        if negate {
            m.mk_and(&children)
        } else {
            m.mk_or(&children)
        }
    } else if m.is_not(e) {
        let a = m.app_args(e)[0];
        nnf(m, a, !negate) // ¬¬x collapses via the flip
    } else if is_implies(m, e) {
        let args = m.app_args(e).to_vec();
        let (a, b) = (args[0], args[1]);
        if negate {
            // ¬(a → b) = a ∧ ¬b
            let na = nnf(m, a, false);
            let nb = nnf(m, b, true);
            m.mk_and(&[na, nb])
        } else {
            // a → b = ¬a ∨ b
            let na = nnf(m, a, true);
            let nb = nnf(m, b, false);
            m.mk_or(&[na, nb])
        }
    } else if m.is_true(e) {
        if negate { m.mk_false() } else { e }
    } else if m.is_false(e) {
        if negate { m.mk_true() } else { e }
    } else {
        // Atom (incl. ite/xor/eq/uninterpreted): negate at the leaf.
        if negate { m.mk_not(e) } else { e }
    }
}

/// NNF each argument of the and/or `e`, propagating `negate`.
fn nnf_children(m: &mut AstManager, e: AstId, negate: bool) -> Vec<AstId> {
    let args = m.app_args(e).to_vec();
    args.into_iter().map(|a| nnf(m, a, negate)).collect()
}

fn is_implies(m: &AstManager, e: AstId) -> bool {
    m.is_app_of(e, BASIC_FAMILY_ID, BasicOp::Implies as DeclKind)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn de_morgan_on_and_or() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        // ¬(p ∧ q) = ¬p ∨ ¬q
        let and = m.mk_and(&[p, q]);
        let not_and = m.mk_not(and);
        let np = m.mk_not(p);
        let nq = m.mk_not(q);
        let expected = m.mk_or(&[np, nq]);
        assert_eq!(to_nnf(&mut m, not_and), expected);
    }

    #[test]
    fn pushes_through_nested_negation() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        // ¬(p ∨ ¬q) = ¬p ∧ q
        let nq = m.mk_not(q);
        let or = m.mk_or(&[p, nq]);
        let not_or = m.mk_not(or);
        let np = m.mk_not(p);
        let expected = m.mk_and(&[np, q]);
        assert_eq!(to_nnf(&mut m, not_or), expected);
    }

    #[test]
    fn expands_implications() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        // p → q  =  ¬p ∨ q
        let imp = m.mk_implies(p, q);
        let np = m.mk_not(p);
        let expected = m.mk_or(&[np, q]);
        assert_eq!(to_nnf(&mut m, imp), expected);
        // ¬(p → q) = p ∧ ¬q
        let not_imp = m.mk_not(imp);
        let nq = m.mk_not(q);
        let expected2 = m.mk_and(&[p, nq]);
        assert_eq!(to_nnf(&mut m, not_imp), expected2);
    }

    #[test]
    fn atoms_and_constants() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let t = m.mk_true();
        // A bare atom is unchanged; ¬true = false.
        assert_eq!(to_nnf(&mut m, p), p);
        let nt = m.mk_not(t);
        assert_eq!(to_nnf(&mut m, nt), m.mk_false());
        // Negation lands on an uninterpreted atom.
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let le = m.mk_le(x, y);
        let not_le = m.mk_not(le);
        assert_eq!(to_nnf(&mut m, not_le), not_le); // already NNF (¬atom)
    }
}
