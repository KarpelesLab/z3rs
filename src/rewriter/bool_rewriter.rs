//! Boolean constant folding — a subset of `bool_rewriter`
//! (`z3/src/ast/rewriter/bool_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! [`try_fold`] applies the identity/annihilator rules for the propositional
//! connectives, double-negation, reflexive equality, and `ite` folding to one
//! basic-family application. The bottom-up driver that calls it lives in
//! [`th_rewriter`](crate::rewriter::th_rewriter); use
//! [`crate::rewriter::simplify`] to simplify a whole formula.

use alloc::vec::Vec;

use crate::ast::basic::BasicOp;
use crate::ast::manager::AstManager;
use crate::ast::{AstId, BASIC_FAMILY_ID, DeclKind};

/// Try to fold a basic-family application `decl(args)`. Returns `None` if `decl`
/// is not a basic-family op this rewriter handles (the driver then rebuilds).
pub(crate) fn try_fold(m: &mut AstManager, decl: AstId, args: &[AstId]) -> Option<AstId> {
    let d = m.func_decl(decl).expect("app decl");
    if d.info.family_id != BASIC_FAMILY_ID {
        return None;
    }
    let kind = d.info.decl_kind;
    if kind == BasicOp::Not as DeclKind {
        Some(simplify_not(m, decl, args))
    } else if kind == BasicOp::And as DeclKind {
        Some(simplify_and(m, args))
    } else if kind == BasicOp::Or as DeclKind {
        Some(simplify_or(m, args))
    } else if kind == BasicOp::Eq as DeclKind && args[0] == args[1] {
        Some(m.mk_true())
    } else if kind == BasicOp::Ite as DeclKind {
        Some(simplify_ite(m, decl, args))
    } else {
        None
    }
}

fn simplify_not(m: &mut AstManager, decl: AstId, args: &[AstId]) -> AstId {
    let a = args[0];
    if m.is_true(a) {
        return m.mk_false();
    }
    if m.is_false(a) {
        return m.mk_true();
    }
    if m.is_not(a) {
        // not(not(x)) = x
        return m.app_args(a)[0];
    }
    m.mk_app(decl, args)
}

fn simplify_and(m: &mut AstManager, args: &[AstId]) -> AstId {
    let mut kept: Vec<AstId> = Vec::new();
    for &a in args {
        if m.is_false(a) {
            return m.mk_false(); // annihilator
        }
        if m.is_true(a) {
            continue; // identity
        }
        if !kept.contains(&a) {
            kept.push(a); // idempotent
        }
    }
    match kept.len() {
        0 => m.mk_true(),
        1 => kept[0],
        _ => m.mk_and(&kept),
    }
}

fn simplify_or(m: &mut AstManager, args: &[AstId]) -> AstId {
    let mut kept: Vec<AstId> = Vec::new();
    for &a in args {
        if m.is_true(a) {
            return m.mk_true(); // annihilator
        }
        if m.is_false(a) {
            continue; // identity
        }
        if !kept.contains(&a) {
            kept.push(a); // idempotent
        }
    }
    match kept.len() {
        0 => m.mk_false(),
        1 => kept[0],
        _ => m.mk_or(&kept),
    }
}

fn simplify_ite(m: &mut AstManager, decl: AstId, args: &[AstId]) -> AstId {
    let (c, t, e) = (args[0], args[1], args[2]);
    if m.is_true(c) {
        return t;
    }
    if m.is_false(c) {
        return e;
    }
    if t == e {
        return t;
    }
    m.mk_app(decl, args)
}

#[cfg(test)]
mod tests {
    use crate::ast::manager::AstManager;
    use crate::rewriter::simplify;

    #[test]
    fn constant_folds_connectives() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let t = m.mk_true();
        let f = m.mk_false();

        let and_pt = m.mk_and(&[p, t]);
        assert_eq!(simplify(&mut m, and_pt), p); // (and p true) = p
        let and_pf = m.mk_and(&[p, f]);
        assert_eq!(simplify(&mut m, and_pf), f); // (and p false) = false
        let or_fp = m.mk_or(&[f, p]);
        assert_eq!(simplify(&mut m, or_fp), p); // (or false p) = p
        let nnp = {
            let np = m.mk_not(p);
            m.mk_not(np)
        };
        assert_eq!(simplify(&mut m, nnp), p); // not(not(p)) = p
    }

    #[test]
    fn folds_ite_and_eq() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let t = m.mk_true();
        let f = m.mk_false();
        let c = m.mk_bool_const("c");

        let ite_t = m.mk_ite(t, x, y);
        assert_eq!(simplify(&mut m, ite_t), x);
        let ite_f = m.mk_ite(f, x, y);
        assert_eq!(simplify(&mut m, ite_f), y);
        let ite_same = m.mk_ite(c, x, x);
        assert_eq!(simplify(&mut m, ite_same), x);
        let eq_xx = m.mk_eq(x, x);
        assert_eq!(simplify(&mut m, eq_xx), t);
    }

    #[test]
    fn simplifies_nested_formula_bottom_up() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let f = m.mk_false();
        // (and (or false p) (not false)) = (and p true) = p
        let or = m.mk_or(&[f, p]);
        let notf = m.mk_not(f);
        let formula = m.mk_and(&[or, notf]);
        assert_eq!(simplify(&mut m, formula), p);
    }

    #[test]
    fn preserves_irreducible_terms() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let and = m.mk_and(&[p, q]);
        // Nothing to fold: result is the same hash-consed node.
        assert_eq!(simplify(&mut m, and), and);
    }
}
