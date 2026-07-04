//! Boolean constant folding — a subset of `bool_rewriter`
//! (`z3/src/ast/rewriter/bool_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! `try_fold` applies the identity/annihilator rules for the propositional
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
    } else if kind == BasicOp::Eq as DeclKind {
        simplify_eq(m, args)
    } else if kind == BasicOp::Ite as DeclKind {
        Some(simplify_ite(m, decl, args))
    } else if kind == BasicOp::Implies as DeclKind {
        simplify_implies(m, args)
    } else if kind == BasicOp::Xor as DeclKind {
        simplify_xor(m, args)
    } else {
        None
    }
}

/// `(=> a b)`: fold the constant cases and normalize `a => b` to `or(not a, b)`
/// only when a constant is involved (leave symbolic implications intact).
fn simplify_implies(m: &mut AstManager, args: &[AstId]) -> Option<AstId> {
    let (a, b) = (args[0], args[1]);
    if m.is_false(a) || m.is_true(b) {
        Some(m.mk_true())
    } else if m.is_true(a) {
        Some(b) // true => b  ==  b
    } else if m.is_false(b) {
        Some(m.mk_not(a)) // a => false  ==  not a
    } else {
        None
    }
}

/// `(xor a b)`: fold constant cases and reflexivity.
fn simplify_xor(m: &mut AstManager, args: &[AstId]) -> Option<AstId> {
    let (a, b) = (args[0], args[1]);
    if a == b {
        Some(m.mk_false())
    } else if m.is_false(a) {
        Some(b) // xor(false, b) = b
    } else if m.is_false(b) {
        Some(a)
    } else if m.is_true(a) {
        Some(m.mk_not(b)) // xor(true, b) = not b
    } else if m.is_true(b) {
        Some(m.mk_not(a))
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

/// `(= a b)`: reflexivity, numeral comparison, and boolean equality with a
/// constant (`(= p true) = p`, `(= p false) = ¬p`).
fn simplify_eq(m: &mut AstManager, args: &[AstId]) -> Option<AstId> {
    if args.len() != 2 {
        return None;
    }
    let (a, b) = (args[0], args[1]);
    if a == b {
        return Some(m.mk_true()); // reflexivity
    }
    if let (Some(x), Some(y)) = (m.as_numeral(a), m.as_numeral(b)) {
        return Some(if x == y { m.mk_true() } else { m.mk_false() });
    }
    if m.is_true(a) {
        return Some(b);
    }
    if m.is_true(b) {
        return Some(a);
    }
    if m.is_false(a) {
        return Some(m.mk_not(b));
    }
    if m.is_false(b) {
        return Some(m.mk_not(a));
    }
    None
}

/// True iff `x` is the negation of some literal also present in `lits` (so the
/// conjunction/disjunction has a complementary pair).
fn has_complement(m: &AstManager, lits: &[AstId], x: AstId) -> bool {
    m.is_not(x) && lits.contains(&m.app_args(x)[0])
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
    // p ∧ ¬p → false.
    if kept.iter().any(|&a| has_complement(m, &kept, a)) {
        return m.mk_false();
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
    // p ∨ ¬p → true.
    if kept.iter().any(|&a| has_complement(m, &kept, a)) {
        return m.mk_true();
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
    // Boolean-constant branches collapse to a connective (`is_true`/`is_false`
    // only match the Bool constants, so these fire only for a Boolean ite). Route
    // through the connective folders so the result is itself simplified.
    if m.is_true(t) {
        return simplify_or(m, &[c, e]); // (ite c true e) = c ∨ e
    }
    if m.is_false(e) {
        return simplify_and(m, &[c, t]); // (ite c t false) = c ∧ t
    }
    if m.is_false(t) {
        let nc = m.mk_not(c);
        return simplify_and(m, &[nc, e]); // (ite c false e) = ¬c ∧ e
    }
    if m.is_true(e) {
        let nc = m.mk_not(c);
        return simplify_or(m, &[nc, t]); // (ite c t true) = ¬c ∨ t
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

    #[test]
    fn folds_complementary_pairs_and_bool_eq() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let np = m.mk_not(p);
        let t = m.mk_true();
        let f = m.mk_false();
        // p ∧ ¬p = false ; p ∨ ¬p = true
        let and = m.mk_and(&[p, np]);
        assert_eq!(simplify(&mut m, and), f);
        let or = m.mk_or(&[p, np]);
        assert_eq!(simplify(&mut m, or), t);
        // (= p true) = p ; (= p false) = ¬p
        let eqt = m.mk_eq(p, t);
        assert_eq!(simplify(&mut m, eqt), p);
        let eqf = m.mk_eq(p, f);
        assert_eq!(simplify(&mut m, eqf), np);
    }

    #[test]
    fn folds_numeral_equality_and_bool_ite() {
        let mut m = AstManager::new();
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let t = m.mk_true();
        let f = m.mk_false();
        // (= 3 5) = false ; (= 3 3) = true
        let ne = m.mk_eq(three, five);
        assert_eq!(simplify(&mut m, ne), f);
        let eq = m.mk_eq(three, three);
        assert_eq!(simplify(&mut m, eq), t);
        // (ite c true false) = c
        let c = m.mk_bool_const("c");
        let ite = m.mk_ite(c, t, f);
        assert_eq!(simplify(&mut m, ite), c);
    }

    #[test]
    fn folds_implies_and_xor() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let t = m.mk_true();
        let f = m.mk_false();
        let notp = m.mk_not(p);

        // (=> false p) = true ; (=> true p) = p ; (=> p false) = (not p)
        let i1 = m.mk_implies(f, p);
        assert_eq!(simplify(&mut m, i1), t);
        let i2 = m.mk_implies(t, p);
        assert_eq!(simplify(&mut m, i2), p);
        let i3 = m.mk_implies(p, f);
        assert_eq!(simplify(&mut m, i3), notp);

        // (xor p p) = false ; (xor false p) = p ; (xor true p) = (not p)
        let x1 = m.mk_xor(p, p);
        assert_eq!(simplify(&mut m, x1), f);
        let x2 = m.mk_xor(f, p);
        assert_eq!(simplify(&mut m, x2), p);
        let x3 = m.mk_xor(t, p);
        assert_eq!(simplify(&mut m, x3), notp);
    }
}
