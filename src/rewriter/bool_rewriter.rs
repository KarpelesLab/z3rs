//! Boolean constant folding — a subset of `bool_rewriter`
//! (`z3/src/ast/rewriter/bool_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! [`simplify`] rewrites a formula bottom-up, applying the identity/annihilator
//! rules for the propositional connectives, double-negation, reflexive equality,
//! and `ite` folding. It rebuilds through the [`AstManager`], so results stay
//! hash-consed and structural sharing is preserved. This is the seed of the full
//! `th_rewriter`; theory rewriting and richer boolean rules come later.

use alloc::vec::Vec;

use crate::ast::basic::BasicOp;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;
use crate::ast::{AstId, BASIC_FAMILY_ID, DeclKind, FamilyId};

/// Simplify `root` by bottom-up boolean constant folding.
pub fn simplify(m: &mut AstManager, root: AstId) -> AstId {
    let order = m.postorder(root);
    // Map every original node id to its simplified replacement. Original ids are
    // all `< m.len()` at entry; simplified results may be newly created ids,
    // which we never need to look up here.
    let mut cache: Vec<Option<AstId>> = alloc::vec![None; m.len()];
    for &id in &order {
        let simplified = match m.node(id).clone() {
            AstNode::App(a) => {
                let new_args: Vec<AstId> = a
                    .args
                    .iter()
                    .map(|&c| cache[c.0 as usize].unwrap())
                    .collect();
                simplify_app(m, a.decl, &new_args)
            }
            // Variables and (leaf) constants rewrite to themselves.
            _ => id,
        };
        cache[id.0 as usize] = Some(simplified);
    }
    cache[root.0 as usize].unwrap()
}

/// The `(family_id, decl_kind)` of a declaration.
fn decl_head(m: &AstManager, decl: AstId) -> (FamilyId, DeclKind) {
    let d = m.func_decl(decl).expect("simplify: app decl");
    (d.info.family_id, d.info.decl_kind)
}

fn simplify_app(m: &mut AstManager, decl: AstId, args: &[AstId]) -> AstId {
    let (fid, kind) = decl_head(m, decl);
    if fid == BASIC_FAMILY_ID {
        if kind == BasicOp::Not as DeclKind {
            return simplify_not(m, decl, args);
        } else if kind == BasicOp::And as DeclKind {
            return simplify_and(m, args);
        } else if kind == BasicOp::Or as DeclKind {
            return simplify_or(m, args);
        } else if kind == BasicOp::Eq as DeclKind {
            if args[0] == args[1] {
                return m.mk_true();
            }
        } else if kind == BasicOp::Ite as DeclKind {
            return simplify_ite(m, decl, args);
        }
    }
    // No rule fired: rebuild with the (possibly) simplified arguments. If nothing
    // changed, hash-consing returns the original node.
    m.mk_app(decl, args)
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
    use super::*;

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
