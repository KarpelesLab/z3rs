//! The bottom-up simplification driver — a lightweight `th_rewriter`
//! (`z3/src/ast/rewriter/th_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! [`simplify`] walks a term bottom-up (children before parents), simplifying
//! each application by dispatching to the per-theory folders
//! ([`bool_rewriter`],
//! [`arith_rewriter`]) and rebuilding through
//! the [`AstManager`] so results stay hash-consed.

use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;
use crate::rewriter::{arith_rewriter, bool_rewriter};

/// Simplify `root`, rewriting bottom-up.
pub fn simplify(m: &mut AstManager, root: AstId) -> AstId {
    let order = m.postorder(root);
    // Original node ids are all `< m.len()` at entry; simplified results may be
    // newly created ids, which are never looked up here.
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

/// Simplify a single application, given already-simplified `args`.
fn simplify_app(m: &mut AstManager, decl: AstId, args: &[AstId]) -> AstId {
    if let Some(r) = bool_rewriter::try_fold(m, decl, args) {
        return r;
    }
    if let Some(r) = arith_rewriter::try_fold(m, decl, args) {
        return r;
    }
    // No theory rule fired: rebuild (hash-consing returns the original node if
    // nothing changed).
    m.mk_app(decl, args)
}

#[cfg(test)]
mod tests {
    use crate::ast::manager::AstManager;
    use crate::rewriter::simplify;

    #[test]
    fn mixed_boolean_and_arithmetic_simplification() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        // (and true (<= x (+ 2 3))) = (<= x 5)
        let t = m.mk_true();
        let sum = m.mk_add(&[two, three]);
        let le = m.mk_le(x, sum);
        let formula = m.mk_and(&[t, le]);
        let expected = m.mk_le(x, five);
        assert_eq!(simplify(&mut m, formula), expected);
    }
}
