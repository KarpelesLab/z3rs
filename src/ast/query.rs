//! AST traversal and term recognizers.
//!
//! Ports the workhorse queries every higher layer needs: a post-order walk over
//! the expression DAG (`for_each_expr` in `z3/src/ast/for_each_expr.h`), term
//! depth, and `is_*` recognizers for the basic family (the `is_and`, `is_eq`, …
//! helpers scattered through `z3/src/ast/ast.h`). MIT; see NOTICE.

use alloc::vec::Vec;

use crate::ast::basic::BasicOp;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;
use crate::ast::{AstId, BASIC_FAMILY_ID, DeclKind, FamilyId};

impl AstManager {
    /// The direct expression children of `id` (application arguments; none for
    /// variables/constants). Sorts and declarations have no expression children.
    fn expr_children(&self, id: AstId) -> &[AstId] {
        match self.node(id) {
            AstNode::App(a) => &a.args,
            _ => &[],
        }
    }

    /// All expressions reachable from `root`, in post-order (children before
    /// parents), each visited exactly once.
    pub fn postorder(&self, root: AstId) -> Vec<AstId> {
        let mut visited = alloc::vec![false; self.len()];
        let mut order = Vec::new();
        // Iterative DFS: push (node, children-expanded?) frames.
        let mut stack: Vec<(AstId, bool)> = alloc::vec![(root, false)];
        while let Some((id, expanded)) = stack.pop() {
            if visited[id.0 as usize] {
                continue;
            }
            if expanded {
                visited[id.0 as usize] = true;
                order.push(id);
            } else {
                stack.push((id, true));
                for &c in self.expr_children(id) {
                    if !visited[c.0 as usize] {
                        stack.push((c, false));
                    }
                }
            }
        }
        order
    }

    /// Visit every expression reachable from `root` once, in post-order.
    pub fn for_each_expr<F: FnMut(AstId)>(&self, root: AstId, mut f: F) {
        for id in self.postorder(root) {
            f(id);
        }
    }

    /// The number of distinct expressions reachable from `root`.
    pub fn num_subexprs(&self, root: AstId) -> usize {
        self.postorder(root).len()
    }

    /// The depth of `root` (a leaf has depth 1).
    pub fn get_depth(&self, root: AstId) -> usize {
        // Post-order guarantees children are computed before parents.
        let order = self.postorder(root);
        let mut depth = alloc::vec![0usize; self.len()];
        for &id in &order {
            let children = self.expr_children(id);
            let d = children
                .iter()
                .map(|&c| depth[c.0 as usize])
                .max()
                .unwrap_or(0);
            depth[id.0 as usize] = d + 1;
        }
        depth[root.0 as usize]
    }

    // --- recognizers ------------------------------------------------------

    /// Is `id` an application of the declaration in family `fid` with kind `k`?
    pub fn is_app_of(&self, id: AstId, fid: FamilyId, k: DeclKind) -> bool {
        match self.node(id) {
            AstNode::App(a) => {
                let d = self.func_decl(a.decl).expect("app decl");
                d.info.family_id == fid && d.info.decl_kind == k
            }
            _ => false,
        }
    }

    /// Is `id` an application of the basic-family op `op`?
    fn is_basic(&self, id: AstId, op: BasicOp) -> bool {
        self.is_app_of(id, BASIC_FAMILY_ID, op as DeclKind)
    }

    /// Is `id` the constant `true`?
    pub fn is_true(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::True)
    }
    /// Is `id` the constant `false`?
    pub fn is_false(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::False)
    }
    /// Is `id` a `not` application?
    pub fn is_not(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::Not)
    }
    /// Is `id` an `and` application?
    pub fn is_and(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::And)
    }
    /// Is `id` an `or` application?
    pub fn is_or(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::Or)
    }
    /// Is `id` an `=` application?
    pub fn is_eq(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::Eq)
    }
    /// Is `id` an `ite` application?
    pub fn is_ite(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::Ite)
    }
    /// Is `id` an `=>` (implies) application?
    pub fn is_implies(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::Implies)
    }
    /// Is `id` an `xor` application?
    pub fn is_xor(&self, id: AstId) -> bool {
        self.is_basic(id, BasicOp::Xor)
    }

    /// Is `id` an uninterpreted constant (nullary app, null family)?
    pub fn is_uninterp_const(&self, id: AstId) -> bool {
        match self.node(id) {
            AstNode::App(a) if a.args.is_empty() => self
                .func_decl(a.decl)
                .is_some_and(|d| d.info.family_id == crate::ast::NULL_FAMILY_ID),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn postorder_visits_children_first_and_once() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let notq = m.mk_not(q);
        let or = m.mk_or(&[p, notq]);
        // (or p (not q)) ; shared subterm q appears once.
        let order = m.postorder(or);
        assert_eq!(order.len(), 4); // p, q, (not q), (or ...)
        assert_eq!(*order.last().unwrap(), or);
        // Each child precedes its parent.
        let pos = |x| order.iter().position(|&y| y == x).unwrap();
        assert!(pos(q) < pos(notq));
        assert!(pos(notq) < pos(or));
        assert!(pos(p) < pos(or));
    }

    #[test]
    fn shared_subterms_counted_once() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        // (+ x x): x is shared, so subexprs = {x, (+ x x)} = 2.
        let sum = m.mk_add(&[x, x]);
        assert_eq!(m.num_subexprs(sum), 2);
        assert_eq!(m.get_depth(x), 1);
        assert_eq!(m.get_depth(sum), 2);
    }

    #[test]
    fn recognizers() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let t = m.mk_true();
        let notp = m.mk_not(p);
        let and = m.mk_and(&[p, q]);
        let eq = m.mk_eq(p, q);
        assert!(m.is_true(t));
        assert!(!m.is_false(t));
        assert!(m.is_not(notp));
        assert!(m.is_and(and));
        assert!(m.is_eq(eq));
        assert!(!m.is_and(eq));
        assert!(m.is_uninterp_const(p));
        assert!(!m.is_uninterp_const(t)); // true is basic-family, not uninterpreted
        assert!(!m.is_uninterp_const(and));
    }

    #[test]
    fn depth_of_nested_arithmetic() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let one = m.mk_int(1);
        let sum = m.mk_add(&[x, one]); // depth 2
        let le = m.mk_le(sum, one); // depth 3
        assert_eq!(m.get_depth(le), 3);
    }
}
