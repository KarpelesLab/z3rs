//! Congruence closure for the theory of equality with uninterpreted functions
//! (EUF) — the heart of `z3/src/ast/euf` / `theory_uf` (Z3 4.17.0, MIT).
//!
//! This is a union-find enriched with **congruence**: if `a₁≈b₁, …, aₙ≈bₙ` then
//! `f(a₁,…,aₙ) ≈ f(b₁,…,bₙ)`. It answers "are these equalities plus congruence
//! consistent with these disequalities?" — enough to decide the quantifier-free
//! theory of equality and uninterpreted functions over a fixed set of terms.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;

/// A congruence-closure structure over the subterms of some formula.
pub struct Egraph {
    /// Dense id per term (index into the union-find).
    ids: BTreeMap<AstId, usize>,
    terms: Vec<AstId>,
    parent: Vec<usize>,
    /// For each term, its `(decl, arg-term-ids)` signature (empty for leaves).
    app: Vec<Option<(AstId, Vec<usize>)>>,
}

impl Egraph {
    /// An empty e-graph (no terms), for models without uninterpreted content.
    pub fn new_empty() -> Egraph {
        Egraph {
            ids: BTreeMap::new(),
            terms: Vec::new(),
            parent: Vec::new(),
            app: Vec::new(),
        }
    }

    /// Build an e-graph over every subterm reachable from the given roots.
    pub fn new(m: &AstManager, roots: &[AstId]) -> Egraph {
        let mut g = Egraph {
            ids: BTreeMap::new(),
            terms: Vec::new(),
            parent: Vec::new(),
            app: Vec::new(),
        };
        for &r in roots {
            for t in m.postorder(r) {
                g.intern(m, t);
            }
        }
        g
    }

    fn intern(&mut self, m: &AstManager, t: AstId) -> usize {
        if let Some(&id) = self.ids.get(&t) {
            return id;
        }
        // Record the application signature, interning any child not already seen
        // first so its id exists before this node's (the AST is a DAG, so this
        // terminates). Doing this before assigning `id` keeps every parallel
        // vector index-aligned regardless of the caller's traversal order.
        let sig = match m.node(t) {
            AstNode::App(a) if !a.args.is_empty() => {
                let args = a.args.clone();
                let arg_ids = args.iter().map(|&c| self.intern(m, c)).collect();
                Some((a.decl, arg_ids))
            }
            _ => None,
        };
        let id = self.terms.len();
        self.ids.insert(t, id);
        self.terms.push(t);
        self.parent.push(id);
        self.app.push(sig);
        id
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]]; // path halving
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }

    /// Merge `a` and `b` (and re-close under congruence).
    fn merge_terms(&mut self, m: &AstManager, a: AstId, b: AstId) {
        let (ia, ib) = (self.intern(m, a), self.intern(m, b));
        self.union(ia, ib);
    }

    /// Propagate congruence to a fixpoint: equal-arg applications of the same
    /// declaration are merged.
    fn close(&mut self) {
        let n = self.terms.len();
        loop {
            let mut changed = false;
            // Group applications by their representative signature.
            let mut sigs: BTreeMap<(AstId, Vec<usize>), usize> = BTreeMap::new();
            for i in 0..n {
                if let Some((decl, args)) = self.app[i].clone() {
                    let key: Vec<usize> = args.iter().map(|&a| self.find(a)).collect();
                    let root = self.find(i);
                    match sigs.get(&(decl, key.clone())) {
                        Some(&j) => {
                            if self.find(j) != root {
                                self.union(i, j);
                                changed = true;
                            }
                        }
                        None => {
                            sigs.insert((decl, key), root);
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// The canonical class index of `t` in the current union-find (terms that
    /// are equal share it). Interns `t` if unseen. Meaningful after a call to
    /// `is_consistent` has applied the equalities.
    pub fn class_of(&mut self, m: &AstManager, t: AstId) -> usize {
        let i = self.intern(m, t);
        self.find(i)
    }

    /// Are the `equalities` (with congruence) consistent with the
    /// `disequalities`? Returns `true` if satisfiable.
    pub fn is_consistent(
        &mut self,
        m: &AstManager,
        equalities: &[(AstId, AstId)],
        disequalities: &[(AstId, AstId)],
    ) -> bool {
        for &(a, b) in equalities {
            self.merge_terms(m, a, b);
        }
        self.close();
        for &(a, b) in disequalities {
            let (ia, ib) = (self.intern(m, a), self.intern(m, b));
            if self.find(ia) == self.find(ib) {
                return false; // a ≠ b but a ≈ b
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::symbol::Symbol;

    fn constant(m: &mut AstManager, name: &str, sort: AstId) -> AstId {
        let d = m.mk_func_decl(Symbol::new(name), &[], sort);
        m.mk_const(d)
    }

    #[test]
    fn transitivity_conflict() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // a=b, b=c, a≠c  → inconsistent
        let mut g = Egraph::new(&m, &[a, b, c]);
        assert!(!g.is_consistent(&m, &[(a, b), (b, c)], &[(a, c)]));
    }

    #[test]
    fn satisfiable_equalities() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // a=b, a≠c is fine
        let mut g = Egraph::new(&m, &[a, b, c]);
        assert!(g.is_consistent(&m, &[(a, b)], &[(a, c)]));
    }

    #[test]
    fn congruence_forces_equality() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[s], s);
        let fa = m.mk_app(f, &[a]);
        let fb = m.mk_app(f, &[b]);
        // a=b ⇒ f(a)=f(b), so f(a)≠f(b) is inconsistent
        let mut g = Egraph::new(&m, &[fa, fb]);
        assert!(!g.is_consistent(&m, &[(a, b)], &[(fa, fb)]));

        // Without a=b, f(a)≠f(b) is fine.
        let mut g2 = Egraph::new(&m, &[fa, fb]);
        assert!(g2.is_consistent(&m, &[], &[(fa, fb)]));
    }
}
