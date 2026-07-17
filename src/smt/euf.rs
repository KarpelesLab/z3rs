//! Congruence closure for the theory of equality with uninterpreted functions
//! (EUF) — the heart of `z3/src/ast/euf` / `theory_uf` (Z3 4.17.0, MIT).
//!
//! This is a union-find enriched with **congruence**: if `a₁≈b₁, …, aₙ≈bₙ` then
//! `f(a₁,…,aₙ) ≈ f(b₁,…,bₙ)`. It answers "are these equalities plus congruence
//! consistent with these disequalities?" — enough to decide the quantifier-free
//! theory of equality and uninterpreted functions over a fixed set of terms.

use alloc::collections::{BTreeMap, BTreeSet};
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

/// Why two enodes were merged in the [`ProofEgraph`] proof forest — Z3's
/// `eq_justification` (`ast/euf/euf_justification.h`).
#[derive(Clone, Debug)]
enum Cause {
    /// The merge came from an asserted input equality identified by `id` — an
    /// index into the caller's `euf_eq` list (Z3's `EQUATION`).
    Equation(usize),
    /// `f(x₁…xₙ)` (enode `lhs`) merged with `f(y₁…yₙ)` (enode `rhs`) because the
    /// arguments are already pairwise equal (Z3's `CONGRUENCE`). Explanation
    /// recurses `xᵢ ≈ yᵢ` for every argument position.
    Congruence(usize, usize),
}

/// A congruence closure that, alongside deciding consistency, can **explain** why
/// any two equal terms are equal — the set of input equalities (by id) whose
/// merges, plus congruence, force them into one class. This is the
/// proof-producing union-find of Nieuwenhuis–Oliveras, mirroring Z3's
/// `smt_conflict_resolution` `eq_justification2literals` / `euf_egraph` explain.
///
/// It keeps two disjoint structures over the same interned terms:
/// * a **fast find** (`parent`, path-halved) that answers `class_of` cheaply, and
/// * a **proof forest** (`pparent`/`pedge`, never compressed) recording the exact
///   causal edge of every merge, so paths reconstruct the justification.
pub struct ProofEgraph {
    ids: BTreeMap<AstId, usize>,
    terms: Vec<AstId>,
    /// `(decl, arg-term-ids)` signature of each application (`None` for leaves).
    app: Vec<Option<(AstId, Vec<usize>)>>,
    /// Fast union-find representative (path-halved, for `class_of`/congruence).
    parent: Vec<usize>,
    /// Proof-forest parent of each node (`pparent[r] == r` marks a root). Never
    /// path-compressed — the tree edges *are* the proof.
    pparent: Vec<usize>,
    /// The cause of the edge `node → pparent[node]` (`None` at a root).
    pedge: Vec<Option<Cause>>,
    /// Per-node generation stamp used to find nearest common ancestors.
    mark: Vec<u64>,
    stamp: u64,
}

impl ProofEgraph {
    /// Build a proof-producing e-graph over every subterm reachable from `roots`.
    pub fn new(m: &AstManager, roots: &[AstId]) -> ProofEgraph {
        let mut g = ProofEgraph {
            ids: BTreeMap::new(),
            terms: Vec::new(),
            app: Vec::new(),
            parent: Vec::new(),
            pparent: Vec::new(),
            pedge: Vec::new(),
            mark: Vec::new(),
            stamp: 0,
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
        self.app.push(sig);
        self.parent.push(id);
        self.pparent.push(id); // its own proof-tree root initially
        self.pedge.push(None);
        self.mark.push(0);
        id
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]]; // path halving
            x = self.parent[x];
        }
        x
    }

    /// Re-root the proof tree of `x` so that `x` becomes its own root, reversing
    /// (and re-labelling) every edge on the path to the old root.
    fn reroot(&mut self, x: usize) {
        let mut child = x;
        let mut parent = self.pparent[child];
        if parent == child {
            return; // already a root
        }
        let mut edge = self.pedge[child].clone();
        self.pparent[child] = child;
        self.pedge[child] = None;
        loop {
            let gp = self.pparent[parent];
            let ge = self.pedge[parent].clone();
            self.pparent[parent] = child;
            self.pedge[parent] = edge;
            if parent == gp {
                break; // reached the old root
            }
            child = parent;
            parent = gp;
            edge = ge;
        }
    }

    /// Merge the classes of enodes `a` and `b` with the given `cause`. Precondition
    /// (always met by callers): they are in different classes, hence different
    /// proof trees, so re-rooting `a` and hanging it under `b` keeps a forest.
    fn merge(&mut self, a: usize, b: usize, cause: Cause) {
        self.reroot(a);
        self.pparent[a] = b;
        self.pedge[a] = Some(cause);
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }

    /// Assert the given input equalities `(id, a, b)` (`id` indexes the caller's
    /// equality list), then close under congruence — recording every merge's
    /// cause in the proof forest.
    pub fn assert_eqs(&mut self, m: &AstManager, eqs: &[(usize, AstId, AstId)]) {
        for &(id, a, b) in eqs {
            let (ia, ib) = (self.intern(m, a), self.intern(m, b));
            if self.find(ia) != self.find(ib) {
                self.merge(ia, ib, Cause::Equation(id));
            }
        }
        self.close();
    }

    /// Congruence closure to a fixpoint: applications of the same declaration whose
    /// arguments are pairwise equal are merged, with a [`Cause::Congruence`] edge.
    fn close(&mut self) {
        let n = self.terms.len();
        loop {
            let mut changed = false;
            let mut sigs: BTreeMap<(AstId, Vec<usize>), usize> = BTreeMap::new();
            for i in 0..n {
                if let Some((decl, args)) = self.app[i].clone() {
                    let key: Vec<usize> = args.iter().map(|&a| self.find(a)).collect();
                    match sigs.get(&(decl, key.clone())) {
                        Some(&j) => {
                            if self.find(j) != self.find(i) {
                                self.merge(i, j, Cause::Congruence(i, j));
                                changed = true;
                            }
                        }
                        None => {
                            sigs.insert((decl, key), i);
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// The canonical class index of `t` (equal terms share it). Interns `t` if
    /// unseen. Meaningful after [`assert_eqs`](Self::assert_eqs).
    pub fn class_of(&mut self, m: &AstManager, t: AstId) -> usize {
        let i = self.intern(m, t);
        self.find(i)
    }

    /// Nearest common ancestor of `a` and `b` in the proof forest (they must be in
    /// the same tree). Stamps `a`'s ancestors, then walks up from `b`.
    fn nca(&mut self, a: usize, b: usize) -> usize {
        self.stamp += 1;
        let s = self.stamp;
        let mut x = a;
        loop {
            self.mark[x] = s;
            let p = self.pparent[x];
            if p == x {
                break;
            }
            x = p;
        }
        let mut y = b;
        loop {
            if self.mark[y] == s {
                return y;
            }
            let p = self.pparent[y];
            if p == y {
                return y; // different trees (should not happen for equal terms)
            }
            y = p;
        }
    }

    /// Walk the proof path from `x` up to `stop`, collecting the causes of each
    /// edge: `Equation` ids land in `out`, `Congruence` edges push their argument
    /// pairs onto `work` for recursive explanation.
    fn collect(
        &self,
        mut x: usize,
        stop: usize,
        out: &mut BTreeSet<usize>,
        work: &mut Vec<(usize, usize)>,
    ) {
        while x != stop {
            match &self.pedge[x] {
                Some(Cause::Equation(id)) => {
                    out.insert(*id);
                }
                Some(Cause::Congruence(p, q)) => {
                    if let (Some((_, ap)), Some((_, aq))) = (&self.app[*p], &self.app[*q]) {
                        for (u, v) in ap.iter().zip(aq.iter()) {
                            work.push((*u, *v));
                        }
                    }
                }
                None => break, // reached a root without hitting `stop`
            }
            x = self.pparent[x];
        }
    }

    /// The set of input-equality ids whose asserted merges (plus congruence) force
    /// `a` and `b` into one class. Precondition: `class_of(a) == class_of(b)`.
    pub fn explain(&mut self, m: &AstManager, a: AstId, b: AstId) -> Vec<usize> {
        let (ia, ib) = (self.intern(m, a), self.intern(m, b));
        let mut out: BTreeSet<usize> = BTreeSet::new();
        let mut work: Vec<(usize, usize)> = alloc::vec![(ia, ib)];
        let mut done: BTreeSet<(usize, usize)> = BTreeSet::new();
        while let Some((x, y)) = work.pop() {
            if x == y {
                continue;
            }
            let key = if x < y { (x, y) } else { (y, x) };
            if !done.insert(key) {
                continue; // already explained this pair
            }
            let anc = self.nca(x, y);
            self.collect(x, anc, &mut out, &mut work);
            self.collect(y, anc, &mut out, &mut work);
        }
        out.into_iter().collect()
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

    // Confirm a returned explanation really is inconsistent with the diseq: the
    // named equalities merged into a fresh e-graph must collapse `a`≈`b`.
    fn explanation_is_sound(
        m: &AstManager,
        eqs: &[(usize, AstId, AstId)],
        roots: &[AstId],
        core: &[usize],
        a: AstId,
        b: AstId,
    ) -> bool {
        let subset: Vec<(AstId, AstId)> = core
            .iter()
            .map(|&id| {
                let (_, x, y) = eqs[id];
                (x, y)
            })
            .collect();
        let mut g = Egraph::new(m, roots);
        // a=b under just the core equalities ⇒ the diseq (a,b) is violated.
        !g.is_consistent(m, &subset, &[(a, b)])
    }

    #[test]
    fn explain_transitivity() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // a=b (id 0), b=c (id 1), a≠c
        let eqs = [(0usize, a, b), (1usize, b, c)];
        let mut g = ProofEgraph::new(&m, &[a, b, c]);
        g.assert_eqs(&m, &eqs);
        assert_eq!(g.class_of(&m, a), g.class_of(&m, c));
        let core = g.explain(&m, a, c);
        assert_eq!(core, alloc::vec![0, 1]);
        assert!(explanation_is_sound(&m, &eqs, &[a, b, c], &core, a, c));
    }

    #[test]
    fn explain_through_congruence() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[s], s);
        let fa = m.mk_app(f, &[a]);
        let fc = m.mk_app(f, &[c]);
        // a=b (0), b=c (1) ⇒ a=c ⇒ f(a)=f(c). Diseq f(a)≠f(c).
        let eqs = [(0usize, a, b), (1usize, b, c)];
        let mut g = ProofEgraph::new(&m, &[fa, fc]);
        g.assert_eqs(&m, &eqs);
        assert_eq!(g.class_of(&m, fa), g.class_of(&m, fc));
        let core = g.explain(&m, fa, fc);
        // Explanation of f(a)≈f(c) recurses to a≈c, giving both a=b and b=c.
        assert_eq!(core, alloc::vec![0, 1]);
        assert!(explanation_is_sound(&m, &eqs, &[fa, fc], &core, fa, fc));
    }

    #[test]
    fn explain_minimal_ignores_irrelevant() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        let d = constant(&mut m, "d", s);
        let e = constant(&mut m, "e", s);
        // a=b (0), b=c (1), plus irrelevant d=e (2). Explain a≈c.
        let eqs = [(0usize, a, b), (1usize, b, c), (2usize, d, e)];
        let mut g = ProofEgraph::new(&m, &[a, b, c, d, e]);
        g.assert_eqs(&m, &eqs);
        let core = g.explain(&m, a, c);
        assert_eq!(core, alloc::vec![0, 1]); // id 2 (d=e) is not on the path
        assert!(explanation_is_sound(&m, &eqs, &[a, b, c], &core, a, c));
    }

    #[test]
    fn explain_two_arg_congruence() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        let d = constant(&mut m, "d", s);
        let g2 = m.mk_func_decl(Symbol::new("g"), &[s, s], s);
        let gac = m.mk_app(g2, &[a, c]);
        let gbd = m.mk_app(g2, &[b, d]);
        // a=b (0), c=d (1) ⇒ g(a,c)=g(b,d). Diseq g(a,c)≠g(b,d).
        let eqs = [(0usize, a, b), (1usize, c, d)];
        let mut g = ProofEgraph::new(&m, &[gac, gbd]);
        g.assert_eqs(&m, &eqs);
        assert_eq!(g.class_of(&m, gac), g.class_of(&m, gbd));
        let core = g.explain(&m, gac, gbd);
        assert_eq!(core, alloc::vec![0, 1]);
        assert!(explanation_is_sound(&m, &eqs, &[gac, gbd], &core, gac, gbd));
    }

    #[test]
    fn explain_nested_congruence() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[s], s);
        let fa = m.mk_app(f, &[a]);
        let fb = m.mk_app(f, &[b]);
        let ffa = m.mk_app(f, &[fa]);
        let ffb = m.mk_app(f, &[fb]);
        // a=b (0) ⇒ f(a)=f(b) ⇒ f(f(a))=f(f(b)).
        let eqs = [(0usize, a, b)];
        let mut g = ProofEgraph::new(&m, &[ffa, ffb]);
        g.assert_eqs(&m, &eqs);
        assert_eq!(g.class_of(&m, ffa), g.class_of(&m, ffb));
        let core = g.explain(&m, ffa, ffb);
        assert_eq!(core, alloc::vec![0]);
        assert!(explanation_is_sound(&m, &eqs, &[ffa, ffb], &core, ffa, ffb));
    }
}
