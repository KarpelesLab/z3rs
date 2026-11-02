//! A backtrackable congruence closure for **online** DPLL(T) — the EUF core of
//! `z3/src/smt/smt_context.cpp` (`add_eq` / `undo_add_eq` / `invert_trans`,
//! Z3 4.17.0, MIT) driven from inside the SAT search.
//!
//! The e-graph follows the SAT trail: every theory literal the search assigns is
//! asserted (an equality atom merges its sides, a predicate atom merges its term
//! with `true`/`false`), and every backtrack undoes exactly the merges made
//! since, from an undo trail. While asserting it
//!
//! * **detects conflicts on partial assignments** — an equality atom assigned
//!   `false` whose sides are already congruent, or a class that would contain two
//!   distinct interpreted values (numerals, or `true` and `false`), and
//! * **propagates** the equality atoms whose sides merge (and predicate atoms
//!   whose term joins the `true`/`false` class),
//!
//! each with an explanation read off the proof forest (`m_trans` in z3): the
//! asserted literals whose merges, closed under congruence, force the equality.
//! It is incomplete only where the offline final check (`theory_check`) takes
//! over — the arithmetic and theory-combination reasoning — so it can only make
//! the search faster, never change its verdict.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use puremp::Rational;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;
use crate::sat::literal::Lit;
use crate::sat::solver::{TheoryCtx, TheoryHook, TheoryProp};
use crate::util::lbool::LBool;

/// "No node" marker for the proof forest.
const NONE: usize = usize::MAX;

/// Why two nodes were merged (z3's `eq_justification`).
#[derive(Clone, Copy)]
enum Just {
    /// An asserted literal (currently true).
    Lit(Lit),
    /// Congruence of the two applications (same declaration, arguments
    /// pairwise equal).
    Cong(usize, usize),
}

/// An interpreted value: two classes carrying different ones cannot merge.
#[derive(Clone, PartialEq)]
enum Val {
    Num(Rational),
    Bool(bool),
}

/// A theory atom the e-graph watches.
#[derive(Clone, Copy)]
enum Atom {
    /// `lit ⇔ a = b`.
    Eq(Lit, usize, usize),
    /// `lit ⇔ t` for a Boolean application `t`.
    Pred(Lit, usize),
}

/// One undoable step.
enum Undo {
    /// `r1`'s class was merged into `r2`'s through the proof edge `n1 → …`.
    Merge {
        r1: usize,
        r2: usize,
        n1: usize,
        parents_len: usize,
        watch_len: usize,
        value: Option<usize>,
    },
    /// A congruence-table entry was inserted.
    CgInsert((AstId, Vec<usize>)),
    /// A congruence-table entry (for the node) was removed.
    CgRemove((AstId, Vec<usize>), usize),
}

/// The backtrackable e-graph plus its link to the SAT trail.
pub struct IncEgraph {
    ids: BTreeMap<AstId, usize>,
    /// `(decl, argument nodes)` of each application node.
    sig: Vec<Option<(AstId, Vec<usize>)>>,
    /// Union-find root (no path compression: undone by relabelling).
    root: Vec<usize>,
    /// Circular list of each class's members.
    next: Vec<usize>,
    size: Vec<usize>,
    /// At a root: the applications with an argument in the class.
    parents: Vec<Vec<usize>>,
    /// At a root: the atoms with a side (or term) in the class.
    watch: Vec<Vec<usize>>,
    /// At a root: a node of the class carrying an interpreted value.
    value: Vec<Option<usize>>,
    /// Each node's own interpreted value.
    val: Vec<Option<Val>>,
    /// Congruence table: signature over argument roots → representative.
    cg: BTreeMap<(AstId, Vec<usize>), usize>,
    /// Proof forest (z3's `m_trans`): `target[n]` and the justification.
    target: Vec<usize>,
    just: Vec<Just>,
    stamp: Vec<u64>,
    epoch: u64,
    atoms: Vec<Atom>,
    /// Atoms per SAT variable.
    var_atoms: Vec<Vec<usize>>,
    undo: Vec<Undo>,
    pending: Vec<(usize, usize, Just)>,
    /// The `true` / `false` nodes.
    t_node: usize,
    f_node: usize,
    /// Number of SAT-trail literals asserted, and per asserted trail position
    /// the undo-trail length before it.
    processed: usize,
    marks: Vec<(usize, usize)>,
    /// Implications found while asserting (literal, explanation).
    implied: Vec<(Lit, Vec<Lit>)>,
    conflict: Option<Vec<Lit>>,
    /// Each node's term (`None` for the `true` / `false` nodes), and whether
    /// it is arithmetic-sorted.
    term: Vec<Option<AstId>>,
    arith: Vec<bool>,
    /// The trail position being asserted.
    cur_pos: usize,
    /// Equalities between arithmetic terms found by congruence, for the
    /// arithmetic theory (`z3`'s `new_eq_eh`): `(trail position, a, b,
    /// explanation)`, kept in position order for the asserted trail prefix.
    pub eq_log: Vec<(usize, AstId, AstId, Vec<Lit>)>,
}

impl IncEgraph {
    /// An e-graph over every subterm of `roots`, watching the equality atoms
    /// `eqs` (`lit ⇔ a = b`) and the predicate atoms `preds` (`lit ⇔ t`).
    pub fn new(
        m: &AstManager,
        roots: &[AstId],
        eqs: &[(Lit, AstId, AstId)],
        preds: &[(Lit, AstId)],
    ) -> IncEgraph {
        let mut g = IncEgraph {
            ids: BTreeMap::new(),
            sig: Vec::new(),
            root: Vec::new(),
            next: Vec::new(),
            size: Vec::new(),
            parents: Vec::new(),
            watch: Vec::new(),
            value: Vec::new(),
            val: Vec::new(),
            cg: BTreeMap::new(),
            target: Vec::new(),
            just: Vec::new(),
            stamp: Vec::new(),
            epoch: 0,
            atoms: Vec::new(),
            var_atoms: Vec::new(),
            undo: Vec::new(),
            pending: Vec::new(),
            t_node: 0,
            f_node: 0,
            processed: 0,
            marks: Vec::new(),
            implied: Vec::new(),
            conflict: None,
            term: Vec::new(),
            arith: Vec::new(),
            cur_pos: 0,
            eq_log: Vec::new(),
        };
        g.t_node = g.add_node(None, Some(Val::Bool(true)));
        g.f_node = g.add_node(None, Some(Val::Bool(false)));
        for t in m.postorder_many(roots) {
            g.intern(m, t);
        }
        for &(lit, a, b) in eqs {
            let (x, y) = (g.intern(m, a), g.intern(m, b));
            g.add_atom(lit, Atom::Eq(lit, x, y), &[x, y]);
        }
        for &(lit, t) in preds {
            let x = g.intern(m, t);
            g.add_atom(lit, Atom::Pred(lit, x), &[x]);
        }
        // Congruences among the initial terms are permanent (never undone).
        g.drain(&|_| LBool::Undef);
        g.implied.clear();
        g.conflict = None;
        g
    }

    fn add_atom(&mut self, lit: Lit, atom: Atom, nodes: &[usize]) {
        let id = self.atoms.len();
        self.atoms.push(atom);
        let v = lit.var() as usize;
        if self.var_atoms.len() <= v {
            self.var_atoms.resize(v + 1, Vec::new());
        }
        self.var_atoms[v].push(id);
        for &n in nodes {
            if !self.watch[n].contains(&id) {
                self.watch[n].push(id);
            }
        }
    }

    fn add_node(&mut self, sig: Option<(AstId, Vec<usize>)>, val: Option<Val>) -> usize {
        let id = self.root.len();
        self.root.push(id);
        self.next.push(id);
        self.size.push(1);
        self.parents.push(Vec::new());
        self.watch.push(Vec::new());
        self.value.push(val.as_ref().map(|_| id));
        self.val.push(val);
        self.target.push(NONE);
        self.just.push(Just::Cong(id, id));
        self.stamp.push(0);
        self.term.push(None);
        self.arith.push(false);
        if let Some((decl, args)) = &sig {
            let key = (*decl, args.clone());
            for &a in args {
                if !self.parents[a].contains(&id) {
                    self.parents[a].push(id);
                }
            }
            // Fresh terms have distinct signatures except for hash-consing
            // misses; a clash is merged by congruence at the first pass.
            match self.cg.get(&key) {
                Some(&q) => self.pending.push((id, q, Just::Cong(id, q))),
                None => {
                    self.cg.insert(key, id);
                }
            }
        }
        self.sig.push(sig);
        id
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
        let val = if m.is_true(t) {
            Some(Val::Bool(true))
        } else if m.is_false(t) {
            Some(Val::Bool(false))
        } else {
            m.as_numeral(t).map(Val::Num)
        };
        let id = self.add_node(sig, val);
        self.ids.insert(t, id);
        self.term[id] = Some(t);
        self.arith[id] = m.is_arith_sort(m.get_sort(t));
        id
    }

    /// The signature of application `p` over the current roots.
    fn key(&self, p: usize) -> Option<(AstId, Vec<usize>)> {
        let (decl, args) = self.sig[p].as_ref()?;
        Some((*decl, args.iter().map(|&a| self.root[a]).collect()))
    }

    /// Make `n` the root of its proof tree (z3 `invert_trans`).
    fn invert_trans(&mut self, n: usize) {
        let mut curr = self.target[n];
        let mut prev = n;
        let mut js = self.just[n];
        self.target[n] = NONE;
        while curr != NONE {
            let new_curr = self.target[curr];
            let new_js = self.just[curr];
            self.target[curr] = prev;
            self.just[curr] = js;
            prev = curr;
            js = new_js;
            curr = new_curr;
        }
    }

    /// Merge the classes of `a` and `b` (z3 `add_eq`), recording conflicts and
    /// implications.
    fn merge(&mut self, a: usize, b: usize, j: Just, val: &dyn Fn(Lit) -> LBool) {
        let (mut a, mut b) = (a, b);
        let (mut r1, mut r2) = (self.root[a], self.root[b]);
        if r1 == r2 {
            return;
        }
        if self.size[r1] > self.size[r2] {
            core::mem::swap(&mut a, &mut b);
            core::mem::swap(&mut r1, &mut r2);
        }
        // Remove r1's parents from the congruence table.
        let r1_parents = self.parents[r1].clone();
        for &p in &r1_parents {
            if let Some(key) = self.key(p)
                && self.cg.get(&key) == Some(&p)
            {
                self.cg.remove(&key);
                self.undo.push(Undo::CgRemove(key, p));
            }
        }
        // Proof forest: a becomes the root of its tree, then hangs under b.
        self.invert_trans(a);
        self.target[a] = b;
        self.just[a] = j;
        // Relabel r1's class and splice the member lists.
        let mut c = r1;
        loop {
            self.root[c] = r2;
            c = self.next[c];
            if c == r1 {
                break;
            }
        }
        self.next.swap(r1, r2);
        self.size[r2] += self.size[r1];
        let (v1, v2) = (self.value[r1], self.value[r2]);
        self.undo.push(Undo::Merge {
            r1,
            r2,
            n1: a,
            parents_len: self.parents[r2].len(),
            watch_len: self.watch[r2].len(),
            value: v2,
        });
        // Reinsert r1's parents; a signature clash is a new congruence.
        for &p in &r1_parents {
            let Some(key) = self.key(p) else { continue };
            match self.cg.get(&key) {
                None => {
                    self.cg.insert(key.clone(), p);
                    self.undo.push(Undo::CgInsert(key));
                }
                Some(&q) => {
                    if self.root[q] != self.root[p] {
                        self.pending.push((p, q, Just::Cong(p, q)));
                    }
                }
            }
        }
        self.parents[r2].extend(r1_parents);
        // Interpreted values: two different ones in one class clash.
        match (v1, v2) {
            (Some(x), Some(y)) => {
                if self.val[x] != self.val[y] && self.conflict.is_none() {
                    self.conflict = Some(self.explain(x, y));
                }
            }
            (Some(x), None) => self.value[r2] = Some(x),
            _ => {}
        }
        // Watched atoms of r1: equalities whose sides are now congruent.
        let w1 = self.watch[r1].clone();
        for &id in &w1 {
            if let Atom::Eq(lit, x, y) = self.atoms[id]
                && self.root[x] == self.root[y]
                && val(lit) != LBool::True
            {
                let why = self.explain(x, y);
                self.implied.push((lit, why));
            }
        }
        // A class joining `true`/`false`: its predicates take that value.
        let bool_val = |g: &Self, v: Option<usize>| match v.and_then(|n| g.val[n].clone()) {
            Some(Val::Bool(bv)) => Some(bv),
            _ => None,
        };
        let joined = match (bool_val(self, v1), bool_val(self, v2)) {
            (None, Some(bv)) => Some((self.watch[r1].clone(), bv)),
            (Some(bv), None) => Some((self.watch[r2].clone(), bv)),
            _ => None,
        };
        if let Some((ws, bv)) = joined {
            let vnode = if bv { self.t_node } else { self.f_node };
            for id in ws {
                if let Atom::Pred(lit, t) = self.atoms[id] {
                    let l = if bv { lit } else { !lit };
                    if val(l) != LBool::True {
                        let why = self.explain(t, vnode);
                        self.implied.push((l, why));
                    }
                }
            }
        }
        self.watch[r2].extend(w1);
        // A congruence between arithmetic terms is news to the arithmetic.
        if let Just::Cong(..) = j
            && self.arith[a]
            && let (Some(ta), Some(tb)) = (self.term[a], self.term[b])
        {
            let why = self.explain(a, b);
            self.eq_log.push((self.cur_pos, ta, tb, why));
        }
    }

    /// Undo the trail down to length `len`.
    fn undo_to(&mut self, len: usize) {
        while self.undo.len() > len {
            match self.undo.pop().unwrap() {
                Undo::CgInsert(key) => {
                    self.cg.remove(&key);
                }
                Undo::CgRemove(key, p) => {
                    self.cg.insert(key, p);
                }
                Undo::Merge {
                    r1,
                    r2,
                    n1,
                    parents_len,
                    watch_len,
                    value,
                } => {
                    self.value[r2] = value;
                    self.watch[r2].truncate(watch_len);
                    self.parents[r2].truncate(parents_len);
                    self.size[r2] -= self.size[r1];
                    self.next.swap(r1, r2);
                    let mut c = r1;
                    loop {
                        self.root[c] = r1;
                        c = self.next[c];
                        if c == r1 {
                            break;
                        }
                    }
                    self.target[n1] = NONE;
                    self.invert_trans(r1);
                }
            }
        }
    }

    /// The asserted literals whose merges (closed under congruence) make `a`
    /// and `b` equal. Precondition: same class.
    fn explain(&mut self, a: usize, b: usize) -> Vec<Lit> {
        let mut out: BTreeSet<Lit> = BTreeSet::new();
        let mut work: Vec<(usize, usize)> = alloc::vec![(a, b)];
        let mut done: BTreeSet<(usize, usize)> = BTreeSet::new();
        while let Some((x, y)) = work.pop() {
            if x == y || !done.insert((x.min(y), x.max(y))) {
                continue;
            }
            // Nearest common ancestor in the proof tree.
            self.epoch += 1;
            let e = self.epoch;
            let mut n = x;
            while n != NONE {
                self.stamp[n] = e;
                n = self.target[n];
            }
            let mut anc = y;
            while anc != NONE && self.stamp[anc] != e {
                anc = self.target[anc];
            }
            for start in [x, y] {
                let mut n = start;
                while n != anc && n != NONE {
                    match self.just[n] {
                        Just::Lit(l) => {
                            out.insert(l);
                        }
                        Just::Cong(p, q) => {
                            if let (Some((_, ap)), Some((_, aq))) = (&self.sig[p], &self.sig[q]) {
                                work.extend(ap.iter().copied().zip(aq.iter().copied()));
                            }
                        }
                    }
                    n = self.target[n];
                }
            }
        }
        out.into_iter().collect()
    }

    /// Process pending congruence merges until none remain or a conflict.
    fn drain(&mut self, val: &dyn Fn(Lit) -> LBool) {
        while self.conflict.is_none() {
            let Some((a, b, j)) = self.pending.pop() else {
                break;
            };
            self.merge(a, b, j, val);
        }
    }

    /// Assert the theory literal `l` (currently true).
    fn assert_lit(&mut self, l: Lit, val: &dyn Fn(Lit) -> LBool) {
        let v = l.var() as usize;
        let Some(ids) = self.var_atoms.get(v) else {
            return;
        };
        for id in ids.clone() {
            match self.atoms[id] {
                Atom::Eq(lit, x, y) => {
                    if l == lit {
                        self.merge(x, y, Just::Lit(l), val);
                    } else if self.root[x] == self.root[y] {
                        // A disequality between congruent terms: imply the
                        // (false) equality, which the solver sees as a conflict.
                        let why = self.explain(x, y);
                        self.implied.push((lit, why));
                    }
                }
                Atom::Pred(lit, t) => {
                    let to = if l == lit { self.t_node } else { self.f_node };
                    self.merge(t, to, Just::Lit(l), val);
                }
            }
            self.drain(val);
            if self.conflict.is_some() {
                return;
            }
        }
    }
}

impl TheoryHook for IncEgraph {
    fn propagate(&mut self, ctx: &TheoryCtx<'_>) -> TheoryProp {
        let val = |l: Lit| ctx.value(l);
        // Backtrack to the part of the trail that is unchanged.
        if ctx.stable < self.processed {
            let k = self.marks.partition_point(|&(pos, _)| pos < ctx.stable);
            if k < self.marks.len() {
                let len = self.marks[k].1;
                self.undo_to(len);
                self.marks.truncate(k);
            }
            self.processed = ctx.stable;
            let keep = self.eq_log.partition_point(|e| e.0 < ctx.stable);
            self.eq_log.truncate(keep);
        }
        self.pending.clear();
        self.implied.clear();
        self.conflict = None;
        let first_mark = self.marks.len();
        let start = self.processed;
        let trail = ctx.trail;
        for (pos, &l) in trail.iter().enumerate().skip(start) {
            if self
                .var_atoms
                .get(l.var() as usize)
                .is_some_and(|a| !a.is_empty())
            {
                self.marks.push((pos, self.undo.len()));
                self.cur_pos = pos;
                self.assert_lit(l, &val);
                if self.conflict.is_some() {
                    break;
                }
            }
        }
        self.processed = trail.len();
        let conflict = self.conflict.take().filter(|c| !c.is_empty());
        if conflict.is_some() {
            // The solver backjumps below this pass; forget it now so a partial
            // state never lingers.
            if first_mark < self.marks.len() {
                let len = self.marks[first_mark].1;
                self.undo_to(len);
                self.marks.truncate(first_mark);
            }
            self.processed = start;
            self.pending.clear();
            let keep = self.eq_log.partition_point(|e| e.0 < start);
            self.eq_log.truncate(keep);
        }
        let implied = if conflict.is_some() {
            Vec::new()
        } else {
            core::mem::take(&mut self.implied)
                .into_iter()
                .filter(|(_, why)| !why.is_empty())
                .collect()
        };
        TheoryProp { implied, conflict }
    }
}
