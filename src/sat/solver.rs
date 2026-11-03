//! A conflict-driven clause-learning (CDCL) SAT solver.
//!
//! MiniSat-style core ported in spirit from `z3/src/sat/sat_solver.{h,cpp}`
//! (Z3 4.17.0, MIT): two-watched-literal propagation, 1-UIP conflict analysis
//! with clause learning, non-chronological backjumping, VSIDS decision
//! heuristic, and Luby restarts. Learnt-clause DB reduction and in-processing
//! come later.

use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, Ordering};

use crate::sat::literal::{Lit, Var};
use crate::util::lbool::LBool;

/// The result of a satisfiability check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SatResult {
    /// Satisfiable — a model is available via [`Solver::value`].
    Sat,
    /// Unsatisfiable.
    Unsat,
}

/// The initial decision phase of fresh variables, shared by the solvers of one
/// context: when set, fresh variables are first decided `false` (z3's default
/// phase, `smt.phase_selection` with a `false` initial phase) instead of
/// `true`. A context sets it around the searches whose models only steer
/// quantifier instantiation, so the models of other checks are unchanged.
///
/// Every [`Solver`] built with [`Solver::with_initial_phase`] from the same
/// handle reads its current value when it allocates a variable; solvers of
/// other contexts (other threads) keep their own handles and are unaffected.
#[derive(Clone, Debug, Default)]
pub struct InitialPhase(Arc<AtomicBool>);

impl InitialPhase {
    /// Whether fresh variables are first decided `false`.
    #[inline]
    pub fn decide_false_first(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    /// Set whether fresh variables are first decided `false`, returning the
    /// previous setting (for the caller to restore).
    #[inline]
    pub fn set_decide_false_first(&self, value: bool) -> bool {
        self.0.swap(value, Ordering::Relaxed)
    }
}

/// Sentinel `reason`: a decision literal or a top-level fact (no antecedent).
const REASON_NONE: i32 = -1;

/// Chronological backtracking: a conflict whose backjump would undo more
/// than this many decision levels backtracks one level instead, the
/// asserting literal taking its level out of order (Nadel & Ryvchin, "Chronological
/// Backtracking", SAT 2018; as in CaDiCaL's `chrono`).
const CHRONO_LEVELS: u32 = 100;

/// Value of literal `l` under the raw per-variable assignment `assign` — the
/// free-function form of [`Solver::lit_value`], so a [`TheoryHook`] closure can
/// read the current assignment without borrowing the solver through a method.
#[inline]
fn lit_value_from(assign: &[LBool], l: Lit) -> LBool {
    match assign[l.var() as usize] {
        LBool::Undef => LBool::Undef,
        LBool::True => LBool::from_bool(!l.sign()),
        LBool::False => LBool::from_bool(l.sign()),
    }
}

/// Theory implications and/or a conflict discovered at a propagation fixpoint,
/// returned by [`TheoryHook::propagate`].
pub struct TheoryProp {
    /// `(p, reason)` pairs: literal `p` is theory-implied by the conjunction of
    /// `reason`, whose literals must ALL currently be true. The solver
    /// materializes the globally-valid clause `(p ∨ ¬reason…)` and enqueues `p`.
    pub implied: Vec<(Lit, Vec<Lit>)>,
    /// A set of currently-true literals that are jointly theory-inconsistent.
    /// The solver materializes `¬conflict` (all-false) and runs 1-UIP analysis.
    pub conflict: Option<Vec<Lit>>,
}

/// A theory participating in online DPLL(T) propagation. The SAT solver calls
/// [`TheoryHook::propagate`] whenever Boolean propagation reaches a fixpoint,
/// before branching — mirroring z3's `extension::unit_propagate`
/// (`sat/sat_solver.cpp:989-1011`, gated by `should_propagate` `:1847`).
///
/// SOUNDNESS CONTRACT: every returned implication `(p, R)` must have all of `R`
/// currently true and `R` must genuinely theory-entail `p`; every returned
/// `conflict` must be currently-true literals that are jointly theory-
/// inconsistent. The solver turns these into learnt clauses that conflict
/// analysis resolves through, so an unsound return is an unsound lemma —
/// implementers MUST independently verify each implication/conflict.
pub trait TheoryHook {
    /// Called at the Boolean fixpoint with a view of the current assignment.
    fn propagate(&mut self, ctx: &TheoryCtx<'_>) -> TheoryProp;
}

/// The solver state a [`TheoryHook`] sees: the assignment trail, and how much of
/// it is unchanged since the previous call (so an incremental theory asserts
/// only the new literals and undoes what was backtracked).
pub struct TheoryCtx<'a> {
    /// The assigned literals, in assignment order.
    pub trail: &'a [Lit],
    /// Length of the trail prefix that has stayed assigned since the previous
    /// call (literals beyond it were retracted or are new).
    pub stable: usize,
    assign: &'a [LBool],
}

impl TheoryCtx<'_> {
    /// The current value of `l`.
    #[inline]
    pub fn value(&self, l: Lit) -> LBool {
        lit_value_from(self.assign, l)
    }
}

/// Outcome of one theory-propagation pass (see [`Solver::theory_pass`]).
enum TheoryPass {
    /// A conflict clause was materialized; its index is ready for `analyze`.
    Conflict(usize),
    /// At least one literal was enqueued — re-run Boolean propagation.
    Progress,
    /// Nothing to do — safe to branch.
    Idle,
    /// A valid literal is false at level 0.
    Unsat,
}

/// A CDCL SAT solver.
pub struct Solver {
    assign: Vec<LBool>,
    level: Vec<u32>,
    /// Antecedent clause index for an implied literal, or [`REASON_NONE`].
    reason: Vec<i32>,
    /// Saved polarity for phase saving.
    polarity: Vec<bool>,
    /// The initial phase of fresh variables (see [`InitialPhase`]).
    initial_phase: InitialPhase,
    activity: Vec<f64>,
    var_inc: f64,
    /// Decision order: a binary max-heap of variables by (activity desc, index
    /// asc) — the port of MiniSat/z3's `var_queue`. It may hold assigned
    /// variables (dropped lazily when popped); every unassigned variable is in
    /// it. `heap_pos[v]` is `v`'s slot, or `-1` when absent.
    heap: Vec<Var>,
    heap_pos: Vec<i32>,
    /// Scratch `seen` marks for [`Solver::analyze`], kept all-false between calls.
    seen: Vec<bool>,

    clauses: Vec<Vec<Lit>>,
    /// `watches[l.index()]` = clauses watching literal `~l` (MiniSat convention).
    watches: Vec<Vec<Watch>>,
    /// Per-clause: is it a learnt clause (deletable), its activity, and whether
    /// it has been lazily deleted (skipped in propagation, freed).
    learnt: Vec<bool>,
    cla_activity: Vec<f64>,
    deleted: Vec<bool>,
    cla_inc: f64,
    /// Number of live (non-deleted) learnt clauses, and the current cap.
    n_learnt: usize,
    max_learnt: usize,

    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    /// Length of the trail prefix unchanged since the last theory pass (the
    /// [`TheoryCtx::stable`] low-water mark, lowered by every backtrack).
    theory_stable: usize,

    /// Clauses added above decision level 0 in resumable mode (see
    /// [`Solver::set_resumable`]), not yet attached: the search attaches each
    /// against the assignment it meets, backjumping where it is unit or
    /// conflicting.
    pending: VecDeque<Vec<Lit>>,
    /// Keep the assignment across searches and add clauses mid-search, and
    /// backtrack chronologically (see [`CHRONO_LEVELS`]): the trail is then
    /// ordered by assignment, not by level, and an implied literal's level is
    /// its antecedent's highest.
    resumable: bool,
    /// When set, the variables a theory watches (see
    /// [`Solver::watch_theory_var`]): a theory pass is skipped while the trail
    /// gained none of them and lost nothing.
    theory_vars: Option<Vec<bool>>,
    /// The trail length at the last theory pass.
    theory_seen: usize,
    /// The backjump distance past which a conflict backtracks
    /// chronologically ([`CHRONO_LEVELS`]).
    chrono_levels: u32,
    /// Conflicts over every search so far (see [`Solver::conflicts`]).
    conflicts: u64,

    ok: bool,
}

/// A watch-list entry: the clause, and a literal of it whose truth shows the
/// clause satisfied without reading it (MiniSat's blocker).
#[derive(Clone, Copy)]
struct Watch {
    cref: usize,
    blocker: Lit,
}

/// What attaching a pending clause did (see [`Solver::attach_pending`]).
enum PendingStep {
    /// Every pending clause is attached, none unit or conflicting.
    Idle,
    /// A literal was enqueued (after a backjump): propagate it.
    Progress,
    /// A clause is false at the current level: analyze it.
    Conflict(usize),
    /// A clause is false at level 0.
    Unsat,
}

impl Default for Solver {
    fn default() -> Solver {
        Solver::new()
    }
}

impl Solver {
    /// A new, empty solver whose fresh variables follow `phase` (shared with
    /// the other solvers of a context; see [`InitialPhase`]).
    pub fn with_initial_phase(phase: InitialPhase) -> Solver {
        let mut s = Solver::new();
        s.initial_phase = phase;
        s
    }

    /// A new, empty solver.
    pub fn new() -> Solver {
        Solver {
            assign: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            polarity: Vec::new(),
            initial_phase: InitialPhase::default(),
            activity: Vec::new(),
            var_inc: 1.0,
            heap: Vec::new(),
            heap_pos: Vec::new(),
            seen: Vec::new(),
            clauses: Vec::new(),
            watches: Vec::new(),
            learnt: Vec::new(),
            cla_activity: Vec::new(),
            deleted: Vec::new(),
            cla_inc: 1.0,
            n_learnt: 0,
            max_learnt: 2000,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            theory_stable: 0,
            pending: VecDeque::new(),
            resumable: false,
            theory_vars: None,
            theory_seen: 0,
            chrono_levels: CHRONO_LEVELS,
            conflicts: 0,
            ok: true,
        }
    }

    /// The number of variables.
    #[inline]
    pub fn num_vars(&self) -> usize {
        self.assign.len()
    }

    /// Allocate a fresh variable.
    pub fn mk_var(&mut self) -> Var {
        let v = self.assign.len() as Var;
        self.assign.push(LBool::Undef);
        self.level.push(0);
        self.reason.push(REASON_NONE);
        self.polarity.push(self.initial_phase.decide_false_first());
        self.activity.push(0.0);
        self.heap_pos.push(-1);
        self.seen.push(false);
        self.heap_insert(v);
        self.watches.push(Vec::new()); // for the positive literal
        self.watches.push(Vec::new()); // for the negative literal
        v
    }

    /// Decide `v` as `value` first (until phase saving overrides it).
    pub fn set_phase(&mut self, v: Var, value: bool) {
        self.ensure_var(v);
        self.polarity[v as usize] = !value;
    }

    fn ensure_var(&mut self, v: Var) {
        while (self.assign.len() as Var) <= v {
            self.mk_var();
        }
    }

    #[inline]
    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    #[inline]
    fn lit_value(&self, l: Lit) -> LBool {
        match self.assign[l.var() as usize] {
            LBool::Undef => LBool::Undef,
            LBool::True => LBool::from_bool(!l.sign()),
            LBool::False => LBool::from_bool(l.sign()),
        }
    }

    /// The value assigned to `v` (meaningful after [`SatResult::Sat`]).
    #[inline]
    pub fn value(&self, v: Var) -> LBool {
        self.assign[v as usize]
    }

    /// Whether literal `l` is true in the current model.
    #[inline]
    pub fn model_holds(&self, l: Lit) -> bool {
        self.lit_value(l) == LBool::True
    }

    /// Keep the assignment of a search for the next one, as z3's and
    /// MiniSat's incremental searches do: a clause added above decision level
    /// 0 is queued instead of backtracking to level 0, and the next search
    /// resumes from the current assignment, attaching each queued clause where
    /// it stands — backjumping to the level where it becomes unit (and
    /// propagating it) or conflicting (and analyzing it).
    pub fn set_resumable(&mut self) {
        self.resumable = true;
    }

    /// Declare `v` a variable the theory of [`Solver::solve_with_theory`]
    /// watches. Once any is declared, the theory is consulted only when the
    /// trail gained a declared variable or was backtracked since its last
    /// pass (z3 calls a theory only on its own atoms' assignments).
    pub fn watch_theory_var(&mut self, v: Var) {
        self.ensure_var(v);
        let tv = self.theory_vars.get_or_insert_with(Vec::new);
        if tv.len() <= v as usize {
            tv.resize(v as usize + 1, false);
        }
        tv[v as usize] = true;
    }

    /// Make the next theory pass see the whole trail as new (a theory rebuilt
    /// from scratch asserts it again).
    pub fn reset_theory(&mut self) {
        self.theory_stable = 0;
        self.theory_seen = usize::MAX;
    }

    /// Does the next theory pass have anything to see: a watched variable
    /// assigned, or an assignment retracted, since the last one?
    fn theory_due(&self) -> bool {
        let Some(tv) = &self.theory_vars else {
            return true;
        };
        self.theory_stable < self.theory_seen
            || self.trail[self.theory_stable.min(self.trail.len())..]
                .iter()
                .any(|l| tv.get(l.var() as usize).copied().unwrap_or(false))
    }

    /// Add a clause. Duplicate literals are merged, tautologies dropped, and an
    /// empty clause makes the problem unsatisfiable.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        if !self.ok {
            return;
        }
        if self.resumable && self.decision_level() > 0 {
            for &l in lits {
                self.ensure_var(l.var());
            }
            let mut ps: Vec<Lit> = lits.to_vec();
            ps.sort_by_key(|l| l.index());
            ps.dedup();
            if ps.windows(2).any(|w| w[0].var() == w[1].var()) {
                return;
            }
            if ps.is_empty() {
                self.ok = false;
            } else {
                self.pending.push_back(ps);
            }
            return;
        }
        // Clauses are added at decision level 0. After a prior `solve()` the trail
        // still holds that call's (possibly non-level-0) assignment; a unit clause
        // enqueued against it could conflict with a *decision* — not a real
        // level-0 fact — and wrongly set `ok = false`, permanently killing the
        // solver (a spurious `unsat` on the next `solve()`). Backtracking to level
        // 0 first ensures a unit enqueues against the persistent level-0
        // assignment, and non-unit clauses are re-propagated cleanly on `solve()`.
        self.cancel_until(0);
        for &l in lits {
            self.ensure_var(l.var());
        }
        // Normalize: sort by index, drop duplicates, detect x ∧ ¬x tautology.
        let mut ps: Vec<Lit> = lits.to_vec();
        ps.sort_by_key(|l| l.index());
        ps.dedup();
        for w in ps.windows(2) {
            if w[0].var() == w[1].var() {
                return; // x and ¬x adjacent after sort → tautology
            }
        }

        if ps.is_empty() {
            self.ok = false;
        } else if ps.len() == 1 {
            if !self.enqueue(ps[0], REASON_NONE) {
                self.ok = false;
            }
        } else {
            self.attach_clause(ps, false);
        }
    }

    fn attach_clause(&mut self, ps: Vec<Lit>, learnt: bool) {
        let cref = self.clauses.len();
        let (w0, w1) = ((!ps[0]).index() as usize, (!ps[1]).index() as usize);
        let (b0, b1) = (ps[1], ps[0]);
        self.clauses.push(ps);
        self.learnt.push(learnt);
        self.cla_activity.push(0.0);
        self.deleted.push(false);
        self.watches[w0].push(Watch { cref, blocker: b0 });
        self.watches[w1].push(Watch { cref, blocker: b1 });
        if learnt {
            self.n_learnt += 1;
            self.bump_clause(cref);
        }
    }

    /// Bump a clause's activity (rescaling all activities if it overflows).
    fn bump_clause(&mut self, cref: usize) {
        self.cla_activity[cref] += self.cla_inc;
        if self.cla_activity[cref] > 1e100 {
            for a in &mut self.cla_activity {
                *a *= 1e-100;
            }
            self.cla_inc *= 1e-100;
        }
    }

    /// Is clause `cref` the reason for a currently-assigned literal (so it must
    /// not be deleted, to keep the implication graph intact)?
    fn locked(&self, cref: usize) -> bool {
        let c = &self.clauses[cref];
        !c.is_empty()
            && self.lit_value(c[0]) == LBool::True
            && self.reason[c[0].var() as usize] == cref as i32
    }

    /// Delete about half of the low-activity, unlocked learnt clauses when the
    /// learnt DB exceeds its cap. Deletion is lazy: the clause is marked and its
    /// literals freed; `propagate` drops stale watches on encounter. Only learnt
    /// (redundant) clauses are ever removed, so verdicts are unaffected.
    fn reduce_db(&mut self) {
        let mut cand: Vec<usize> = (0..self.clauses.len())
            .filter(|&i| self.learnt[i] && !self.deleted[i] && !self.locked(i))
            .collect();
        // Sort ascending by activity so the least useful come first.
        cand.sort_by(|&a, &b| {
            self.cla_activity[a]
                .partial_cmp(&self.cla_activity[b])
                .unwrap_or(core::cmp::Ordering::Equal)
        });
        let remove = cand.len() / 2;
        for &cref in cand.iter().take(remove) {
            self.deleted[cref] = true;
            self.clauses[cref].clear(); // free the literals; watches drop lazily
            self.n_learnt -= 1;
        }
        self.max_learnt += self.max_learnt / 2; // grow the cap geometrically
    }

    /// Assign `l` true with the given antecedent. Returns `false` on conflict.
    /// Backtracking chronologically, an implied literal takes the highest level
    /// of its antecedent's other literals.
    fn enqueue(&mut self, l: Lit, reason: i32) -> bool {
        let level = if self.resumable && reason >= 0 {
            self.clauses[reason as usize]
                .iter()
                .filter(|&&q| q != l)
                .map(|q| self.level[q.var() as usize])
                .max()
                .unwrap_or(0)
        } else {
            self.decision_level()
        };
        self.enqueue_at(l, reason, level)
    }

    /// Assign `l` true at decision level `level` with the given antecedent.
    /// Returns `false` on conflict.
    fn enqueue_at(&mut self, l: Lit, reason: i32, level: u32) -> bool {
        match self.lit_value(l) {
            LBool::True => true,
            LBool::False => false,
            LBool::Undef => {
                let v = l.var() as usize;
                self.assign[v] = LBool::from_bool(!l.sign());
                self.level[v] = level;
                self.reason[v] = reason;
                self.trail.push(l);
                true
            }
        }
    }

    /// Attach the pending clauses (see [`Solver::set_resumable`]) in order,
    /// against the current assignment, each watching its best two literals.
    /// A unit clause is implied where it stands, at the level of its highest
    /// false literal (backtracking chronologically, no backjump is needed),
    /// and a false clause is a conflict for the search to analyze at its
    /// level.
    fn attach_pending(&mut self) -> PendingStep {
        while let Some(mut c) = self.pending.pop_front() {
            // True literals first (lowest level first), then unassigned ones,
            // then false ones by decreasing level.
            let key = |s: &Solver, l: Lit| -> (u8, i64) {
                let lv = i64::from(s.level[l.var() as usize]);
                match s.lit_value(l) {
                    LBool::True => (0, lv),
                    LBool::Undef => (1, 0),
                    LBool::False => (2, -lv),
                }
            };
            c.sort_by_key(|&l| key(self, l));
            let v0 = self.lit_value(c[0]);
            if c.len() == 1 {
                // A unit clause is a level-0 fact.
                let v = c[0].var() as usize;
                match v0 {
                    LBool::True => {
                        self.level[v] = 0;
                        self.reason[v] = REASON_NONE;
                        continue;
                    }
                    LBool::False if self.level[v] == 0 => {
                        self.ok = false;
                        return PendingStep::Unsat;
                    }
                    LBool::False => self.cancel_until(self.level[v] - 1),
                    LBool::Undef => {}
                }
                self.enqueue_at(c[0], REASON_NONE, 0);
                return PendingStep::Progress;
            }
            let v1 = self.lit_value(c[1]);
            let cref = self.clauses.len();
            if v0 == LBool::True || v1 != LBool::False {
                self.attach_clause(c, false);
            } else if v0 == LBool::Undef {
                let unit = c[0];
                self.attach_clause(c, false);
                self.enqueue(unit, cref as i32);
                return PendingStep::Progress;
            } else {
                self.attach_clause(c, false);
                return PendingStep::Conflict(cref);
            }
        }
        PendingStep::Idle
    }

    /// Propagate all queued assignments. Returns the conflicting clause, if any.
    fn propagate(&mut self) -> Option<usize> {
        let mut confl = None;
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            // Clauses watching ~p (now false) live under watches[p.index()].
            let mut ws = core::mem::take(&mut self.watches[p.index() as usize]);
            let false_lit = !p;
            let mut i = 0;
            'next_clause: while i < ws.len() {
                let Watch { cref, blocker } = ws[i];
                if self.deleted[cref] {
                    ws.swap_remove(i); // drop stale watch of a deleted clause
                    continue;
                }
                if self.lit_value(blocker) == LBool::True {
                    i += 1; // clause satisfied by its blocker; keep watching
                    continue;
                }
                // Ensure the false watched literal is at position 1.
                if self.clauses[cref][0] == false_lit {
                    self.clauses[cref].swap(0, 1);
                }
                let first = self.clauses[cref][0]; // the other watched literal
                if self.lit_value(first) == LBool::True {
                    ws[i].blocker = first;
                    i += 1; // clause already satisfied; keep watching
                    continue;
                }
                // Look for a new, non-false literal to watch.
                let len = self.clauses[cref].len();
                for k in 2..len {
                    let lk = self.clauses[cref][k];
                    if self.lit_value(lk) != LBool::False {
                        self.clauses[cref].swap(1, k);
                        self.watches[(!self.clauses[cref][1]).index() as usize].push(Watch {
                            cref,
                            blocker: first,
                        });
                        ws.swap_remove(i); // stop watching under p
                        continue 'next_clause;
                    }
                }
                // No new watch: `first` is unit, or conflict.
                if self.lit_value(first) == LBool::False {
                    // Conflict: keep the rest of the watch list intact.
                    confl = Some(cref);
                    self.qhead = self.trail.len();
                    break;
                } else {
                    i += 1;
                    self.enqueue(first, cref as i32);
                }
            }
            // Restore the (possibly shortened) watch list.
            let dst = &mut self.watches[p.index() as usize];
            if dst.is_empty() {
                *dst = ws;
            } else {
                dst.append(&mut ws);
            }
            if confl.is_some() {
                break;
            }
        }
        confl
    }

    fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
            // Scaling is monotone, but underflow can merge two activities into
            // a tie that the index then breaks the other way: rebuild the heap.
            self.heap_rebuild();
        } else if self.heap_pos[v] >= 0 {
            self.heap_up(self.heap_pos[v] as usize); // activity only grew
        }
    }

    /// Does `a` come before `b` in decision order? Highest activity first, ties
    /// to the lowest index — the same choice the former linear scan made, so
    /// the search (and every model it yields) is unchanged.
    #[inline]
    fn heap_before(&self, a: Var, b: Var) -> bool {
        let (aa, ab) = (self.activity[a as usize], self.activity[b as usize]);
        aa > ab || (aa == ab && a < b)
    }

    fn heap_insert(&mut self, v: Var) {
        if self.heap_pos[v as usize] >= 0 {
            return;
        }
        self.heap_pos[v as usize] = self.heap.len() as i32;
        self.heap.push(v);
        self.heap_up(self.heap.len() - 1);
    }

    fn heap_up(&mut self, mut i: usize) {
        let v = self.heap[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            let pv = self.heap[parent];
            if !self.heap_before(v, pv) {
                break;
            }
            self.heap[i] = pv;
            self.heap_pos[pv as usize] = i as i32;
            i = parent;
        }
        self.heap[i] = v;
        self.heap_pos[v as usize] = i as i32;
    }

    fn heap_down(&mut self, mut i: usize) {
        let v = self.heap[i];
        let n = self.heap.len();
        loop {
            let l = 2 * i + 1;
            if l >= n {
                break;
            }
            let r = l + 1;
            let c = if r < n && self.heap_before(self.heap[r], self.heap[l]) {
                r
            } else {
                l
            };
            let cv = self.heap[c];
            if !self.heap_before(cv, v) {
                break;
            }
            self.heap[i] = cv;
            self.heap_pos[cv as usize] = i as i32;
            i = c;
        }
        self.heap[i] = v;
        self.heap_pos[v as usize] = i as i32;
    }

    fn heap_pop(&mut self) -> Option<Var> {
        let top = *self.heap.first()?;
        let last = self.heap.pop().unwrap();
        self.heap_pos[top as usize] = -1;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.heap_pos[last as usize] = 0;
            self.heap_down(0);
        }
        Some(top)
    }

    fn heap_rebuild(&mut self) {
        for i in (0..self.heap.len() / 2).rev() {
            self.heap_down(i);
        }
    }

    /// The highest level of the all-false clause `cref` and whether a single
    /// literal has it (then moved to the front, and watched); `None` at level
    /// 0. Backtracking chronologically, a conflict can lie below the current
    /// level.
    fn conflict_level(&mut self, cref: usize) -> Option<(u32, bool)> {
        let c = &self.clauses[cref];
        let lv = |q: &Lit| self.level[q.var() as usize];
        let top = c.iter().map(lv).max().unwrap_or(0);
        if top == 0 {
            return None;
        }
        let at: Vec<usize> = (0..c.len()).filter(|&i| lv(&c[i]) == top).collect();
        if at.len() > 1 {
            return Some((top, false));
        }
        let k = at[0];
        if k >= 2 {
            // Watch the literal at `k` instead of the one at 1.
            let old = (!self.clauses[cref][1]).index() as usize;
            if let Some(i) = self.watches[old].iter().position(|w| w.cref == cref) {
                self.watches[old].swap_remove(i);
            }
            self.clauses[cref].swap(1, k);
            let new = (!self.clauses[cref][1]).index() as usize;
            let blocker = self.clauses[cref][0];
            self.watches[new].push(Watch { cref, blocker });
        }
        if k != 0 {
            self.clauses[cref].swap(0, 1);
        }
        Some((top, true))
    }

    /// 1-UIP conflict analysis. Returns the learnt clause (asserting literal at
    /// index 0) and the level to backjump to.
    fn analyze(&mut self, confl: usize) -> (Vec<Lit>, u32) {
        let cur_level = self.decision_level();
        let mut seen = core::mem::take(&mut self.seen);
        let mut learnt: Vec<Lit> = vec![Lit::pos(0)]; // slot 0 reserved for the UIP
        let mut path_c = 0i32;
        let mut p: Option<Lit> = None;
        let mut confl = confl;
        let mut index = self.trail.len();

        loop {
            if self.learnt[confl] {
                self.bump_clause(confl); // clauses that drive conflicts are useful
            }
            let clause = self.clauses[confl].clone();
            let start = usize::from(p.is_some());
            for &q in &clause[start..] {
                let v = q.var() as usize;
                if !seen[v] && self.level[v] > 0 {
                    self.bump_var(v);
                    seen[v] = true;
                    if self.level[v] >= cur_level {
                        path_c += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            // Next literal to resolve: the most recent `seen` one on the trail.
            index -= 1;
            while {
                let v = self.trail[index].var() as usize;
                !seen[v] || self.level[v] < cur_level
            } {
                index -= 1;
            }
            let pl = self.trail[index];
            seen[pl.var() as usize] = false;
            path_c -= 1;
            p = Some(pl);
            if path_c <= 0 {
                break;
            }
            confl = self.reason[pl.var() as usize] as usize;
        }
        learnt[0] = !p.unwrap();
        // Restore the all-false invariant: the marks left set are exactly the
        // lower-level literals collected into the clause.
        for l in &learnt[1..] {
            seen[l.var() as usize] = false;
        }
        self.seen = seen;

        // Backtrack level = second-highest level in the clause; move that literal
        // to position 1 so the learnt clause watches it.
        let btlevel = if learnt.len() == 1 {
            0
        } else {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[learnt[i].var() as usize] > self.level[learnt[max_i].var() as usize] {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            self.level[learnt[1].var() as usize]
        };
        (learnt, btlevel)
    }

    /// Undo assignments until decision level `level`.
    fn cancel_until(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        let target = self.trail_lim[level as usize];
        // Backtracking chronologically, literals of a level `≤ level` sit
        // above the cut too: they stay assigned, in their order.
        let mut keep: Vec<Lit> = Vec::new();
        while self.trail.len() > target {
            let l = self.trail.pop().unwrap();
            let v = l.var() as usize;
            if self.level[v] <= level && self.resumable {
                keep.push(l);
                continue;
            }
            self.assign[v] = LBool::Undef;
            self.polarity[v] = l.sign(); // phase saving
            self.reason[v] = REASON_NONE;
            self.heap_insert(v as Var);
        }
        self.trail.extend(keep.into_iter().rev());
        self.qhead = target;
        self.theory_stable = self.theory_stable.min(target);
        self.trail_lim.truncate(level as usize);
    }

    /// Pick the unassigned variable with the highest activity (ties to the
    /// lowest index). Assigned variables met on the way are dropped; they
    /// re-enter on backtrack.
    fn pick_branch_var(&mut self) -> Option<Var> {
        while let Some(v) = self.heap_pop() {
            if self.assign[v as usize] == LBool::Undef {
                return Some(v);
            }
        }
        None
    }

    /// Solve. On [`SatResult::Sat`], the assignment is a model.
    pub fn solve(&mut self) -> SatResult {
        self.solve_assumptions(&[])
    }

    /// Solve under a set of `assumptions` (literals forced true for this call
    /// only). Learnt clauses are retained, so repeated calls are incremental.
    /// Each assumption occupies a decision level; a conflict that would have to
    /// undo an assumption yields [`SatResult::Unsat`].
    pub fn solve_assumptions(&mut self, assumptions: &[Lit]) -> SatResult {
        // Unbounded search never runs out of budget, so `None` is impossible.
        self.search(assumptions, u64::MAX, None)
            .unwrap_or(SatResult::Unsat)
    }

    /// Solve, giving up after `max_conflicts` conflicts. Returns `None` when the
    /// budget is exhausted (the caller treats that as `unknown`), so a
    /// hard-but-decidable instance cannot hang the solver.
    pub fn solve_budgeted(&mut self, max_conflicts: u64) -> Option<SatResult> {
        self.search(&[], max_conflicts, None)
    }

    /// Solve with an online DPLL(T) theory: `theory` is consulted at every
    /// Boolean propagation fixpoint (before branching) to propagate implied
    /// literals and detect theory conflicts early. See [`TheoryHook`] for the
    /// soundness contract. Learnt clauses (including materialized theory lemmas)
    /// are retained, so repeated calls remain incremental.
    pub fn solve_with_theory(&mut self, theory: &mut dyn TheoryHook) -> SatResult {
        self.search(&[], u64::MAX, Some(theory))
            .unwrap_or(SatResult::Unsat)
    }

    /// [`Solver::solve_with_theory`], giving up after `max_conflicts`
    /// conflicts (`None`, the caller's `unknown`).
    pub fn solve_with_theory_budgeted(
        &mut self,
        theory: &mut dyn TheoryHook,
        max_conflicts: u64,
    ) -> Option<SatResult> {
        self.search(&[], max_conflicts, Some(theory))
    }

    /// The conflicts met over every search of this solver so far.
    pub fn conflicts(&self) -> u64 {
        self.conflicts
    }

    /// Attach an all-false clause (a theory conflict `¬C`, or a falsified
    /// implication `(p ∨ ¬R)`) and return its index for [`Solver::analyze`].
    /// Returns `None` for a degenerate (<2-literal) clause, which the caller
    /// then ignores rather than mis-handle.
    fn attach_conflict_clause(&mut self, lits: Vec<Lit>) -> Option<usize> {
        if lits.len() < 2 {
            return None;
        }
        for &l in &lits {
            self.ensure_var(l.var());
        }
        // 1-UIP analysis needs a literal of the current level: a lemma that is
        // already false at a lower level first backjumps there (z3 does the
        // same for a theory conflict below the search level).
        let top = lits
            .iter()
            .map(|l| self.level[l.var() as usize])
            .max()
            .unwrap_or(0);
        if top < self.decision_level() {
            self.cancel_until(top);
        }
        // Watch the two highest-level literals, so the clause keeps its watch
        // invariant once the search backjumps.
        let mut lits = lits;
        lits.sort_by_key(|l| core::cmp::Reverse(self.level[l.var() as usize]));
        let cref = self.clauses.len();
        self.attach_clause(lits, true);
        Some(cref)
    }

    /// Run one online theory-propagation pass at the Boolean fixpoint — the port
    /// of z3 `extension::unit_propagate`. For each theory implication `(p, R)`:
    /// `p` already true → nothing; `p` currently false → conflict via the
    /// all-false `(p ∨ ¬R)`; `p` unassigned → materialize `(p ∨ ¬R)` and
    /// `enqueue(p, …)`. A theory `conflict` `C` becomes the all-false `¬C`.
    /// Every clause is a globally-valid theory lemma (the hook's soundness
    /// contract), so conflict analysis resolves through it soundly.
    fn theory_pass(&mut self, th: &mut dyn TheoryHook) -> TheoryPass {
        let prop = th.propagate(&TheoryCtx {
            trail: &self.trail,
            stable: self.theory_stable,
            assign: &self.assign,
        });
        self.theory_stable = self.trail.len();
        self.theory_seen = self.trail.len();
        if let Some(c) = prop.conflict {
            let neg: Vec<Lit> = c.iter().map(|&l| !l).collect();
            if let Some(cref) = self.attach_conflict_clause(neg) {
                return TheoryPass::Conflict(cref);
            }
        }
        let mut progress = false;
        for (p, r) in prop.implied {
            self.ensure_var(p.var());
            match lit_value_from(&self.assign, p) {
                LBool::True => {}
                LBool::False if r.is_empty() => {
                    // A valid literal assigned false: undo that assignment and
                    // assert it as a level-0 fact.
                    let lv = self.level[p.var() as usize];
                    if lv == 0 {
                        self.ok = false;
                        return TheoryPass::Unsat;
                    }
                    self.cancel_until(lv - 1);
                    if self.lit_value(p) == LBool::Undef {
                        self.enqueue_at(p, REASON_NONE, 0);
                    }
                    return TheoryPass::Progress;
                }
                LBool::False => {
                    let mut clause = alloc::vec![p];
                    clause.extend(r.iter().map(|&l| !l));
                    if let Some(cref) = self.attach_conflict_clause(clause) {
                        return TheoryPass::Conflict(cref);
                    }
                }
                LBool::Undef => {
                    let mut clause = alloc::vec![p];
                    clause.extend(r.iter().map(|&l| !l));
                    if clause.len() == 1 {
                        if self.enqueue(p, REASON_NONE) {
                            // A valid literal (empty reason): a level-0 fact to
                            // conflict analysis, which drops it from learnt
                            // clauses instead of looking for its antecedent.
                            self.level[p.var() as usize] = 0;
                            progress = true;
                        }
                    } else {
                        for &l in &clause {
                            self.ensure_var(l.var());
                        }
                        // Watch the highest-level reason literal (index 1).
                        let hi = (1..clause.len())
                            .max_by_key(|&i| self.level[clause[i].var() as usize])
                            .unwrap_or(1);
                        clause.swap(1, hi);
                        let cref = self.clauses.len();
                        self.attach_clause(clause, true);
                        self.enqueue(p, cref as i32);
                        progress = true;
                    }
                }
            }
        }
        if progress {
            TheoryPass::Progress
        } else {
            TheoryPass::Idle
        }
    }

    fn search(
        &mut self,
        assumptions: &[Lit],
        max_conflicts: u64,
        mut theory: Option<&mut dyn TheoryHook>,
    ) -> Option<SatResult> {
        if !self.ok {
            return Some(SatResult::Unsat);
        }
        if !(self.resumable && assumptions.is_empty() && self.decision_level() > 0) {
            self.cancel_until(0);
            // Re-propagate level 0 against the full clause DB. Clauses added
            // since the last solve (e.g. theory blocking clauses) may be unit or
            // falsified under the existing level-0 assignment; resetting qhead
            // forces them to be seen.
            self.qhead = 0;
        }
        for &l in assumptions {
            self.ensure_var(l.var());
        }
        let n_assump = assumptions.len() as u32;

        let mut restart_conflicts = 0u64;
        let mut total_conflicts = 0u64;
        let mut luby_index = 1u32; // Luby is 1-indexed
        let mut restart_limit = luby(luby_index) * 100;

        loop {
            // Determine the conflict source this iteration: Boolean propagation
            // first, then — only at the Boolean fixpoint with all assumptions
            // placed — one online theory-propagation pass (port of z3
            // `propagate_core`/`should_propagate`, `sat_solver.cpp:1002,1847`).
            let step = if self.pending.is_empty() {
                PendingStep::Idle
            } else {
                self.attach_pending()
            };
            let confl: Option<usize> = if let PendingStep::Conflict(c) = step {
                Some(c)
            } else if let PendingStep::Unsat = step {
                return Some(SatResult::Unsat);
            } else if let Some(c) = self.propagate() {
                Some(c)
            } else if self.decision_level() >= n_assump && self.theory_due() {
                match theory.as_deref_mut() {
                    Some(th) => match self.theory_pass(th) {
                        TheoryPass::Conflict(c) => Some(c),
                        // Enqueued implications: re-run Boolean propagation.
                        TheoryPass::Progress => continue,
                        TheoryPass::Idle => None,
                        TheoryPass::Unsat => return Some(SatResult::Unsat),
                    },
                    None => None,
                }
            } else {
                None
            };

            if let Some(confl) = confl {
                let chrono = self.resumable && n_assump == 0;
                if chrono {
                    // The conflict's own level: below it nothing is false.
                    match self.conflict_level(confl) {
                        None => {
                            self.ok = false;
                            return Some(SatResult::Unsat);
                        }
                        Some((lvl, true)) => {
                            // One literal of that level: the clause is unit
                            // just below it.
                            self.cancel_until(lvl - 1);
                            let unit = self.clauses[confl][0];
                            self.enqueue(unit, confl as i32);
                            continue;
                        }
                        Some((lvl, false)) => self.cancel_until(lvl),
                    }
                }
                if self.decision_level() == 0 {
                    self.ok = false;
                    return Some(SatResult::Unsat);
                }
                let (learnt, btlevel) = self.analyze(confl);
                if btlevel < n_assump {
                    // Backjumping would undo an assumption: unsat under assumptions.
                    self.cancel_until(0);
                    return Some(SatResult::Unsat);
                }
                let dl = self.decision_level();
                if chrono && dl - btlevel > self.chrono_levels {
                    self.cancel_until(dl - 1);
                } else {
                    self.cancel_until(btlevel);
                }
                let asserting = learnt[0];
                if learnt.len() == 1 {
                    self.enqueue_at(asserting, REASON_NONE, 0);
                } else {
                    let cref = self.clauses.len();
                    self.attach_clause(learnt, true);
                    self.enqueue(asserting, cref as i32);
                }
                self.var_inc /= 0.95; // decay
                self.cla_inc /= 0.999; // clause-activity decay
                total_conflicts += 1;
                self.conflicts += 1;
                if total_conflicts > max_conflicts {
                    self.cancel_until(0);
                    return None; // budget exhausted → unknown
                }
                restart_conflicts += 1;
                if restart_conflicts >= restart_limit {
                    restart_conflicts = 0;
                    luby_index += 1;
                    restart_limit = luby(luby_index) * 100;
                    self.cancel_until(n_assump); // keep the assumption prefix
                    // At a restart (decision level = assumptions) it is safe to
                    // reduce the learnt DB: nothing beyond the prefix is locked.
                    if self.n_learnt > self.max_learnt {
                        self.reduce_db();
                    }
                }
            } else if self.decision_level() < n_assump {
                // Place the next assumption as its own decision level.
                let a = assumptions[self.decision_level() as usize];
                match self.lit_value(a) {
                    LBool::False => {
                        self.cancel_until(0);
                        return Some(SatResult::Unsat);
                    }
                    LBool::True => self.trail_lim.push(self.trail.len()), // empty level
                    LBool::Undef => {
                        self.trail_lim.push(self.trail.len());
                        self.enqueue(a, REASON_NONE);
                    }
                }
            } else {
                match self.pick_branch_var() {
                    None => return Some(SatResult::Sat), // all variables assigned
                    Some(v) => {
                        self.trail_lim.push(self.trail.len());
                        let sign = self.polarity[v as usize];
                        self.enqueue(Lit::new(v, sign), REASON_NONE);
                    }
                }
            }
        }
    }
}

/// The Luby sequence (1,1,2,1,1,2,4,…) used to schedule restart intervals.
fn luby(mut i: u32) -> u64 {
    // Find the subsequence: smallest k with i < 2^k - 1.
    let mut k = 1u32;
    loop {
        if i == (1 << k) - 1 {
            return 1u64 << (k - 1);
        }
        if i < (1 << k) - 1 {
            i -= (1 << (k - 1)) - 1;
            k = 1;
        } else {
            k += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lits(v: &[i32]) -> Vec<Lit> {
        v.iter()
            .map(|&x| Lit::new(x.unsigned_abs() - 1, x < 0))
            .collect()
    }

    /// Mock online theory: whenever `a` is true, implies `b` with reason `[a]`
    /// (models the constraint `a → b`). Exercises the [`TheoryHook`] propagation
    /// path — the solver must materialize `(¬a ∨ b)` and enqueue `b` mid-search.
    struct ImplyHook {
        a: Lit,
        b: Lit,
    }
    impl TheoryHook for ImplyHook {
        fn propagate(&mut self, ctx: &TheoryCtx<'_>) -> TheoryProp {
            let val = |l| ctx.value(l);
            let mut implied = Vec::new();
            if val(self.a) == LBool::True && val(self.b) != LBool::True {
                implied.push((self.b, alloc::vec![self.a]));
            }
            TheoryProp {
                implied,
                conflict: None,
            }
        }
    }

    /// Mock online theory: `a ∧ b` is theory-inconsistent. Exercises the
    /// conflict path — the solver must materialize `¬(a ∧ b)` and analyze it.
    struct ConflictHook {
        a: Lit,
        b: Lit,
    }
    impl TheoryHook for ConflictHook {
        fn propagate(&mut self, ctx: &TheoryCtx<'_>) -> TheoryProp {
            let val = |l| ctx.value(l);
            let conflict = if val(self.a) == LBool::True && val(self.b) == LBool::True {
                Some(alloc::vec![self.a, self.b])
            } else {
                None
            };
            TheoryProp {
                implied: Vec::new(),
                conflict,
            }
        }
    }

    #[test]
    fn theory_propagation_forces_and_chains() {
        // The theory implies `b` from `a` mid-search; that must feed Boolean
        // propagation so a downstream clause `(¬b ∨ c)` also fires.
        let mut s = Solver::new();
        s.add_clause(&lits(&[1])); // a (var 0) asserted
        s.add_clause(&lits(&[-2, 3])); // (¬b ∨ c): b (var 1) → c (var 2)
        let mut hook = ImplyHook {
            a: Lit::pos(0),
            b: Lit::pos(1),
        };
        assert_eq!(s.solve_with_theory(&mut hook), SatResult::Sat);
        assert!(s.model_holds(Lit::pos(1)), "theory must force b");
        assert!(
            s.model_holds(Lit::pos(2)),
            "b→c must propagate after the theory forces b"
        );
    }

    #[test]
    fn theory_conflict_yields_unsat_at_level_zero() {
        // `a` and `b` forced true by units; the theory declares `a ∧ b` a
        // conflict at level 0 → unsat.
        let mut s = Solver::new();
        s.add_clause(&lits(&[1])); // a
        s.add_clause(&lits(&[2])); // b
        let mut hook = ConflictHook {
            a: Lit::pos(0),
            b: Lit::pos(1),
        };
        assert_eq!(s.solve_with_theory(&mut hook), SatResult::Unsat);
    }

    #[test]
    fn theory_conflict_forces_backtrack_to_model() {
        // Nothing forces `a`/`b`; the theory conflict `a ∧ b` must be learnt
        // mid-search and backtracked, yielding a model that respects it. `(a ∨ d)`
        // keeps the problem satisfiable (e.g. via `d`).
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 3])); // (a ∨ d)
        let mut hook = ConflictHook {
            a: Lit::pos(0),
            b: Lit::pos(1),
        };
        assert_eq!(s.solve_with_theory(&mut hook), SatResult::Sat);
        assert!(
            !(s.model_holds(Lit::pos(0)) && s.model_holds(Lit::pos(1))),
            "model must respect the theory conflict a ∧ b"
        );
    }

    #[test]
    fn empty_problem_is_sat() {
        let mut s = Solver::new();
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn pigeonhole_unsat_with_clause_deletion() {
        // PHP(n+1, n): n+1 pigeons into n holes is unsat. This generates enough
        // learnt clauses to exercise reduce_db while staying decidable.
        let n = 6usize;
        let mut s = Solver::new();
        // var(p, h) = pigeon p in hole h, 1-indexed literal p*n + h + 1.
        let var = |p: usize, h: usize| (p * n + h) as i32 + 1;
        // Each pigeon occupies at least one hole.
        for p in 0..=n {
            let clause: Vec<i32> = (0..n).map(|h| var(p, h)).collect();
            s.add_clause(&lits(&clause));
        }
        // No hole holds two pigeons.
        for h in 0..n {
            for p1 in 0..=n {
                for p2 in (p1 + 1)..=n {
                    s.add_clause(&lits(&[-var(p1, h), -var(p2, h)]));
                }
            }
        }
        // Force early reduction to cover the deletion path.
        s.max_learnt = 50;
        assert_eq!(s.solve_budgeted(10_000_000), Some(SatResult::Unsat));
    }

    #[test]
    fn empty_clause_is_unsat() {
        let mut s = Solver::new();
        s.add_clause(&[]);
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn unit_propagation_chain() {
        let mut s = Solver::new();
        s.add_clause(&lits(&[1]));
        s.add_clause(&lits(&[-1, 2]));
        s.add_clause(&lits(&[-2, 3]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert_eq!(s.value(0), LBool::True);
        assert_eq!(s.value(1), LBool::True);
        assert_eq!(s.value(2), LBool::True);
    }

    #[test]
    fn contradiction_is_unsat() {
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2]));
        s.add_clause(&lits(&[-1]));
        s.add_clause(&lits(&[-2]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn finds_a_satisfying_model() {
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2]));
        s.add_clause(&lits(&[-1]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert!(s.model_holds(Lit::pos(1)));
    }

    #[test]
    fn unit_clause_added_after_solve_backtracks_to_level_zero() {
        // Regression: a unit clause added *after* a SAT solve must not conflict
        // with that call's stale (non-level-0) trail and wrongly kill the solver.
        // `(x1 ∨ x2)` is SAT; the first solve may decide x1=true. Adding the unit
        // `¬x1` (a theory blocking clause) must still leave `(x1 ∨ x2)` SAT via
        // x2, not report a spurious UNSAT — exactly the DPLL(T) blocking pattern.
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2]));
        assert_eq!(s.solve(), SatResult::Sat);
        s.add_clause(&lits(&[-1])); // unit, forces x1 = false
        assert_eq!(s.solve(), SatResult::Sat);
        assert!(s.model_holds(Lit::pos(1))); // literal 2 (var 1) must hold
        // And once genuinely over-constrained at level 0 it is UNSAT.
        s.add_clause(&lits(&[-2]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn pigeonhole_php_3_2_is_unsat() {
        // 3 pigeons, 2 holes. var(p,h) = p*2 + h + 1 (1-based).
        let mut s = Solver::new();
        let v = |p: i32, h: i32| p * 2 + h + 1;
        // each pigeon in some hole
        for p in 0..3 {
            s.add_clause(&lits(&[v(p, 0), v(p, 1)]));
        }
        // no two pigeons share a hole
        for h in 0..2 {
            for p1 in 0..3 {
                for p2 in (p1 + 1)..3 {
                    s.add_clause(&lits(&[-v(p1, h), -v(p2, h)]));
                }
            }
        }
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn six_clause_cycle_unsat_regression() {
        // Exact instance that must be UNSAT (implication cycle + both polarities
        // blocked); guards against an earlier unsoundness.
        let mut s = Solver::new();
        for c in [
            lits(&[1, 2, 3]),
            lits(&[-1, 2]),
            lits(&[-2, 3]),
            lits(&[-3, 1]),
            lits(&[1, -2, 3]),
            lits(&[-1, -2, -3]),
        ] {
            s.add_clause(&c);
        }
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn implication_cycle_is_unsat() {
        // x1→x2→x3→x1 forces all equal; both all-true and all-false violate a
        // clause, so this is UNSAT — a good conflict-learning stress test.
        let mut s = Solver::new();
        for c in [
            lits(&[1, 2, 3]),
            lits(&[-1, 2]),
            lits(&[-2, 3]),
            lits(&[-3, 1]),
            lits(&[-1, -2, -3]),
        ] {
            s.add_clause(&c);
        }
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn learns_and_verifies_model_on_larger_sat() {
        let mut s = Solver::new();
        let clauses = [
            lits(&[1, 2, 3]),
            lits(&[-1, 2]),
            lits(&[-2, 3]),
            lits(&[1, -2, 3]),
        ];
        for c in &clauses {
            s.add_clause(c);
        }
        assert_eq!(s.solve(), SatResult::Sat);
        for c in &clauses {
            assert!(
                c.iter().any(|&l| s.model_holds(l)),
                "clause {c:?} unsatisfied"
            );
        }
    }

    #[test]
    fn solving_under_assumptions() {
        // (x1 ∨ x2)
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2]));
        // No assumptions: satisfiable.
        assert_eq!(s.solve(), SatResult::Sat);
        // Assume ¬x1: still satisfiable (x2 must hold).
        assert_eq!(s.solve_assumptions(&lits(&[-1])), SatResult::Sat);
        assert!(s.model_holds(Lit::pos(1)));
        // Assume ¬x1 ∧ ¬x2: contradicts the clause → unsat under assumptions,
        // but the clause set itself is still satisfiable afterwards.
        assert_eq!(s.solve_assumptions(&lits(&[-1, -2])), SatResult::Unsat);
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn assumption_directly_contradicting_a_unit() {
        let mut s = Solver::new();
        s.add_clause(&lits(&[1])); // x1 forced true
        assert_eq!(s.solve(), SatResult::Sat);
        // Assuming ¬x1 contradicts the unit.
        assert_eq!(s.solve_assumptions(&lits(&[-1])), SatResult::Unsat);
    }

    #[test]
    fn theory_lemma_clause_forces_implied_literal() {
        // DPLL(T) reason-injection primitive (step A): a theory-propagated literal
        // `b` implied by `a` is materialized as the globally-valid lemma
        // `(¬a ∨ b)` and injected via `add_clause`. With `a` also asserted, solving
        // must force `b`, and a full model must still satisfy every original clause
        // (the lemma only prunes, never changes the verdict). Injection at level 0
        // via `add_clause` gives exactly the semantics step B relies on.
        let mut s = Solver::new();
        let originals = [lits(&[1, 3]), lits(&[-3, 2, 4])];
        for c in &originals {
            s.add_clause(c);
        }
        s.add_clause(&lits(&[1])); // assert a (var 0)
        s.add_clause(&lits(&[-1, 2])); // theory lemma (¬a ∨ b), b = var 1
        assert_eq!(s.solve(), SatResult::Sat);
        assert!(s.model_holds(Lit::pos(1)), "theory lemma must force b");
        for c in &originals {
            assert!(
                c.iter().any(|&l| s.model_holds(l)),
                "clause {c:?} unsatisfied"
            );
        }
    }

    #[test]
    fn theory_lemma_injected_between_solves_is_incremental() {
        // Injecting a theory lemma *after* a first SAT solve (the between-solves
        // level-0 pattern of step B) must be honored on the next solve without any
        // spurious unsat, and must not disturb an already-satisfiable base.
        let mut s = Solver::new();
        s.add_clause(&lits(&[1, 2])); // (a ∨ b)
        assert_eq!(s.solve(), SatResult::Sat);
        // Between solves, inject the valid implication (¬a ∨ b) and assert a.
        s.add_clause(&lits(&[-1, 2]));
        s.add_clause(&lits(&[1]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert!(s.model_holds(Lit::pos(0)), "a must hold");
        assert!(s.model_holds(Lit::pos(1)), "lemma must force b");
    }

    /// Mock online theory: each listed pair of literals is inconsistent.
    struct PairsHook {
        bad: Vec<(Lit, Lit)>,
    }
    impl TheoryHook for PairsHook {
        fn propagate(&mut self, ctx: &TheoryCtx<'_>) -> TheoryProp {
            let val = |l| ctx.value(l);
            let mut implied = Vec::new();
            for &(a, b) in &self.bad {
                match (val(a), val(b)) {
                    (LBool::True, LBool::True) => {
                        return TheoryProp {
                            implied: Vec::new(),
                            conflict: Some(alloc::vec![a, b]),
                        };
                    }
                    (LBool::True, LBool::Undef) => implied.push((!b, alloc::vec![a])),
                    _ => {}
                }
            }
            TheoryProp {
                implied,
                conflict: None,
            }
        }
    }

    #[test]
    fn resumable_search_matches_fresh_search() {
        // Random 3-SAT plus theory pairs, the clauses added in batches between
        // resumed searches (mid-search, with chronological backtracking past
        // one level), against a fresh search over the same clauses.
        let mut seed = 12345u64;
        let mut rnd = |n: u64| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) % n
        };
        for _ in 0..2000 {
            let nv = 8 + rnd(120) as i32;
            let nc = (nv as u64 * (15 + rnd(30))) / 10;
            let mut clauses: Vec<Vec<i32>> = Vec::new();
            for _ in 0..nc {
                let len = if rnd(10) == 0 { 1 } else { 2 + rnd(3) as usize };
                let c: Vec<i32> = (0..len)
                    .map(|_| {
                        let v = 1 + rnd(nv as u64) as i32;
                        if rnd(2) == 0 { v } else { -v }
                    })
                    .collect();
                clauses.push(c);
            }
            let bad: Vec<(Lit, Lit)> = (0..rnd(6))
                .map(|_| {
                    let a = lits(&[1 + rnd(nv as u64) as i32])[0];
                    let b = lits(&[-(1 + rnd(nv as u64) as i32)])[0];
                    (a, b)
                })
                .filter(|(a, b)| a.var() != b.var())
                .collect();
            let mut live = Solver::new();
            live.set_resumable();
            live.chrono_levels = 1;
            live.ensure_var(nv as Var);
            let mut hook = PairsHook { bad: bad.clone() };
            let mut verdict = SatResult::Sat;
            let mut added = 0;
            while added < clauses.len() {
                let step = 1 + rnd(8) as usize;
                for c in &clauses[added..(added + step).min(clauses.len())] {
                    live.add_clause(&lits(c));
                }
                added = (added + step).min(clauses.len());
                verdict = live.solve_with_theory(&mut hook);
                if verdict == SatResult::Unsat {
                    break;
                }
                for c in &clauses[..added] {
                    assert!(lits(c).iter().any(|&l| live.model_holds(l)), "model");
                }
                for &(a, b) in &bad {
                    assert!(!(live.model_holds(a) && live.model_holds(b)), "theory");
                }
            }
            let mut fresh = Solver::new();
            fresh.ensure_var(nv as Var);
            for c in &clauses {
                fresh.add_clause(&lits(c));
            }
            let mut hook = PairsHook { bad };
            assert_eq!(fresh.solve_with_theory(&mut hook), verdict);
        }
    }

    #[test]
    fn luby_sequence_prefix() {
        // Luby is 1-indexed: luby(1..).
        let seq: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(seq, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }
}
