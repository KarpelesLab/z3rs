//! A conflict-driven clause-learning (CDCL) SAT solver.
//!
//! MiniSat-style core ported in spirit from `z3/src/sat/sat_solver.{h,cpp}`
//! (Z3 4.17.0, MIT): two-watched-literal propagation, 1-UIP conflict analysis
//! with clause learning, non-chronological backjumping, VSIDS decision
//! heuristic, and Luby restarts. Learnt-clause DB reduction and in-processing
//! come later.

use alloc::vec;
use alloc::vec::Vec;

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

/// Sentinel `reason`: a decision literal or a top-level fact (no antecedent).
const REASON_NONE: i32 = -1;

/// A CDCL SAT solver.
pub struct Solver {
    assign: Vec<LBool>,
    level: Vec<u32>,
    /// Antecedent clause index for an implied literal, or [`REASON_NONE`].
    reason: Vec<i32>,
    /// Saved polarity for phase saving.
    polarity: Vec<bool>,
    activity: Vec<f64>,
    var_inc: f64,

    clauses: Vec<Vec<Lit>>,
    /// `watches[l.index()]` = clauses watching literal `~l` (MiniSat convention).
    watches: Vec<Vec<usize>>,
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

    ok: bool,
}

impl Default for Solver {
    fn default() -> Solver {
        Solver::new()
    }
}

impl Solver {
    /// A new, empty solver.
    pub fn new() -> Solver {
        Solver {
            assign: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            polarity: Vec::new(),
            activity: Vec::new(),
            var_inc: 1.0,
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
        self.polarity.push(false);
        self.activity.push(0.0);
        self.watches.push(Vec::new()); // for the positive literal
        self.watches.push(Vec::new()); // for the negative literal
        v
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

    /// Add a clause. Duplicate literals are merged, tautologies dropped, and an
    /// empty clause makes the problem unsatisfiable.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        if !self.ok {
            return;
        }
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
        self.clauses.push(ps);
        self.learnt.push(learnt);
        self.cla_activity.push(0.0);
        self.deleted.push(false);
        self.watches[w0].push(cref);
        self.watches[w1].push(cref);
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
    fn enqueue(&mut self, l: Lit, reason: i32) -> bool {
        match self.lit_value(l) {
            LBool::True => true,
            LBool::False => false,
            LBool::Undef => {
                let v = l.var() as usize;
                self.assign[v] = LBool::from_bool(!l.sign());
                self.level[v] = self.decision_level();
                self.reason[v] = reason;
                self.trail.push(l);
                true
            }
        }
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
                let cref = ws[i];
                if self.deleted[cref] {
                    ws.swap_remove(i); // drop stale watch of a deleted clause
                    continue;
                }
                // Ensure the false watched literal is at position 1.
                if self.clauses[cref][0] == false_lit {
                    self.clauses[cref].swap(0, 1);
                }
                let first = self.clauses[cref][0]; // the other watched literal
                if self.lit_value(first) == LBool::True {
                    i += 1; // clause already satisfied; keep watching
                    continue;
                }
                // Look for a new, non-false literal to watch.
                let len = self.clauses[cref].len();
                for k in 2..len {
                    let lk = self.clauses[cref][k];
                    if self.lit_value(lk) != LBool::False {
                        self.clauses[cref].swap(1, k);
                        self.watches[(!self.clauses[cref][1]).index() as usize].push(cref);
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
        }
    }

    /// 1-UIP conflict analysis. Returns the learnt clause (asserting literal at
    /// index 0) and the level to backjump to.
    fn analyze(&mut self, confl: usize) -> (Vec<Lit>, u32) {
        let cur_level = self.decision_level();
        let mut seen = vec![false; self.num_vars()];
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
            while !seen[self.trail[index].var() as usize] {
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
        while self.trail.len() > target {
            let l = self.trail.pop().unwrap();
            let v = l.var() as usize;
            self.assign[v] = LBool::Undef;
            self.polarity[v] = !l.sign(); // phase saving
            self.reason[v] = REASON_NONE;
        }
        self.qhead = target;
        self.trail_lim.truncate(level as usize);
    }

    /// Pick the unassigned variable with the highest activity.
    fn pick_branch_var(&self) -> Option<Var> {
        let mut best: Option<(f64, Var)> = None;
        for v in 0..self.num_vars() {
            if self.assign[v] == LBool::Undef {
                let a = self.activity[v];
                if best.is_none_or(|(ba, _)| a > ba) {
                    best = Some((a, v as Var));
                }
            }
        }
        best.map(|(_, v)| v)
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
        self.search(assumptions, u64::MAX)
            .unwrap_or(SatResult::Unsat)
    }

    /// Solve, giving up after `max_conflicts` conflicts. Returns `None` when the
    /// budget is exhausted (the caller treats that as `unknown`), so a
    /// hard-but-decidable instance cannot hang the solver.
    pub fn solve_budgeted(&mut self, max_conflicts: u64) -> Option<SatResult> {
        self.search(&[], max_conflicts)
    }

    fn search(&mut self, assumptions: &[Lit], max_conflicts: u64) -> Option<SatResult> {
        if !self.ok {
            return Some(SatResult::Unsat);
        }
        self.cancel_until(0);
        // Re-propagate level 0 against the full clause DB. Clauses added since the
        // last solve (e.g. theory blocking clauses) may be unit or falsified under
        // the existing level-0 assignment; resetting qhead forces them to be seen.
        self.qhead = 0;
        for &l in assumptions {
            self.ensure_var(l.var());
        }
        let n_assump = assumptions.len() as u32;

        let mut restart_conflicts = 0u64;
        let mut total_conflicts = 0u64;
        let mut luby_index = 1u32; // Luby is 1-indexed
        let mut restart_limit = luby(luby_index) * 100;

        loop {
            if let Some(confl) = self.propagate() {
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
                self.cancel_until(btlevel);
                let asserting = learnt[0];
                if learnt.len() == 1 {
                    self.enqueue(asserting, REASON_NONE);
                } else {
                    let cref = self.clauses.len();
                    self.attach_clause(learnt, true);
                    self.enqueue(asserting, cref as i32);
                }
                self.var_inc /= 0.95; // decay
                self.cla_inc /= 0.999; // clause-activity decay
                total_conflicts += 1;
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
    fn luby_sequence_prefix() {
        // Luby is 1-indexed: luby(1..).
        let seq: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(seq, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }
}
