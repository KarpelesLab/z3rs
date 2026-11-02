//! Online linear arithmetic for DPLL(T): the bounded simplex ([`Lra`]) follows
//! the SAT trail, asserting the bound of every arithmetic atom the search
//! assigns and reporting a Farkas conflict as soon as the asserted bounds are
//! infeasible over the rationals — the role of z3's `theory_lra`
//! (`z3/src/smt/theory_lra.cpp`, `assign_eh` / `propagate` / `set_conflict`,
//! Z3 4.17.0, MIT) on partial assignments.
//!
//! Disequalities and integrality are left to the offline final check: a
//! rational conflict is a conflict over the integers too, so everything this
//! reports is sound for `Int` as well (integer strict bounds are tightened
//! first, `e < 0` to `e + 1 ≤ 0`, which only holds for integral `e`).

use alloc::vec::Vec;

use crate::sat::literal::Lit;
use crate::sat::solver::{TheoryCtx, TheoryHook, TheoryProp};
use crate::smt::arith::{Check, Constraint, Lra, LraBound};

/// Pivot budget for one propagation pass; on exhaustion the pass reports
/// nothing (the final check still decides).
const PASS_BUDGET: u64 = 50_000;

/// The simplex following the SAT trail.
pub struct ArithOnline {
    lra: Lra,
    /// Per SAT variable: the bound when the atom is true / false.
    bounds: Vec<Option<(Option<LraBound>, Option<LraBound>)>>,
    /// Bound tag → the asserted literals it stands for.
    tags: Vec<Vec<Lit>>,
    /// Number of trail literals asserted, and per asserted trail position the
    /// tag count before it (each also opened one simplex scope).
    processed: usize,
    marks: Vec<(usize, usize)>,
}

impl ArithOnline {
    /// An online arithmetic theory over the atoms `(lit, if_true, if_false)`:
    /// the constraint the atom imposes in each polarity (`None` when it imposes
    /// none online, e.g. a disequality).
    pub fn new(atoms: &[(Lit, Option<Constraint>, Option<Constraint>)]) -> ArithOnline {
        let mut a = ArithOnline {
            lra: Lra::default(),
            bounds: Vec::new(),
            tags: Vec::new(),
            processed: 0,
            marks: Vec::new(),
        };
        for (lit, t, f) in atoms {
            a.add_atom(*lit, t.as_ref(), f.as_ref());
        }
        a
    }

    /// Watch one more atom `lit` with its constraint when true / false.
    pub fn add_atom(&mut self, lit: Lit, t: Option<&Constraint>, f: Option<&Constraint>) {
        let (mut bt, mut bf) = (
            t.map(|c| self.lra.prepare(c)),
            f.map(|c| self.lra.prepare(c)),
        );
        if lit.sign() {
            core::mem::swap(&mut bt, &mut bf);
        }
        let v = lit.var() as usize;
        if self.bounds.len() <= v {
            self.bounds.resize_with(v + 1, || None);
        }
        self.bounds[v] = Some((bt, bf));
    }

    /// Retract every asserted trail position `≥ pos`.
    fn rollback(&mut self, pos: usize) {
        while let Some(&(p, ntags)) = self.marks.last() {
            if p < pos {
                break;
            }
            self.lra.pop();
            self.tags.truncate(ntags);
            self.marks.pop();
        }
        self.processed = self.processed.min(pos);
    }
}

impl TheoryHook for ArithOnline {
    fn propagate(&mut self, ctx: &TheoryCtx<'_>) -> TheoryProp {
        self.propagate_with(ctx, &[])
    }
}

impl ArithOnline {
    /// [`TheoryHook::propagate`], also asserting the equalities `eqs`
    /// (`(trail position, constraint, explanation)`, in position order) that
    /// another theory derived while asserting the trail.
    pub fn propagate_with(
        &mut self,
        ctx: &TheoryCtx<'_>,
        eqs: &[(usize, Constraint, Vec<Lit>)],
    ) -> TheoryProp {
        if ctx.stable < self.processed {
            self.rollback(ctx.stable);
        }
        let start = self.processed;
        let mut conflict: Option<Vec<usize>> = None;
        let mut asserted = false;
        let mut next_eq = eqs.partition_point(|e| e.0 < start);
        for (pos, &l) in ctx.trail.iter().enumerate().skip(start) {
            let mut items: Vec<(LraBound, Vec<Lit>)> = Vec::new();
            if let Some(Some((bt, bf))) = self.bounds.get(l.var() as usize) {
                // The bound of the variable's positive literal being `l`.
                if let Some(b) = if l.sign() { bf } else { bt } {
                    items.push((b.clone(), alloc::vec![l]));
                }
            }
            while next_eq < eqs.len() && eqs[next_eq].0 == pos {
                let (_, c, why) = &eqs[next_eq];
                items.push((self.lra.prepare(c), why.clone()));
                next_eq += 1;
            }
            if items.is_empty() {
                continue;
            }
            self.marks.push((pos, self.tags.len()));
            self.lra.push();
            asserted = true;
            for (b, why) in items {
                let tag = self.tags.len();
                self.tags.push(why);
                if let Err(core) = self.lra.assert(&b, tag) {
                    conflict = Some(core);
                    break;
                }
            }
            if conflict.is_some() {
                break;
            }
        }
        self.processed = ctx.trail.len();
        if conflict.is_none() && asserted {
            let mut budget = PASS_BUDGET;
            if let Check::Unsat(core) = self.lra.check(&mut budget) {
                conflict = Some(core);
            }
        }
        let conflict = conflict.map(|core| {
            let mut lits: Vec<Lit> = core
                .iter()
                .flat_map(|&t| self.tags[t].iter().copied())
                .collect();
            lits.sort_unstable();
            lits.dedup();
            // The search backjumps below this pass: forget it now.
            self.rollback(start);
            lits
        });
        TheoryProp {
            implied: Vec::new(),
            conflict,
        }
    }
}
