//! The nlsat solver: conflict-driven, model-constructing satisfiability of
//! Boolean combinations of polynomial constraints over the reals (Jovanović and
//! de Moura, "Solving Non-Linear Arithmetic", IJCAR 2012).
//!
//! Ported from `z3/src/nlsat/nlsat_solver.cpp`, `nlsat_evaluator.cpp`,
//! `nlsat_interval_set.cpp` and `nlsat_explain.cpp` (MIT). The search assigns
//! the arithmetic variables one at a time (a *stage* per variable). In the stage
//! of `x` every clause whose maximal variable is `x` must be satisfied by a
//! value of `x`; each literal's *infeasible set* (the values of `x`, under the
//! assignment of the lower variables, at which it is false) comes from the
//! roots of its polynomial. When the infeasible sets of a clause cover the
//! real line, the conflict is explained by a lemma built by z3's levelwise
//! single-cell construction (`levelwise`; the classic sample-cell projection
//! of `nlsat_explain` is the fallback): a clause, valid in the reals, whose
//! literals over the lower variables describe a cell around the current sample
//! in which the conflict persists. CDCL-style resolution of these lemmas then either
//! backjumps to a lower stage or derives the empty clause.
//!
//! Projection polynomials are replaced by their factors (`math::factor`, a
//! partial factorization); root isolation and atom degrees work on the
//! factors too, as z3's atoms are products of factors. Integer variables are handled as z3's
//! `search_check` does: branch and bound on a non-integral value of a
//! satisfying assignment.
//!
//! Every answer is exact: `Unsat` means the empty clause was derived from valid
//! lemmas; `Sat` comes with an assignment satisfying every clause (each clause
//! has a literal evaluated true at the exact algebraic sample). Any inexact
//! primitive (an inexact resultant, an unresolved root comparison) or an
//! exhausted budget yields `Unknown`.
//!
//! Root literals of linear and quadratic polynomials become sign conditions
//! (`mk_linear_root`, `mk_quadratic_root`'s Thom encoding).
//!
//! Before projection the conflict core is normalized and simplified with its
//! equations and those of lower stages (`simplify`, z3's
//! `simplify_conflicts`).
//!
//! Not ported: core minimization, restarts and reordering during search, and
//! lazy-mode clause skipping.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::cmp::Ordering;

use puremp::{Int, Rational};

use crate::math::polynomial::{Monomial, Polynomial, Var};
use crate::math::resultant::psc_chain;
use crate::nlsat::cad::roots_at;
use crate::nlsat::realclosure::{Alg, sign_at_point};

mod levelwise;
mod simplify;

/// The kind of an arithmetic atom: `p = 0`, `p < 0`, `p > 0`, or a comparison
/// of the atom's variable with the `i`-th real root of `p` (`x = root_i(p)`, …).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    /// `p = 0`.
    Eq,
    /// `p < 0`.
    Lt,
    /// `p > 0`.
    Gt,
    /// `x = root_i(p)`.
    RootEq,
    /// `x < root_i(p)`.
    RootLt,
    /// `x > root_i(p)`.
    RootGt,
    /// `x ≤ root_i(p)`.
    RootLe,
    /// `x ≥ root_i(p)`.
    RootGe,
}

impl Kind {
    /// `p < 0` ⇔ `-p > 0`.
    fn flip(self) -> Kind {
        match self {
            Kind::Lt => Kind::Gt,
            Kind::Gt => Kind::Lt,
            k => k,
        }
    }

    fn is_eq(self) -> bool {
        matches!(self, Kind::Eq | Kind::RootEq)
    }

    fn is_root(self) -> bool {
        !matches!(self, Kind::Eq | Kind::Lt | Kind::Gt)
    }
}

/// A literal: a Boolean variable and a sign (`true` = negated).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(u32);

impl Lit {
    /// The literal of Boolean variable `b`, negated when `neg`.
    pub fn new(b: u32, neg: bool) -> Lit {
        Lit(b * 2 + u32::from(neg))
    }
    /// Its Boolean variable.
    pub fn var(self) -> u32 {
        self.0 >> 1
    }
    /// Whether it is negated.
    pub fn sign(self) -> bool {
        self.0 & 1 == 1
    }
    /// The complementary literal.
    pub fn complement(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

/// Boolean variable 0 is the constant `true`.
const TRUE_LIT: Lit = Lit(0);
const FALSE_LIT: Lit = Lit(1);

/// An input literal for [`check`].
#[derive(Clone, Debug)]
pub enum InLit {
    /// The pure Boolean variable `b` (numbered from 0), negated when `neg`.
    Bool(u32, bool),
    /// The polynomial constraint `p ⋈ 0` (`Eq`, `Lt` or `Gt`), negated when
    /// `neg`.
    Ineq(Polynomial, Kind, bool),
}

/// The outcome of [`check`].
#[derive(Clone, Debug)]
pub enum NlsatResult {
    /// Satisfiable: a value for every arithmetic variable (indexed as in the
    /// input) and every pure Boolean variable.
    Sat(Vec<Alg>, Vec<bool>),
    /// Unsatisfiable over the reals.
    Unsat,
    /// Undecided (an inexact primitive or an exhausted budget).
    Unknown,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LBool {
    True,
    False,
    Undef,
}

impl LBool {
    fn from(b: bool) -> LBool {
        if b { LBool::True } else { LBool::False }
    }
    fn not(self) -> LBool {
        match self {
            LBool::True => LBool::False,
            LBool::False => LBool::True,
            LBool::Undef => LBool::Undef,
        }
    }
}

/// An arithmetic atom over the internal (reordered) variables.
#[derive(Clone, Debug)]
struct Atom {
    kind: Kind,
    p: Polynomial,
    /// The maximal variable (for a root atom, its compared variable).
    x: Var,
    /// The 1-based root index of a root atom (0 for an inequality).
    i: u32,
    /// Its degree in `x`: for an inequality, the largest degree of a factor
    /// of `p` (z3's atoms are products of factors).
    deg: u32,
}

#[derive(Clone, Debug)]
struct Clause {
    lits: Vec<Lit>,
}

/// Why a Boolean variable has its value.
#[derive(Clone, Debug)]
enum Just {
    None,
    Decision,
    Clause(usize),
    /// Implied in the current interpretation by the infeasibility of these
    /// literals (z3's lazy justification; explained on demand).
    Lazy(Vec<Lit>),
}

/// A maximal interval of values of the current variable at which some
/// literal (`just`) is false.
#[derive(Clone, Debug)]
struct Interval {
    lower_open: bool,
    lower_inf: bool,
    lower: Alg,
    upper_open: bool,
    upper_inf: bool,
    upper: Alg,
    just: Lit,
}

/// A sorted set of disjoint infeasible intervals (`nlsat_interval_set`).
#[derive(Clone, Debug, Default)]
struct ISet {
    ivs: Vec<Interval>,
    full: bool,
}

#[derive(Clone, Debug)]
enum Trail {
    BAssign(u32),
    Infeasible(ISet),
    NewStage,
    NewLevel,
    /// The previous equation recorded for the current stage.
    UpdtEq(Option<usize>),
}

/// An inequality atom's factors with parity (`true`: even multiplicity) and
/// the sign of the remaining constant.
type AtomFactors = (Vec<(Polynomial, bool)>, i32);

/// The solver aborted: an inexact primitive or an exhausted budget.
#[derive(Debug)]
struct Abort;

/// Explanation control flow: abort, or restart with all coefficients.
enum ExplainErr {
    Abort,
    Restart,
}

impl From<Abort> for ExplainErr {
    fn from(_: Abort) -> ExplainErr {
        ExplainErr::Abort
    }
}

type Res<T> = Result<T, Abort>;

/// z3's `random_gen` (`util/util.h`), for the witness choices.
struct RandomGen(u32);

impl RandomGen {
    fn next(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(214013).wrapping_add(2531011);
        (self.0 >> 16) & 0x7fff
    }
}

fn zero() -> Rational {
    Rational::from_integer(Int::from(0))
}

fn rat(n: i64) -> Rational {
    Rational::from_integer(Int::from(n))
}

/// The variables of `p`, and its maximal one (`None` for a constant).
fn max_var(p: &Polynomial) -> Option<Var> {
    p.terms()
        .iter()
        .flat_map(|(_, m)| m.vars().collect::<Vec<_>>())
        .max()
}

/// `p` scaled by a positive rational to primitive integer coefficients
/// (signs preserved), so equal-up-to-positive-factor polynomials coincide.
fn primitive(p: &Polynomial) -> Polynomial {
    if p.is_zero() {
        return p.clone();
    }
    let mut den = Int::from(1);
    for (c, _) in p.terms() {
        let d = c.denominator();
        let g = den.gcd(d);
        den = den.mul(d).div_floor(&g);
    }
    let mut num = Int::from(0);
    for (c, _) in p.terms() {
        let n = c
            .mul(&Rational::from_integer(den.clone()))
            .numerator()
            .clone();
        num = num.gcd(&n);
    }
    let scale = Rational::new(den, num.abs());
    p.scale(&scale)
}

/// `p` primitive with a positive leading coefficient, and whether the sign
/// was flipped (z3's `flip_sign_if_lm_neg` on a canonical representative).
fn normalize(p: &Polynomial) -> (Polynomial, bool) {
    let q = primitive(p);
    match q.terms().first() {
        Some((c, _)) if c.is_negative() => (q.neg(), true),
        _ => (q, false),
    }
}

impl Interval {
    fn new(
        lower_open: bool,
        lower_inf: bool,
        lower: Option<&Alg>,
        upper_open: bool,
        upper_inf: bool,
        upper: Option<&Alg>,
        just: Lit,
    ) -> Interval {
        let z = Alg::Rational(zero());
        Interval {
            lower_open,
            lower_inf,
            lower: lower.cloned().unwrap_or_else(|| z.clone()),
            upper_open,
            upper_inf,
            upper: upper.cloned().unwrap_or(z),
            just,
        }
    }
}

fn sgn(o: Ordering) -> i32 {
    match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

fn compare_lower_lower(a: &Interval, b: &Interval) -> i32 {
    if a.lower_inf && b.lower_inf {
        return 0;
    }
    if a.lower_inf {
        return -1;
    }
    if b.lower_inf {
        return 1;
    }
    let s = sgn(a.lower.compare(&b.lower));
    if s != 0 {
        return s;
    }
    if a.lower_open == b.lower_open {
        0
    } else if a.lower_open {
        1
    } else {
        -1
    }
}

fn compare_upper_upper(a: &Interval, b: &Interval) -> i32 {
    if a.upper_inf && b.upper_inf {
        return 0;
    }
    if a.upper_inf {
        return 1;
    }
    if b.upper_inf {
        return -1;
    }
    let s = sgn(a.upper.compare(&b.upper));
    if s != 0 {
        return s;
    }
    if a.upper_open == b.upper_open {
        0
    } else if a.upper_open {
        -1
    } else {
        1
    }
}

fn compare_upper_lower(a: &Interval, b: &Interval) -> i32 {
    if a.upper_inf || b.lower_inf {
        return 1;
    }
    let s = sgn(a.upper.compare(&b.lower));
    if s != 0 {
        return s;
    }
    if !a.upper_open && !b.lower_open {
        0
    } else {
        -1
    }
}

fn adjacent(a: &Interval, b: &Interval) -> bool {
    if a.upper_inf || b.lower_inf {
        return false;
    }
    a.upper.compare(&b.lower) == Ordering::Equal && (!a.upper_open || !b.lower_open)
}

impl ISet {
    fn single(iv: Interval) -> ISet {
        let full = iv.lower_inf && iv.upper_inf;
        ISet {
            ivs: alloc::vec![iv],
            full,
        }
    }

    fn is_empty(&self) -> bool {
        self.ivs.is_empty()
    }

    /// The union of two interval sets (`interval_set_manager::mk_union`).
    fn union(s1: &ISet, s2: &ISet) -> ISet {
        if s1.is_empty() {
            return s2.clone();
        }
        if s2.is_empty() {
            return s1.clone();
        }
        if s1.full {
            return s1.clone();
        }
        if s2.full {
            return s2.clone();
        }
        let mut result: Vec<Interval> = Vec::new();
        let (sz1, sz2) = (s1.ivs.len(), s2.ivs.len());
        let (mut i1, mut i2) = (0, 0);
        loop {
            if i1 >= sz1 {
                result.extend(s2.ivs[i2..].iter().cloned());
                break;
            }
            if i2 >= sz2 {
                result.extend(s1.ivs[i1..].iter().cloned());
                break;
            }
            let int1 = &s1.ivs[i1];
            let int2 = &s2.ivs[i2];
            let l1_l2 = compare_lower_lower(int1, int2);
            let u1_u2 = compare_upper_upper(int1, int2);
            if l1_l2 <= 0 {
                if u1_u2 == 0 {
                    result.push(int1.clone());
                    i1 += 1;
                    i2 += 1;
                } else if u1_u2 > 0 {
                    i2 += 1;
                } else {
                    let u1_l2 = compare_upper_lower(int1, int2);
                    if u1_l2 < 0 {
                        result.push(int1.clone());
                        i1 += 1;
                    } else if u1_l2 == 0 {
                        if l1_l2 != 0 {
                            let mut iv = int1.clone();
                            iv.upper_open = true;
                            iv.upper_inf = false;
                            result.push(iv);
                        }
                        i1 += 1;
                    } else if l1_l2 == 0 {
                        i1 += 1;
                    } else {
                        let mut iv = int1.clone();
                        iv.upper_open = !int2.lower_open;
                        iv.upper_inf = false;
                        iv.upper = int2.lower.clone();
                        result.push(iv);
                        i1 += 1;
                    }
                }
            } else if u1_u2 == 0 {
                result.push(int2.clone());
                i1 += 1;
                i2 += 1;
            } else if u1_u2 < 0 {
                i1 += 1;
            } else {
                let u2_l1 = compare_upper_lower(int2, int1);
                if u2_l1 < 0 {
                    result.push(int2.clone());
                    i2 += 1;
                } else if u2_l1 == 0 {
                    let mut iv = int2.clone();
                    iv.upper_open = true;
                    iv.upper_inf = false;
                    result.push(iv);
                    i2 += 1;
                } else {
                    let mut iv = int2.clone();
                    iv.upper_open = !int1.lower_open;
                    iv.upper_inf = false;
                    iv.upper = int1.lower.clone();
                    result.push(iv);
                    i2 += 1;
                }
            }
        }
        // Merge adjacent intervals with the same justification.
        let mut merged: Vec<Interval> = Vec::with_capacity(result.len());
        for next in result {
            if let Some(curr) = merged.last_mut()
                && curr.just == next.just
                && adjacent(curr, &next)
            {
                curr.upper_inf = next.upper_inf;
                curr.upper_open = next.upper_open;
                curr.upper = next.upper;
                continue;
            }
            merged.push(next);
        }
        let n = merged.len();
        let mut slack = !merged[0].lower_inf || !merged[n - 1].upper_inf;
        for i in 0..n.saturating_sub(1) {
            if slack {
                break;
            }
            if !adjacent(&merged[i], &merged[i + 1]) {
                slack = true;
            }
        }
        ISet {
            ivs: merged,
            full: !slack,
        }
    }

    /// Whether `s1 ⊆ s2` (`interval_set_manager::subset`).
    fn subset(s1: &ISet, s2: &ISet) -> bool {
        if s1.is_empty() {
            return true;
        }
        if s2.is_empty() {
            return false;
        }
        if s2.full {
            return true;
        }
        if s1.full {
            return false;
        }
        let (sz1, sz2) = (s1.ivs.len(), s2.ivs.len());
        let (mut i1, mut i2) = (0, 0);
        while i1 < sz1 && i2 < sz2 {
            let int1 = &s1.ivs[i1];
            if compare_lower_lower(int1, &s2.ivs[i2]) < 0 {
                return false;
            }
            while i2 < sz2 {
                let int2 = &s2.ivs[i2];
                let u1_u2 = compare_upper_upper(int1, int2);
                if u1_u2 == 0 {
                    i1 += 1;
                    i2 += 1;
                    break;
                } else if u1_u2 < 0 {
                    i1 += 1;
                    break;
                } else {
                    if compare_upper_lower(int2, int1) < 0 {
                        i2 += 1;
                        break;
                    }
                    if i2 == sz2 - 1 {
                        return false;
                    }
                    if !adjacent(int2, &s2.ivs[i2 + 1]) {
                        return false;
                    }
                    i2 += 1;
                }
            }
        }
        i1 == sz1
    }

    /// The justifying literals, each once, in interval order.
    fn justifications(&self) -> Vec<Lit> {
        let mut out: Vec<Lit> = Vec::new();
        for iv in &self.ivs {
            if !out.contains(&iv.just) {
                out.push(iv.just);
            }
        }
        out
    }
}

/// `⌊a⌋`.
fn alg_floor(a: &Alg) -> Int {
    match a {
        Alg::Rational(r) => r.floor(),
        Alg::Irrational { .. } => {
            let mut k = a.approx().floor();
            loop {
                let kr = Alg::Rational(Rational::from_integer(k.clone()));
                if a.compare(&kr) == Ordering::Less {
                    k = k.sub(&Int::from(1));
                    continue;
                }
                let k1 = Alg::Rational(Rational::from_integer(k.add(&Int::from(1))));
                if a.compare(&k1) != Ordering::Less {
                    k = k.add(&Int::from(1));
                    continue;
                }
                return k;
            }
        }
    }
}

/// The smallest integer strictly above `a` (z3's `int_gt`).
fn int_gt(a: &Alg) -> Rational {
    match a {
        Alg::Rational(r) => Rational::from_integer(r.ceil().add(&Int::from(1))),
        Alg::Irrational { hi, .. } => Rational::from_integer(hi.ceil()),
    }
}

/// The largest integer strictly below `a` (z3's `int_lt`).
fn int_lt(a: &Alg) -> Rational {
    match a {
        Alg::Rational(r) => Rational::from_integer(r.floor().sub(&Int::from(1))),
        Alg::Irrational { lo, .. } => Rational::from_integer(lo.floor()),
    }
}

/// The least integer in the open interval `(l, u)`, if any.
fn int_in_open(l: &Rational, u: &Rational) -> Option<Int> {
    let lo = if l.is_integer() {
        l.numerator().add(&Int::from(1))
    } else {
        l.ceil()
    };
    let hi = if u.is_integer() {
        u.numerator().sub(&Int::from(1))
    } else {
        u.floor()
    };
    (lo <= hi).then_some(lo)
}

/// A dyadic rational strictly between `l < u` with the fewest fraction bits,
/// the least such (z3's `select_small_core` on rationals).
fn select_small(l: &Rational, u: &Rational) -> Rational {
    if let Some(i) = int_in_open(l, u) {
        return Rational::from_integer(i);
    }
    let two = rat(2);
    let mut scale = rat(1);
    loop {
        scale = scale.mul(&two);
        if let Some(i) = int_in_open(&l.mul(&scale), &u.mul(&scale)) {
            return Rational::from_integer(i).div(&scale);
        }
    }
}

/// A rational strictly between `a < b` (z3's `select`): the isolating
/// intervals are separated first.
fn select_between(a: &Alg, b: &Alg) -> Res<Rational> {
    let (mut a, mut b) = (a.clone(), b.clone());
    for _ in 0..4000 {
        let ahi = a.interval().1;
        let blo = b.interval().0;
        let ok = match (&a, &b) {
            (Alg::Rational(_), Alg::Rational(_)) => ahi < blo,
            _ => ahi <= blo && !(matches!(a, Alg::Rational(_)) && matches!(b, Alg::Rational(_))),
        };
        if ok && ahi < blo {
            return Ok(select_small(&ahi, &blo));
        }
        if ok {
            // Touching endpoints: the shared endpoint is not a root of the
            // irrational side, so it lies strictly between.
            if matches!(a, Alg::Irrational { .. }) && matches!(b, Alg::Irrational { .. }) {
                return Ok(ahi);
            }
        }
        a.refine();
        b.refine();
    }
    Err(Abort)
}

/// The state of an nlsat search over internal variables `0..n` (assigned in
/// that order).
struct Solver {
    num_vars: usize,
    atoms: Vec<Atom>,
    /// The atom of each Boolean variable (`None`: a pure Boolean).
    bool2atom: Vec<Option<usize>>,
    atom_index: BTreeMap<(Kind, Var, u32, Polynomial), u32>,
    bvalues: Vec<LBool>,
    levels: Vec<usize>,
    justs: Vec<Just>,
    clauses: Vec<Clause>,
    learned: Vec<bool>,
    /// Clauses whose maximal arithmetic variable is `x`.
    watches: Vec<Vec<usize>>,
    /// Purely Boolean clauses by maximal Boolean variable.
    bwatches: BTreeMap<u32, Vec<usize>>,
    trail: Vec<Trail>,
    infeasible: Vec<ISet>,
    assignment: Vec<Option<Alg>>,
    /// The current stage (`None`: Boolean stage).
    xk: Option<usize>,
    bk: Option<u32>,
    scope_lvl: usize,
    conflicts: usize,
    max_conflicts: usize,
    rand: RandomGen,
    full_dimensional: bool,
    /// Integer variables (branch and bound on non-integral values).
    is_int: Vec<bool>,
    // Explanation state.
    todo: Vec<Polynomial>,
    todo_extracted: BTreeSet<Polynomial>,
    result: Vec<Lit>,
    add_all_coeffs: bool,
    // Conflict resolution state.
    marks: BTreeSet<u32>,
    num_marks: usize,
    lemma: Vec<Lit>,
    /// Work budget (polynomial operations); exhausted ⇒ abort.
    budget: u64,
    /// Root isolations at the current assignment, by `(x, p)`: valid while
    /// the variables below `x` keep their values.
    root_cache: BTreeMap<(Var, Polynomial), (Vec<Alg>, Vec<i32>)>,
    /// Signs at the current assignment, by `(max_var(p), p)`.
    sign_cache: BTreeMap<(Var, Polynomial), i32>,
    /// Principal subresultant chains, by `(x, p, q)` (z3's polynomial cache).
    psc_cache: BTreeMap<(Var, Polynomial, Polynomial), Vec<Polynomial>>,
    /// Factorizations (`math::factor::factors`), memoized.
    factor_cache: BTreeMap<Polynomial, Vec<Polynomial>>,
    /// The Boolean variable of each atom.
    atom_bool: Vec<u32>,
    /// Each atom's factors with parity and constant sign (`atom_factors`).
    atom_factor_cache: Vec<Option<AtomFactors>>,
    /// Lower-stage factors dropped by core normalization, to project.
    lower_stage_polys: Vec<Polynomial>,
    /// The equation recorded for each stage (`m_var2eq`), by atom.
    var2eq: Vec<Option<usize>>,
}

impl Solver {
    fn new(num_vars: usize) -> Solver {
        Solver {
            num_vars,
            atoms: Vec::new(),
            bool2atom: alloc::vec![None],
            atom_index: BTreeMap::new(),
            bvalues: alloc::vec![LBool::True],
            levels: alloc::vec![0],
            justs: alloc::vec![Just::None],
            clauses: Vec::new(),
            learned: Vec::new(),
            watches: alloc::vec![Vec::new(); num_vars],
            bwatches: BTreeMap::new(),
            trail: Vec::new(),
            infeasible: alloc::vec![ISet::default(); num_vars],
            assignment: alloc::vec![None; num_vars],
            xk: None,
            bk: None,
            scope_lvl: 0,
            conflicts: 0,
            max_conflicts: 4000,
            rand: RandomGen(0),
            full_dimensional: false,
            is_int: alloc::vec![false; num_vars],
            todo: Vec::new(),
            todo_extracted: BTreeSet::new(),
            result: Vec::new(),
            add_all_coeffs: false,
            marks: BTreeSet::new(),
            num_marks: 0,
            lemma: Vec::new(),
            budget: 2_000_000,
            root_cache: BTreeMap::new(),
            sign_cache: BTreeMap::new(),
            psc_cache: BTreeMap::new(),
            factor_cache: BTreeMap::new(),
            atom_bool: Vec::new(),
            atom_factor_cache: Vec::new(),
            lower_stage_polys: Vec::new(),
            var2eq: alloc::vec![None; num_vars],
        }
    }

    fn spend(&mut self, n: u64) -> Res<()> {
        if self.budget < n {
            return Err(Abort);
        }
        self.budget -= n;
        Ok(())
    }

    fn mk_bool_var(&mut self) -> u32 {
        let b = self.bool2atom.len() as u32;
        self.bool2atom.push(None);
        self.bvalues.push(LBool::Undef);
        self.levels.push(usize::MAX);
        self.justs.push(Just::None);
        b
    }

    /// The literal of the inequality atom `p ⋈ 0` (constant folded,
    /// sign-normalized and shared), `mk_ineq_literal`.
    fn mk_ineq_literal(&mut self, kind: Kind, p: &Polynomial) -> Lit {
        if let Some(c) = p.as_constant() {
            let holds = match kind {
                Kind::Eq => c.is_zero(),
                Kind::Lt => c.is_negative(),
                _ => c.is_positive(),
            };
            return if holds { TRUE_LIT } else { FALSE_LIT };
        }
        let (q, flipped) = normalize(p);
        let kind = if flipped { kind.flip() } else { kind };
        let x = max_var(&q).expect("non-constant");
        Lit::new(self.mk_atom(kind, q, x, 0), false)
    }

    fn mk_atom(&mut self, kind: Kind, p: Polynomial, x: Var, i: u32) -> u32 {
        let key = (kind, x, i, p);
        if let Some(&b) = self.atom_index.get(&key) {
            return b;
        }
        let b = self.mk_bool_var();
        let (kind, x, i, p) = key.clone();
        let deg = if kind.is_root() {
            p.degree_of(x)
        } else {
            self.factors_cached(&p)
                .map(|fs| fs.iter().map(|f| f.degree_of(x)).max().unwrap_or(0))
                .unwrap_or_else(|_| p.degree_of(x))
        };
        self.atoms.push(Atom { kind, p, x, i, deg });
        self.atom_bool.push(b);
        self.bool2atom[b as usize] = Some(self.atoms.len() - 1);
        self.atom_index.insert(key, b);
        b
    }

    /// The root atom `x ⋈ root_i(p)`.
    fn mk_root_atom(&mut self, kind: Kind, x: Var, i: u32, p: &Polynomial) -> u32 {
        let (q, _) = normalize(p); // the sign does not change the roots
        self.mk_atom(kind, q, x, i)
    }

    fn atom(&self, b: u32) -> Option<&Atom> {
        self.bool2atom[b as usize].map(|a| &self.atoms[a])
    }

    fn lit_max_var(&self, l: Lit) -> Option<Var> {
        self.atom(l.var()).map(|a| a.x)
    }

    fn clause_max_var(&self, lits: &[Lit]) -> Option<Var> {
        lits.iter().filter_map(|&l| self.lit_max_var(l)).max()
    }

    fn atom_degree(&self, a: &Atom) -> u32 {
        a.deg
    }

    /// z3's `lit_lt`: Boolean literals first, then by maximal variable,
    /// degree, inequalities before equalities, and index.
    fn lit_cmp(&self, l1: Lit, l2: Lit) -> Ordering {
        match (self.atom(l1.var()), self.atom(l2.var())) {
            (None, None) => l1.cmp(&l2),
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a1), Some(a2)) => {
                a1.x.cmp(&a2.x)
                    .then(self.atom_degree(a1).cmp(&self.atom_degree(a2)))
                    .then(a1.kind.is_eq().cmp(&a2.kind.is_eq()))
                    .then(l1.cmp(&l2))
            }
        }
    }

    fn mk_clause(&mut self, mut lits: Vec<Lit>, learned: bool) -> usize {
        if lits.is_empty() {
            lits.push(FALSE_LIT);
        }
        lits.sort_by(|&a, &b| self.lit_cmp(a, b));
        let id = self.clauses.len();
        let mx = self.clause_max_var(&lits);
        let mb = lits.iter().map(|l| l.var()).max().unwrap_or(0);
        self.clauses.push(Clause { lits });
        self.learned.push(learned);
        match mx {
            Some(x) => self.watches[x as usize].push(id),
            None => self.bwatches.entry(mb).or_default().push(id),
        }
        id
    }

    // ----- values -------------------------------------------------------

    fn assigned_value(&self, l: Lit) -> LBool {
        let v = self.bvalues[l.var() as usize];
        if l.sign() { v.not() } else { v }
    }

    fn is_assigned(&self, x: Var) -> bool {
        self.assignment[x as usize].is_some()
    }

    /// The assigned values of variables `0..n`.
    fn point(&self, n: usize) -> Vec<Alg> {
        self.assignment[..n]
            .iter()
            .map(|v| v.clone().expect("lower variables assigned"))
            .collect()
    }

    /// The sign of `p` at the current assignment (every variable of `p`
    /// assigned).
    fn sign(&mut self, p: &Polynomial) -> Res<i32> {
        if let Some(c) = p.as_constant() {
            return Ok(c.signum());
        }
        let mv = max_var(p).expect("non-constant");
        let key = (mv, p.clone());
        if let Some(&s) = self.sign_cache.get(&key) {
            return Ok(s);
        }
        self.spend(1)?;
        let pt = self.point(mv as usize + 1);
        let s = sign_at_point(p, &pt).ok_or(Abort)?;
        self.sign_cache.insert(key, s);
        Ok(s)
    }

    /// Set (or clear) the value of `x`, dropping the cached roots and signs
    /// that depend on it.
    fn set_value(&mut self, x: usize, v: Option<Alg>) {
        self.assignment[x] = v;
        let y = x as Var;
        self.root_cache.retain(|(z, _), _| *z <= y);
        self.sign_cache.retain(|(z, _), _| *z < y);
    }

    /// The real roots of `p` in `x` at the assignment of the variables below
    /// `x`, and the sign of `p` on each sector (`isolate_roots(p, x2v, roots,
    /// signs)`; a polynomial vanishing identically has no roots and sign 0).
    fn roots_signs(&mut self, p: &Polynomial, x: Var) -> Res<(Vec<Alg>, Vec<i32>)> {
        let key = (x, p.clone());
        if let Some(r) = self.root_cache.get(&key) {
            return Ok(r.clone());
        }
        let r = self.roots_signs_core(p, x)?;
        self.root_cache.insert(key, r.clone());
        Ok(r)
    }

    fn roots_signs_core(&mut self, p: &Polynomial, x: Var) -> Res<(Vec<Alg>, Vec<i32>)> {
        self.spend(4)?;
        let pt = self.point(x as usize);
        if p.degree_of(x) == 0 {
            let s = if let Some(c) = p.as_constant() {
                c.signum()
            } else {
                sign_at_point(p, &pt).ok_or(Abort)?
            };
            return Ok((Vec::new(), alloc::vec![s]));
        }
        // The roots of the factors (z3's atoms are factored): smaller
        // polynomials to isolate along the fiber.
        let fs = self.factors_cached(p)?;
        let mut roots = if fs.len() > 1 {
            let mut rs = Vec::new();
            for f in &fs {
                if f.degree_of(x) > 0 {
                    rs.extend(self.roots(f, x)?);
                } else if self.sign(f)? == 0 {
                    // A vanishing factor free of `x`: `p` is identically
                    // zero along the fiber (no roots, sign 0).
                    return Ok((Vec::new(), alloc::vec![0]));
                }
            }
            rs
        } else {
            roots_at(p, &pt, x).ok_or(Abort)?
        };
        roots.sort_by(|a, b| a.compare(b));
        // Factors from a partial factorization may share roots.
        roots.dedup_by(|a, b| a.compare(b) == Ordering::Equal);
        let mut samples: Vec<Rational> = Vec::with_capacity(roots.len() + 1);
        if roots.is_empty() {
            samples.push(zero());
        } else {
            samples.push(int_lt(&roots[0]));
            for i in 0..roots.len() - 1 {
                samples.push(select_between(&roots[i], &roots[i + 1])?);
            }
            samples.push(int_gt(roots.last().expect("non-empty")));
        }
        let mut signs = Vec::with_capacity(samples.len());
        for s in samples {
            let mut q = pt.clone();
            q.push(Alg::Rational(s));
            signs.push(sign_at_point(p, &q).ok_or(Abort)?);
        }
        Ok((roots, signs))
    }

    /// The factors of `p` (memoized).
    fn factors_cached(&mut self, p: &Polynomial) -> Res<Vec<Polynomial>> {
        if let Some(fs) = self.factor_cache.get(p) {
            return Ok(fs.clone());
        }
        self.spend(4)?;
        let fs = crate::math::factor::factors(p);
        self.factor_cache.insert(p.clone(), fs.clone());
        Ok(fs)
    }

    fn roots(&mut self, p: &Polynomial, x: Var) -> Res<Vec<Alg>> {
        Ok(self.roots_signs(p, x)?.0)
    }

    fn satisfied(sign: i32, k: Kind) -> bool {
        (sign == 0 && matches!(k, Kind::Eq | Kind::RootEq | Kind::RootLe | Kind::RootGe))
            || (sign < 0 && matches!(k, Kind::Lt | Kind::RootLt | Kind::RootLe))
            || (sign > 0 && matches!(k, Kind::Gt | Kind::RootGt | Kind::RootGe))
    }

    /// The truth of atom `a` (negated when `neg`) at the assignment of its
    /// maximal variable.
    fn eval_atom(&mut self, a: &Atom, neg: bool) -> Res<bool> {
        let r = if a.kind.is_root() {
            let roots = self.roots(&a.p, a.x)?;
            if a.i as usize > roots.len() {
                return Ok(neg);
            }
            let v = self.assignment[a.x as usize].clone().expect("assigned");
            let s = sgn(v.compare(&roots[a.i as usize - 1]));
            Self::satisfied(s, a.kind)
        } else {
            let s = self.sign(&a.p)?;
            Self::satisfied(s, a.kind)
        };
        Ok(r != neg)
    }

    /// The value of a literal: assigned, or evaluated once its maximal
    /// variable is assigned.
    fn value(&mut self, l: Lit) -> Res<LBool> {
        let v = self.assigned_value(l);
        if v != LBool::Undef {
            return Ok(v);
        }
        let Some(a) = self.atom(l.var()).cloned() else {
            return Ok(LBool::Undef);
        };
        if !self.is_assigned(a.x) {
            return Ok(LBool::Undef);
        }
        Ok(LBool::from(self.eval_atom(&a, l.sign())?))
    }

    fn is_satisfied_clause(&mut self, c: usize) -> Res<bool> {
        for i in 0..self.clauses[c].lits.len() {
            let l = self.clauses[c].lits[i];
            if self.value(l)? == LBool::True {
                return Ok(true);
            }
        }
        Ok(false)
    }

    // ----- infeasible intervals (nlsat_evaluator) ------------------------

    /// The values of the current variable at which literal (`a`, `neg`) is
    /// false.
    fn infeasible_intervals(&mut self, a: &Atom, l: Lit) -> Res<ISet> {
        let neg = l.sign();
        if a.kind.is_root() {
            let roots = self.roots(&a.p, a.x)?;
            if a.i as usize > roots.len() {
                return Ok(if neg {
                    ISet::default()
                } else {
                    ISet::single(Interval::new(true, true, None, true, true, None, l))
                });
            }
            let r = roots[a.i as usize - 1].clone();
            let r = Some(&r);
            let iv = |lo, li, lr, uo, ui, ur| Interval::new(lo, li, lr, uo, ui, ur, l);
            return Ok(match (a.kind, neg) {
                (Kind::RootEq, true) => ISet::single(iv(false, false, r, false, false, r)),
                (Kind::RootEq, false) => ISet::union(
                    &ISet::single(iv(true, true, None, true, false, r)),
                    &ISet::single(iv(true, false, r, true, true, None)),
                ),
                (Kind::RootLt, true) => ISet::single(iv(true, true, None, true, false, r)),
                (Kind::RootLt, false) => ISet::single(iv(false, false, r, true, true, None)),
                (Kind::RootGt, true) => ISet::single(iv(true, false, r, true, true, None)),
                (Kind::RootGt, false) => ISet::single(iv(true, true, None, false, false, r)),
                (Kind::RootLe, true) => ISet::single(iv(true, true, None, false, false, r)),
                (Kind::RootLe, false) => ISet::single(iv(true, false, r, true, true, None)),
                (Kind::RootGe, true) => ISet::single(iv(false, false, r, true, true, None)),
                (Kind::RootGe, false) => ISet::single(iv(true, true, None, true, false, r)),
                _ => unreachable!("root kinds"),
            });
        }
        let (roots, signs) = self.roots_signs(&a.p, a.x)?;
        // Cells: sector 0, root 1, sector 1, …: cell c is a section iff odd.
        let num_cells = roots.len() * 2 + 1;
        let sign_at = |c: usize| if c % 2 == 1 { 0 } else { signs[c / 2] };
        let root = |idx: Option<usize>| idx.map(|i| &roots[i]);
        let mut result = ISet::default();
        let mut prev_sat = true;
        let mut prev_inf = true;
        let mut prev_open = true;
        let mut prev_root: Option<usize> = None;
        for c in 0..num_cells {
            let s = sign_at(c);
            if Self::satisfied(s, a.kind) != neg {
                if !prev_sat {
                    let (curr_open, curr_root) = if c % 2 == 1 {
                        (true, c / 2)
                    } else {
                        (false, (c - 1) / 2)
                    };
                    let set = ISet::single(Interval::new(
                        prev_open,
                        prev_inf,
                        root(prev_root),
                        curr_open,
                        false,
                        Some(&roots[curr_root]),
                        l,
                    ));
                    result = ISet::union(&result, &set);
                    prev_sat = true;
                }
            } else {
                if prev_sat {
                    if c == 0 {
                        if num_cells == 1 {
                            result =
                                ISet::single(Interval::new(true, true, None, true, true, None, l));
                        } else {
                            prev_open = true;
                            prev_inf = true;
                            prev_root = None;
                        }
                    } else {
                        prev_inf = false;
                        if c % 2 == 1 {
                            prev_open = false;
                            prev_root = Some(c / 2);
                        } else {
                            prev_open = true;
                            prev_root = Some((c - 1) / 2);
                        }
                    }
                    prev_sat = false;
                }
                if c == num_cells - 1 && num_cells > 1 {
                    let set = ISet::single(Interval::new(
                        prev_open,
                        prev_inf,
                        root(prev_root),
                        true,
                        true,
                        None,
                        l,
                    ));
                    result = ISet::union(&result, &set);
                }
            }
        }
        Ok(result)
    }

    // ----- trail ----------------------------------------------------------

    fn set_literal_true(&mut self, l: Lit, j: Just) {
        let b = l.var() as usize;
        self.bvalues[b] = LBool::from(!l.sign());
        self.levels[b] = self.scope_lvl;
        self.justs[b] = j;
        self.trail.push(Trail::BAssign(l.var()));
        self.updt_eq(l);
    }

    fn new_level(&mut self) {
        self.scope_lvl += 1;
        self.trail.push(Trail::NewLevel);
    }

    fn decide_literal(&mut self, l: Lit) {
        self.new_level();
        self.set_literal_true(l, Just::Decision);
    }

    fn undo_one(&mut self) -> bool {
        let Some(t) = self.trail.pop() else {
            return false;
        };
        match t {
            Trail::BAssign(b) => {
                self.bvalues[b as usize] = LBool::Undef;
                self.levels[b as usize] = usize::MAX;
                self.justs[b as usize] = Just::None;
                if self.atom(b).is_none() && self.bk.is_none_or(|k| b < k) {
                    self.bk = Some(b);
                }
            }
            Trail::Infeasible(old) => {
                if let Some(x) = self.xk {
                    self.infeasible[x] = old;
                }
            }
            Trail::NewStage => match self.xk {
                Some(0) => self.xk = None,
                Some(x) => {
                    self.xk = Some(x - 1);
                    self.set_value(x - 1, None);
                }
                None => {}
            },
            Trail::NewLevel => self.scope_lvl -= 1,
            Trail::UpdtEq(old) => {
                if let Some(x) = self.xk
                    && x < self.var2eq.len()
                {
                    self.var2eq[x] = old;
                }
            }
        }
        true
    }

    fn undo_until_level(&mut self, lvl: usize) {
        while self.scope_lvl > lvl && self.undo_one() {}
    }

    fn undo_until_stage(&mut self, x: Option<usize>) {
        while self.xk != x && self.undo_one() {}
    }

    fn undo_until_unassigned(&mut self, b: u32) {
        while self.bvalues[b as usize] != LBool::Undef && self.undo_one() {}
    }

    // ----- clause processing ---------------------------------------------

    fn r_propagate(&mut self, l: Lit, s: Option<&ISet>, include_l: bool) {
        let mut core = s.map(|s| s.justifications()).unwrap_or_default();
        if include_l {
            core.push(l.complement());
        }
        self.set_literal_true(l, Just::Lazy(core));
    }

    fn updt_infeasible(&mut self, s: &ISet) {
        let x = self.xk.expect("arith stage");
        let old = self.infeasible[x].clone();
        self.trail.push(Trail::Infeasible(old.clone()));
        self.infeasible[x] = ISet::union(s, &old);
    }

    fn process_boolean_clause(&mut self, c: usize) -> Res<bool> {
        let lits = self.clauses[c].lits.clone();
        let mut num_undef = 0;
        let mut first = None;
        for l in &lits {
            match self.value(*l)? {
                LBool::False => continue,
                LBool::True => return Ok(true),
                LBool::Undef => {
                    num_undef += 1;
                    first.get_or_insert(*l);
                }
            }
        }
        match (num_undef, first) {
            (0, _) => Ok(false),
            (1, Some(l)) => {
                self.set_literal_true(l, Just::Clause(c));
                Ok(true)
            }
            (_, Some(l)) => {
                self.decide_literal(l);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn process_arith_clause(&mut self, c: usize) -> Res<bool> {
        let lits = self.clauses[c].lits.clone();
        let x = self.xk.expect("arith stage");
        let mut num_undef = 0;
        let mut selected: Option<(Lit, ISet)> = None;
        for &l in &lits {
            let v = self.value(l)?;
            if v == LBool::False {
                continue;
            }
            if v == LBool::True {
                return Ok(true);
            }
            let a = self.atom(l.var()).cloned().expect("arith literal");
            let curr = self.infeasible_intervals(&a, l)?;
            let xk_set = self.infeasible[x].clone();

            if curr.is_empty() {
                self.r_propagate(l, None, true);
                return Ok(true);
            }
            if curr.full {
                self.r_propagate(l.complement(), None, true);
                continue;
            }
            if ISet::subset(&curr, &xk_set) {
                self.r_propagate(l, Some(&xk_set), true);
                return Ok(true);
            }
            let tmp = ISet::union(&curr, &xk_set);
            if tmp.full {
                self.r_propagate(l.complement(), Some(&tmp), false);
                continue;
            }
            num_undef += 1;
            if selected.is_none() {
                selected = Some((l, curr));
            }
        }
        if num_undef == 0 {
            return Ok(false);
        }
        let (l, set) = selected.expect("an undefined literal");
        if num_undef == 1 {
            self.set_literal_true(l, Just::Clause(c));
        } else {
            self.decide_literal(l);
        }
        self.updt_infeasible(&set);
        Ok(true)
    }

    fn process_clause(&mut self, c: usize) -> Res<bool> {
        if self.is_satisfied_clause(c)? {
            return Ok(true);
        }
        if self.xk.is_none() {
            self.process_boolean_clause(c)
        } else {
            self.process_arith_clause(c)
        }
    }

    fn process_clauses(&mut self, cs: &[usize]) -> Res<Option<usize>> {
        for &c in cs {
            if !self.process_clause(c)? {
                return Ok(Some(c));
            }
        }
        Ok(None)
    }

    fn peek_next_bool_var(&mut self) {
        let mut b = self.bk.unwrap_or(u32::MAX);
        while (b as usize) < self.bool2atom.len() {
            if self.bool2atom[b as usize].is_none() && self.bvalues[b as usize] == LBool::Undef {
                self.bk = Some(b);
                return;
            }
            b += 1;
        }
        self.bk = None;
    }

    fn new_stage(&mut self) {
        self.trail.push(Trail::NewStage);
        self.xk = Some(self.xk.map_or(0, |x| x + 1));
    }

    /// Assign the current variable a value outside its infeasible set
    /// (`interval_set_manager::pick_in_complement`, randomized as z3).
    fn select_witness(&mut self) -> Res<()> {
        let x = self.xk.expect("arith stage");
        let s = self.infeasible[x].clone();
        let w = self.pick_in_complement(&s)?;
        self.set_value(x, Some(w));
        Ok(())
    }

    fn pick_in_complement(&mut self, s: &ISet) -> Res<Alg> {
        if s.is_empty() {
            return Ok(Alg::Rational(zero()));
        }
        // Zero, when not covered.
        let z = Alg::Rational(zero());
        let mut available = true;
        for iv in &s.ivs {
            let mut sgn_iv = 0;
            if !iv.upper_inf {
                let c = sgn(iv.upper.compare(&z));
                if c < 0 || (c == 0 && iv.upper_open) {
                    sgn_iv = -1;
                }
            }
            if sgn_iv == 0 && !iv.lower_inf {
                let c = sgn(iv.lower.compare(&z));
                if c > 0 || (c == 0 && iv.lower_open) {
                    sgn_iv = 1;
                }
            }
            if sgn_iv == 0 {
                available = false;
                break;
            }
            if sgn_iv > 0 {
                break;
            }
        }
        if available {
            return Ok(z);
        }
        let num = s.ivs.len();
        let mut n = 0u32;
        let mut w: Option<Alg> = None;
        if !s.ivs[num - 1].upper_inf {
            n += 1;
            if n == 1 || self.rand.next().is_multiple_of(n) {
                w = Some(Alg::Rational(int_gt(&s.ivs[num - 1].upper)));
            }
        }
        if !s.ivs[0].lower_inf {
            n += 1;
            w = Some(Alg::Rational(int_lt(&s.ivs[0].lower)));
        }
        for i in 1..num {
            if s.ivs[i - 1].upper.compare(&s.ivs[i].lower) == Ordering::Less {
                n += 1;
                if n == 1 || self.rand.next().is_multiple_of(n) {
                    w = Some(Alg::Rational(select_between(
                        &s.ivs[i - 1].upper,
                        &s.ivs[i].lower,
                    )?));
                }
            }
        }
        if n > 0 {
            return w.ok_or(Abort);
        }
        // Only isolated points are left: a shared open endpoint.
        let mut irrational = None;
        for i in 1..num {
            if s.ivs[i - 1].upper_open && s.ivs[i].lower_open {
                if matches!(s.ivs[i - 1].upper, Alg::Rational(_)) {
                    return Ok(s.ivs[i - 1].upper.clone());
                }
                irrational.get_or_insert(i - 1);
            }
        }
        irrational.map(|i| s.ivs[i].upper.clone()).ok_or(Abort)
    }

    fn is_satisfied_all(&self) -> bool {
        self.bk.is_none() && self.xk.is_some_and(|x| x >= self.num_vars)
    }

    /// The main search loop (`imp::search`).
    fn search(&mut self) -> Res<bool> {
        self.bk = Some(0);
        self.xk = None;
        loop {
            if self.xk.is_none() {
                self.peek_next_bool_var();
                if self.bk.is_none() {
                    self.new_stage();
                }
            } else {
                self.new_stage();
            }
            if self.is_satisfied_all() {
                return Ok(true);
            }
            loop {
                let cs: Vec<usize> = match self.xk {
                    None => self
                        .bwatches
                        .get(&self.bk.expect("a Boolean stage"))
                        .cloned()
                        .unwrap_or_default(),
                    Some(x) if x < self.num_vars => self.watches[x].clone(),
                    Some(_) => Vec::new(),
                };
                let Some(conflict) = self.process_clauses(&cs)? else {
                    break;
                };
                if !self.resolve(conflict)? {
                    return Ok(false);
                }
                if self.conflicts >= self.max_conflicts {
                    return Err(Abort);
                }
            }
            match self.xk {
                None => {
                    let b = self.bk.expect("a Boolean stage");
                    if self.bvalues[b as usize] == LBool::Undef {
                        self.decide_literal(Lit::new(b, true));
                    }
                    self.bk = Some(b + 1);
                }
                Some(x) if x < self.num_vars => self.select_witness()?,
                Some(_) => {}
            }
        }
    }

    /// Undo the whole trail: back to the Boolean stage at level 0.
    fn undo_all(&mut self) {
        while self.undo_one() {}
    }

    /// `search`, then branch and bound on the integer variables
    /// (`search_check`): a satisfying assignment giving an integer variable
    /// `x` a non-integral value `v` adds the valid (over the integers) clause
    /// `x ≤ ⌊v⌋ ∨ x ≥ ⌊v⌋ + 1` and searches again.
    fn search_check(&mut self) -> Res<bool> {
        for _ in 0..1000 {
            if !self.search()? {
                return Ok(false);
            }
            let mut bounds = Vec::new();
            for x in 0..self.num_vars {
                if !self.is_int[x] {
                    continue;
                }
                let v = self.assignment[x].clone().expect("assigned");
                if matches!(&v, Alg::Rational(r) if r.is_integer()) {
                    continue;
                }
                bounds.push((x, alg_floor(&v)));
            }
            if bounds.is_empty() {
                return Ok(true);
            }
            self.undo_all();
            for (x, lo) in bounds {
                let xp = Polynomial::var(x as Var);
                let lo_r = Rational::from_integer(lo.clone());
                let hi_r = Rational::from_integer(lo.add(&Int::from(1)));
                // ¬(x − lo > 0) ∨ ¬(x − (lo + 1) < 0)
                let l1 = self
                    .mk_ineq_literal(Kind::Gt, &xp.sub(&Polynomial::constant(lo_r)))
                    .complement();
                let l2 = self
                    .mk_ineq_literal(Kind::Lt, &xp.sub(&Polynomial::constant(hi_r)))
                    .complement();
                self.mk_clause(alloc::vec![l1, l2], true);
            }
        }
        Err(Abort)
    }

    // ----- conflict resolution ---------------------------------------------

    fn process_antecedent(&mut self, l: Lit) -> Res<()> {
        let b = l.var();
        if self.assigned_value(l) == LBool::Undef {
            // False in the current arithmetic interpretation (an earlier stage).
            if self.marks.insert(b) {
                self.lemma.push(l);
            }
            return Ok(());
        }
        if self.marks.insert(b) {
            let same_stage = self.lit_max_var(l).map(|v| v as usize) == self.xk;
            if self.levels[b as usize] == self.scope_lvl && same_stage {
                self.num_marks += 1;
            } else {
                self.lemma.push(l);
            }
        }
        Ok(())
    }

    fn resolve_clause_lits(&mut self, b: Option<u32>, lits: &[Lit]) -> Res<()> {
        for &l in lits {
            if Some(l.var()) != b {
                self.process_antecedent(l)?;
            }
        }
        Ok(())
    }

    fn resolve_lazy(&mut self, b: u32, core: &[Lit]) -> Res<()> {
        let mut clause = self.explain(core)?;
        for &l in core {
            clause.push(l.complement());
        }
        self.resolve_clause_lits(Some(b), &clause)
    }

    fn only_previous_stages(&self, ls: &[Lit]) -> bool {
        ls.iter()
            .all(|&l| self.lit_max_var(l).map(|v| v as usize) != self.xk)
    }

    fn max_scope_lvl(&self, ls: &[Lit]) -> usize {
        ls.iter()
            .filter(|&&l| self.assigned_value(l) == LBool::False)
            .map(|&l| self.levels[l.var() as usize])
            .max()
            .unwrap_or(0)
    }

    fn remove_literals_from_lvl(&mut self, lvl: usize) {
        let xk = self.xk;
        let lemma = core::mem::take(&mut self.lemma);
        for l in lemma {
            let b = l.var();
            if self.assigned_value(l) == LBool::False
                && self.levels[b as usize] == lvl
                && self.lit_max_var(l).map(|v| v as usize) == xk
            {
                self.num_marks += 1;
                continue;
            }
            self.lemma.push(l);
        }
    }

    fn is_bool_lemma(&self, ls: &[Lit]) -> bool {
        ls.iter().all(|l| self.atom(l.var()).is_none())
    }

    fn find_new_level_arith_lemma(&self, ls: &[Lit]) -> usize {
        let mut new_lvl = None;
        for &l in &ls[..ls.len() - 1] {
            if self.lit_max_var(l).map(|v| v as usize) == self.xk {
                let lv = self.levels[l.var() as usize];
                new_lvl = Some(new_lvl.map_or(lv, |m: usize| m.max(lv)));
            }
        }
        new_lvl.unwrap_or(self.scope_lvl.saturating_sub(1))
    }

    /// Resolve a conflicting clause (`imp::resolve`); `false` when the empty
    /// clause was derived.
    fn resolve(&mut self, conflict: usize) -> Res<bool> {
        let mut conflict_lits = self.clauses[conflict].lits.clone();
        let mut conflict_id = Some(conflict);
        loop {
            self.conflicts += 1;
            if self.conflicts >= self.max_conflicts {
                return Err(Abort);
            }
            self.num_marks = 0;
            self.lemma.clear();
            self.marks.clear();
            self.resolve_clause_lits(None, &conflict_lits)?;
            let mut top = self.trail.len();
            let mut found_decision;
            loop {
                found_decision = false;
                while self.num_marks > 0 {
                    if top == 0 {
                        return Err(Abort);
                    }
                    if let Trail::BAssign(b) = self.trail[top - 1].clone()
                        && self.marks.contains(&b)
                    {
                        self.num_marks -= 1;
                        self.marks.remove(&b);
                        match self.justs[b as usize].clone() {
                            Just::Clause(c) => {
                                let lits = self.clauses[c].lits.clone();
                                self.resolve_clause_lits(Some(b), &lits)?;
                            }
                            Just::Lazy(core) => self.resolve_lazy(b, &core)?,
                            Just::Decision => {
                                found_decision = true;
                                let v = self.bvalues[b as usize] == LBool::True;
                                self.lemma.push(Lit::new(b, v));
                            }
                            Just::None => return Err(Abort),
                        }
                    }
                    top -= 1;
                }
                if found_decision {
                    break;
                }
                let lemma = self.lemma.clone();
                if self.only_previous_stages(&lemma) {
                    break;
                }
                let max_lvl = self.max_scope_lvl(&lemma);
                if max_lvl >= self.scope_lvl {
                    return Err(Abort);
                }
                self.remove_literals_from_lvl(max_lvl);
                self.undo_until_level(max_lvl);
                top = self.trail.len();
            }
            if self.lemma.is_empty() {
                return Ok(false);
            }
            self.marks.clear();
            let lemma = self.lemma.clone();
            let new_cls = if !found_decision {
                let new_max = self.clause_max_var(&lemma).map(|v| v as usize);
                self.undo_until_stage(new_max);
                self.mk_clause(lemma, true)
            } else {
                if self.is_bool_lemma(&lemma) {
                    let b = lemma[lemma.len() - 1].var();
                    self.undo_until_unassigned(b);
                } else {
                    let lvl = self.find_new_level_arith_lemma(&lemma);
                    self.undo_until_level(lvl);
                }
                if let Some(cid) = conflict_id
                    && self.lemma_is_clause(cid)
                {
                    if !self.process_clause(cid)? {
                        return Err(Abort);
                    }
                    return Ok(true);
                }
                self.mk_clause(lemma, true)
            };
            if self.process_clause(new_cls)? {
                return Ok(true);
            }
            conflict_lits = self.clauses[new_cls].lits.clone();
            conflict_id = Some(new_cls);
        }
    }

    fn lemma_is_clause(&self, c: usize) -> bool {
        let cl = &self.clauses[c].lits;
        cl.len() == self.lemma.len() && self.lemma.iter().all(|l| cl.contains(l))
    }

    // ----- explanation (nlsat_explain, classic projection) -------------------

    /// A valid clause `result ∨ ¬core`: literals false at the current sample,
    /// describing a cell of the lower variables in which `core` (whose
    /// infeasible sets cover the current variable's line) stays infeasible.
    fn explain(&mut self, core: &[Lit]) -> Res<Vec<Lit>> {
        if core.is_empty() {
            return Ok(Vec::new());
        }
        let mv = core.iter().filter_map(|&l| self.lit_max_var(l)).max();
        if mv == Some(0) && !self.is_assigned(0) {
            return Ok(Vec::new());
        }
        let saved = self.add_all_coeffs;
        let r = loop {
            self.result.clear();
            match self.explain_main(core) {
                Ok(()) => break Ok(core::mem::take(&mut self.result)),
                Err(ExplainErr::Restart) => {
                    if self.add_all_coeffs {
                        break Err(Abort);
                    }
                    self.add_all_coeffs = true;
                }
                Err(ExplainErr::Abort) => break Err(Abort),
            }
        };
        self.add_all_coeffs = saved;
        r
    }

    fn add_literal(&mut self, l: Lit) {
        if l == FALSE_LIT || l == TRUE_LIT {
            return;
        }
        if !self.result.contains(&l) {
            self.result.push(l);
        }
    }

    fn explain_main(&mut self, core: &[Lit]) -> Result<(), ExplainErr> {
        // Core normalization and simplification (z3's `process2` with
        // `simplify_conflicts`).
        let Some(max) = core.iter().filter_map(|&l| self.lit_max_var(l)).max() else {
            return Ok(());
        };
        let mut c = core.to_vec();
        self.lower_stage_polys.clear();
        self.normalize_core(&mut c, max)?;
        self.simplify_core(&mut c, max)?;
        if c.is_empty() {
            return Ok(());
        }
        let mut ps: Vec<Polynomial> = Vec::new();
        for &l in &c {
            let Some(ai) = self.bool2atom[l.var() as usize] else {
                continue;
            };
            if self.atoms[ai].kind.is_root() {
                ps.push(self.atoms[ai].p.clone());
            } else {
                for (f, _) in self.atom_factors(ai)?.0 {
                    ps.push(f);
                }
            }
        }
        ps.extend(core::mem::take(&mut self.lower_stage_polys));
        let max_x = ps.iter().filter_map(max_var).max();
        let Some(max_x) = max_x else {
            return Ok(());
        };
        let mut kept = Vec::new();
        for p in ps {
            let p = self.elim_vanishing(p)?;
            if !p.is_constant() {
                kept.push(p);
            }
        }
        self.project(kept, max_x)
    }

    fn in_todo(&self, p: &Polynomial) -> bool {
        self.todo.contains(p)
    }

    fn insert_fresh_factors_in_todo(&mut self, p: Polynomial) -> Result<(), ExplainErr> {
        let (p, _) = normalize(&p);
        if self.todo_extracted.contains(&p) || p.is_constant() {
            return Ok(());
        }
        let p = self.elim_vanishing(p)?;
        if p.is_constant() {
            return Ok(());
        }
        // The irreducible factors replace `p`: the same zero set, smaller
        // projections.
        self.spend(4)?;
        for f in crate::math::factor::factors(&p) {
            let f = self.elim_vanishing(f)?;
            if f.is_constant() {
                continue;
            }
            let (f, _) = normalize(&f);
            if !self.todo_extracted.contains(&f) && !self.in_todo(&f) {
                self.todo.push(f);
            }
        }
        Ok(())
    }

    /// Drop the leading coefficients of `p` that vanish at the sample, adding
    /// the assumptions that they vanish (`elim_vanishing`).
    fn elim_vanishing(&mut self, mut p: Polynomial) -> Result<Polynomial, ExplainErr> {
        let Some(mut x) = max_var(&p) else {
            return Ok(p);
        };
        let mut k = p.degree_of(x);
        loop {
            if p.is_constant() {
                return Ok(p);
            }
            if k == 0 {
                x = max_var(&p).expect("non-constant");
                k = p.degree_of(x);
            }
            let lc = p.coeff_of_var(x, k);
            if lc.as_constant().is_some_and(|c| !c.is_zero()) {
                return Ok(p);
            }
            // reduct = p - lc·x^k
            let xk = Polynomial::from_terms(alloc::vec![(
                Rational::from_integer(Int::from(1)),
                Monomial::from_powers(&[(x, k)])
            )]);
            let reduct = p.sub(&lc.mul(&xk));
            self.insert_fresh_factors_in_todo(lc.clone())?;
            if !lc.is_zero() && self.sign(&lc)? != 0 {
                return Ok(p);
            }
            if k == 0 {
                if self.add_all_coeffs {
                    self.add_zero_assumption(&lc)?;
                    return Ok(Polynomial::zero());
                }
                return Err(ExplainErr::Restart);
            }
            self.add_zero_assumption(&lc)?;
            k -= 1;
            p = reduct;
        }
    }

    /// The root of `p` (in its maximal variable) at which the sample lies,
    /// or the closest roots below and above it, over polynomials `ps` with
    /// maximal variable `y` (`find_cell_roots`).
    #[allow(clippy::type_complexity)]
    fn find_cell_roots(
        &mut self,
        ps: &[Polynomial],
        y: Var,
    ) -> Res<(
        Option<(Polynomial, u32)>,
        Option<(Polynomial, u32, Alg)>,
        Option<(Polynomial, u32, Alg)>,
    )> {
        let y_val = self.assignment[y as usize].clone().expect("assigned");
        let mut lower: Option<(Polynomial, u32, Alg)> = None;
        let mut upper: Option<(Polynomial, u32, Alg)> = None;
        for p in ps {
            if max_var(p) != Some(y) {
                continue;
            }
            let roots = self.roots(p, y)?;
            let mut all_lt = true;
            for (i, r) in roots.iter().enumerate() {
                match y_val.compare(r) {
                    Ordering::Equal => return Ok((Some((p.clone(), i as u32 + 1)), None, None)),
                    Ordering::Less => {
                        if i > 0 {
                            let j = i - 1;
                            if lower
                                .as_ref()
                                .is_none_or(|(_, _, l)| l.compare(&roots[j]) == Ordering::Less)
                            {
                                lower = Some((p.clone(), j as u32 + 1, roots[j].clone()));
                            }
                        }
                        if upper
                            .as_ref()
                            .is_none_or(|(_, _, u)| r.compare(u) == Ordering::Less)
                        {
                            upper = Some((p.clone(), i as u32 + 1, r.clone()));
                        }
                        all_lt = false;
                        break;
                    }
                    Ordering::Greater => {}
                }
            }
            if all_lt && !roots.is_empty() {
                let j = roots.len() - 1;
                if lower
                    .as_ref()
                    .is_none_or(|(_, _, l)| l.compare(&roots[j]) == Ordering::Less)
                {
                    lower = Some((p.clone(), j as u32 + 1, roots[j].clone()));
                }
            }
        }
        Ok((None, lower, upper))
    }

    fn add_zero_assumption(&mut self, p: &Polynomial) -> Result<(), ExplainErr> {
        if p.is_constant() {
            return Ok(());
        }
        // A square-free representative (z3's `square_free`): the product of
        // the distinct factors.
        let mut q = Polynomial::constant(Rational::from_integer(Int::from(1)));
        for f in self.factors_cached(p)? {
            q = q.mul(&f);
        }
        if q.is_constant() {
            return Ok(());
        }
        let y = max_var(&q).expect("non-constant");
        if let (Some((q, i)), _, _) = self.find_cell_roots(core::slice::from_ref(&q), y)? {
            self.add_root_literal(Kind::RootEq, y, i, &q)?;
        }
        Ok(())
    }

    /// Add the negation of `p ⋈ 0` (true at the sample) to the lemma.
    fn add_assumption(&mut self, kind: Kind, p: &Polynomial, sign: bool) {
        let l = self.mk_ineq_literal(kind, p);
        let l = if sign { l } else { l.complement() };
        self.add_literal(l);
    }

    fn add_root_literal(
        &mut self,
        kind: Kind,
        y: Var,
        i: u32,
        p: &Polynomial,
    ) -> Result<(), ExplainErr> {
        // A root of a polynomial linear in `y` with a constant coefficient is
        // an inequality (`mk_linear_root`).
        if p.degree_of(y) == 1
            && let Some(c) = p.coeff_of_var(y, 1).as_constant()
        {
            self.mk_linear_root(kind, p, c.is_negative());
            return Ok(());
        }
        if self.mk_quadratic_root(kind, y, i, p)? {
            return Ok(());
        }
        let b = self.mk_root_atom(kind, y, i, p);
        self.add_literal(Lit::new(b, true));
        Ok(())
    }

    /// The root literal of `p`, linear in its variable, as an inequality
    /// (`mk_linear_root`; `neg`: the coefficient is negative).
    fn mk_linear_root(&mut self, kind: Kind, p: &Polynomial, neg: bool) {
        let p = if neg { p.neg() } else { p.clone() };
        let (k, lsign) = match kind {
            Kind::RootEq => (Kind::Eq, false),
            Kind::RootLt => (Kind::Lt, false),
            Kind::RootGt => (Kind::Gt, false),
            Kind::RootLe => (Kind::Gt, true),
            Kind::RootGe => (Kind::Lt, true),
            _ => unreachable!("root kinds"),
        };
        self.add_assumption(k, &p, lsign);
    }

    /// A pseudo-linear root: `q` linear in `y` with a coefficient of known
    /// sign (`mk_plinear_root`).
    fn mk_plinear_root(&mut self, kind: Kind, y: Var, q: &Polynomial) -> Result<bool, ExplainErr> {
        if q.degree_of(y) != 1 {
            return Ok(false);
        }
        let c = q.coeff_of_var(y, 1);
        let s = self.sign(&c)?;
        if s == 0 {
            return Ok(false);
        }
        self.ensure_sign(&c)?;
        self.mk_linear_root(kind, q, s < 0);
        Ok(true)
    }

    /// The root literal of a quadratic `p = A·y² + B·y + C` by the signs of
    /// the discriminant, `A`, `p' = 2A·y + B` and `p` (Thom's lemma,
    /// `mk_quadratic_root`): those signs, fixed in the cell, place `y` with
    /// respect to both roots.
    fn mk_quadratic_root(
        &mut self,
        kind: Kind,
        y: Var,
        i: u32,
        p: &Polynomial,
    ) -> Result<bool, ExplainErr> {
        if p.degree_of(y) != 2 || (i != 1 && i != 2) {
            return Ok(false);
        }
        let a = p.coeff_of_var(y, 2);
        let b = p.coeff_of_var(y, 1);
        let c = p.coeff_of_var(y, 0);
        let four = Rational::from_integer(Int::from(4));
        let q = b.mul(&b).sub(&a.mul(&c).scale(&four));
        let yy = Polynomial::var(y);
        let two = Rational::from_integer(Int::from(2));
        let (p_diff, _) = normalize(&a.mul(&yy).scale(&two).add(&b));
        let sq = self.ensure_sign_quad(&q)?;
        if sq < 0 {
            return Ok(false);
        }
        let sa = self.ensure_sign_quad(&a)?;
        if sa == 0 {
            let q = b.mul(&yy).add(&c);
            return self.mk_plinear_root(kind, y, &q);
        }
        self.ensure_sign(&p_diff)?;
        if sq > 0 {
            self.ensure_sign(p)?;
        }
        Ok(true)
    }

    /// Add the current sign of `p` as an assumption and `p` to the projection
    /// (`ensure_sign`).
    fn ensure_sign(&mut self, p: &Polynomial) -> Result<(), ExplainErr> {
        if p.is_constant() {
            return Ok(());
        }
        self.ensure_sign_quad(p).map(|_| ())
    }

    /// [`Self::ensure_sign`], returning the sign (`ensure_sign_quad`).
    fn ensure_sign_quad(&mut self, p: &Polynomial) -> Result<i32, ExplainErr> {
        let s = self.sign(p)?;
        if !p.is_constant() {
            let k = match s {
                0 => Kind::Eq,
                s if s < 0 => Kind::Lt,
                _ => Kind::Gt,
            };
            self.add_assumption(k, p, false);
            self.insert_fresh_factors_in_todo(p.clone())?;
        }
        Ok(s)
    }

    fn add_cell_lits(&mut self, ps: &[Polynomial], y: Var) -> Result<Vec<Polynomial>, ExplainErr> {
        let mut samples = Vec::new();
        let (eq, lower, upper) = self.find_cell_roots(ps, y)?;
        if let Some((p, i)) = eq {
            self.add_root_literal(Kind::RootEq, y, i, &p)?;
            samples.push(p);
            return Ok(samples);
        }
        if let Some((p, i, _)) = lower {
            let k = if self.full_dimensional {
                Kind::RootGe
            } else {
                Kind::RootGt
            };
            self.add_root_literal(k, y, i, &p)?;
            samples.push(p);
        }
        if let Some((p, i, _)) = upper {
            let k = if self.full_dimensional {
                Kind::RootLe
            } else {
                Kind::RootLt
            };
            self.add_root_literal(k, y, i, &p)?;
            samples.push(p);
        }
        Ok(samples)
    }

    /// Remove and return the todo polynomials with the greatest maximal
    /// variable.
    fn extract_max_polys(&mut self) -> (Option<Var>, Vec<Polynomial>) {
        let x = self.todo.iter().filter_map(max_var).max();
        let Some(x) = x else {
            self.todo.clear();
            return (None, Vec::new());
        };
        let (mine, rest): (Vec<Polynomial>, Vec<Polynomial>) = core::mem::take(&mut self.todo)
            .into_iter()
            .partition(|p| max_var(p) == Some(x));
        self.todo = rest;
        for p in &mine {
            self.todo_extracted.insert(p.clone());
        }
        (Some(x), mine)
    }

    fn add_lcs(&mut self, ps: &[Polynomial], x: Var) -> Result<(), ExplainErr> {
        for p in ps {
            let k = p.degree_of(x);
            if k == 0 {
                continue;
            }
            for j in (0..=k).rev() {
                self.insert_fresh_factors_in_todo(p.coeff_of_var(x, j))?;
                if !self.add_all_coeffs {
                    break;
                }
            }
        }
        Ok(())
    }

    /// Add the first nonzero principal subresultant coefficient of `p`, `q`
    /// in `x` (`psc`).
    fn psc(&mut self, p: &Polynomial, q: &Polynomial, x: Var) -> Result<(), ExplainErr> {
        let chain = self.psc_chain_cached(p, q, x)?;
        let s = chain[0].clone();
        if s.is_zero() {
            // `p` and `q` share a common factor: project all coefficients.
            if self.add_all_coeffs {
                return Ok(());
            }
            return Err(ExplainErr::Restart);
        }
        if s.is_constant() {
            return Ok(());
        }
        self.insert_fresh_factors_in_todo(s)
    }

    /// [`psc_chain`] of `p` and `q` in `x`, memoized.
    fn psc_chain_cached(&mut self, p: &Polynomial, q: &Polynomial, x: Var) -> Res<Vec<Polynomial>> {
        let key = if p <= q {
            (x, p.clone(), q.clone())
        } else {
            (x, q.clone(), p.clone())
        };
        if let Some(c) = self.psc_cache.get(&key) {
            return Ok(c.clone());
        }
        self.spend(16)?;
        let chain = psc_chain(p, q, x).ok_or(Abort)?;
        self.psc_cache.insert(key, chain.clone());
        Ok(chain)
    }

    fn psc_discriminant(&mut self, ps: &[Polynomial], x: Var) -> Result<(), ExplainErr> {
        for p in ps {
            if p.degree_of(x) < 2 {
                continue;
            }
            let d = p.deriv_var(x);
            self.psc(p, &d, x)?;
        }
        Ok(())
    }

    fn psc_resultant(&mut self, ps: &[Polynomial], x: Var) -> Result<(), ExplainErr> {
        for i in 0..ps.len() {
            for j in i + 1..ps.len() {
                self.psc(&ps[i], &ps[j], x)?;
            }
        }
        Ok(())
    }

    fn psc_resultant_sample(
        &mut self,
        ps: &[Polynomial],
        x: Var,
        samples: &[Polynomial],
    ) -> Result<(), ExplainErr> {
        for p in ps {
            for q in samples {
                if p != q {
                    self.psc(p, q, x)?;
                }
            }
        }
        Ok(())
    }

    fn all_univ(ps: &[Polynomial], x: Var) -> bool {
        ps.iter()
            .all(|p| p.vars().iter().all(|&v| v == x) && max_var(p) == Some(x))
    }

    /// The sample-cell projection (`explain::imp::project`).
    fn project(&mut self, ps: Vec<Polynomial>, max_x: Var) -> Result<(), ExplainErr> {
        if ps.is_empty() {
            return Ok(());
        }
        self.todo.clear();
        self.todo_extracted.clear();
        for p in ps {
            self.insert_fresh_factors_in_todo(p)?;
        }
        // Levelwise single cell (z3's default); when it fails, the explanation
        // restarts in the classic projection with all coefficients.
        if !self.add_all_coeffs {
            let ps = core::mem::take(&mut self.todo);
            return self.levelwise(&ps, max_x);
        }
        let (x, mut ps) = self.extract_max_polys();
        let Some(mut x) = x else {
            return Ok(());
        };
        let mut samples = Vec::new();
        if x < max_x {
            samples = self.add_cell_lits(&ps, x)?;
        }
        let mut first = true;
        loop {
            if Self::all_univ(&ps, x) && self.todo.is_empty() {
                self.todo.clear();
                break;
            }
            self.add_lcs(&ps, x)?;
            self.psc_discriminant(&ps, x)?;
            if first {
                self.psc_resultant(&ps, x)?;
                first = false;
            } else {
                self.psc_resultant_sample(&ps, x, &samples)?;
            }
            if self.todo.is_empty() {
                break;
            }
            let (nx, nps) = self.extract_max_polys();
            let Some(nx) = nx else {
                break;
            };
            x = nx;
            ps = nps;
            samples = self.add_cell_lits(&ps, x)?;
        }
        Ok(())
    }

    fn is_full_dimensional(&self) -> bool {
        self.clauses.iter().all(|c| {
            c.lits.iter().all(|&l| match self.atom(l.var()) {
                None => true,
                // A literal is full-dimensional when it is a strict inequality
                // or a negated equality.
                Some(a) => match a.kind {
                    Kind::Eq | Kind::RootEq => l.sign(),
                    Kind::Lt | Kind::Gt | Kind::RootLt | Kind::RootGt => !l.sign(),
                    Kind::RootLe | Kind::RootGe => l.sign(),
                },
            })
        })
    }

    /// Re-check every input clause at the final assignment, evaluating each
    /// atom exactly (a safety net over the search's bookkeeping).
    fn verify_model(&mut self) -> Res<()> {
        for c in 0..self.clauses.len() {
            if self.learned[c] {
                continue;
            }
            let mut ok = false;
            for i in 0..self.clauses[c].lits.len() {
                let l = self.clauses[c].lits[i];
                let holds = match self.atom(l.var()).cloned() {
                    None => self.assigned_value(l) == LBool::True,
                    Some(a) => self.eval_atom(&a, l.sign())?,
                };
                if holds {
                    ok = true;
                    break;
                }
            }
            if !ok {
                return Err(Abort);
            }
        }
        Ok(())
    }

    /// Sort each variable's watched clauses by degree (`sort_watched_clauses`).
    fn sort_watched_clauses(&mut self) {
        for x in 0..self.num_vars {
            let mut ws = core::mem::take(&mut self.watches[x]);
            let deg = |s: &Self, c: usize| {
                s.clauses[c]
                    .lits
                    .iter()
                    .filter_map(|l| s.atom(l.var()).map(|a| s.atom_degree(a)))
                    .max()
                    .unwrap_or(0)
            };
            ws.sort_by_key(|&c| deg(self, c));
            self.watches[x] = ws;
        }
    }
}

/// The variable order z3's `heuristic_reorder` chooses: higher maximal degree
/// first, then more occurrences (both over the factors of every literal's
/// polynomial, as z3's atoms are factored), then z3's seeded shuffle. Returns
/// `order[k]` = the input variable placed at position `k`.
fn heuristic_order(num_vars: usize, polys: &[&Polynomial]) -> Vec<Var> {
    let mut max_deg = alloc::vec![0u32; num_vars];
    let mut occs = alloc::vec![0usize; num_vars];
    let mut memo: BTreeMap<&Polynomial, Vec<Polynomial>> = BTreeMap::new();
    for &p in polys {
        let fs = memo
            .entry(p)
            .or_insert_with(|| crate::math::factor::factors(p));
        for f in fs.iter() {
            for v in f.vars() {
                let d = f.degree_of(v);
                occs[v as usize] += 1;
                max_deg[v as usize] = max_deg[v as usize].max(d);
            }
        }
    }
    // init_shuffle: the identity shuffled by `random_gen(1)`.
    let mut shuffle: Vec<usize> = (0..num_vars).collect();
    let mut rand = RandomGen(1);
    let mut n = num_vars;
    while n > 0 {
        n -= 1;
        let k = rand.next() as usize % (n + 1);
        shuffle.swap(n, k);
    }
    let mut order: Vec<Var> = (0..num_vars as Var).collect();
    order.sort_by(|&x, &y| {
        max_deg[y as usize]
            .cmp(&max_deg[x as usize])
            .then(occs[y as usize].cmp(&occs[x as usize]))
            .then(shuffle[x as usize].cmp(&shuffle[y as usize]))
    });
    order
}

/// Rename the variables of `p` by `map` (input variable → internal one).
fn rename(p: &Polynomial, map: &[Var]) -> Polynomial {
    Polynomial::from_terms(
        p.terms()
            .iter()
            .map(|(c, m)| {
                let powers: Vec<(Var, u32)> = m
                    .vars()
                    .map(|v| (map[v as usize], m.degree_of(v)))
                    .collect();
                let mut powers = powers;
                powers.sort();
                (c.clone(), Monomial::from_powers(&powers))
            })
            .collect(),
    )
}

/// Decide a CNF over polynomial constraints in `num_vars` real variables and
/// `num_bools` Boolean variables.
pub fn check(num_vars: usize, num_bools: usize, clauses: &[Vec<InLit>]) -> NlsatResult {
    check_with_ints(num_vars, num_bools, clauses, &[])
}

/// [`check`] where the input variables `v` with `is_int[v]` range over the
/// integers (branch and bound; a `Sat` assignment gives them integer values,
/// `Unsat` is over the integers for them).
pub fn check_with_ints(
    num_vars: usize,
    num_bools: usize,
    clauses: &[Vec<InLit>],
    is_int: &[bool],
) -> NlsatResult {
    // Variable order.
    let polys: Vec<&Polynomial> = clauses
        .iter()
        .flatten()
        .filter_map(|l| match l {
            InLit::Ineq(p, _, _) => Some(p),
            InLit::Bool(..) => None,
        })
        .collect();
    let order = heuristic_order(num_vars, &polys);
    let mut to_internal = alloc::vec![0 as Var; num_vars];
    for (k, &v) in order.iter().enumerate() {
        to_internal[v as usize] = k as Var;
    }
    let mut s = Solver::new(num_vars);
    for (v, &b) in is_int.iter().enumerate() {
        s.is_int[to_internal[v] as usize] = b;
    }
    let bools: Vec<u32> = (0..num_bools).map(|_| s.mk_bool_var()).collect();
    for c in clauses {
        let mut lits = Vec::new();
        let mut tautology = false;
        for l in c {
            let lit = match l {
                InLit::Bool(b, neg) => Lit::new(bools[*b as usize], *neg),
                InLit::Ineq(p, k, neg) => {
                    let q = rename(p, &to_internal);
                    let lit = s.mk_ineq_literal(*k, &q);
                    if *neg { lit.complement() } else { lit }
                }
            };
            if lit == TRUE_LIT {
                tautology = true;
                break;
            }
            if lit != FALSE_LIT && !lits.contains(&lit) {
                lits.push(lit);
            }
        }
        if tautology {
            continue;
        }
        if lits.is_empty() {
            return NlsatResult::Unsat; // every literal is constantly false
        }
        s.mk_clause(lits, false);
    }
    s.full_dimensional = s.is_full_dimensional();
    s.sort_watched_clauses();
    let verdict = s.search_check().and_then(|sat| {
        if sat {
            s.verify_model()?;
        }
        Ok(sat)
    });
    match verdict {
        Ok(true) => {
            let mut values = alloc::vec![Alg::Rational(zero()); num_vars];
            for (k, &v) in order.iter().enumerate() {
                values[v as usize] = s.assignment[k].clone().unwrap_or(Alg::Rational(zero()));
            }
            let bvals = bools
                .iter()
                .map(|&b| s.bvalues[b as usize] == LBool::True)
                .collect();
            NlsatResult::Sat(values, bvals)
        }
        Ok(false) => NlsatResult::Unsat,
        Err(Abort) => NlsatResult::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        rat(n)
    }
    fn poly(terms: &[(i64, &[(Var, u32)])]) -> Polynomial {
        Polynomial::from_terms(
            terms
                .iter()
                .map(|&(c, m)| (r(c), Monomial::from_powers(m)))
                .collect(),
        )
    }
    fn unit(p: Polynomial, k: Kind) -> Vec<InLit> {
        alloc::vec![InLit::Ineq(p, k, false)]
    }

    #[test]
    fn circle_and_hyperbola_unsat() {
        // x² + y² < 1 ∧ x·y > 1
        let c1 = poly(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (-1, &[])]);
        let c2 = poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]);
        let r = check(2, 0, &[unit(c1, Kind::Lt), unit(c2, Kind::Gt)]);
        assert!(matches!(r, NlsatResult::Unsat), "{r:?}");
    }

    #[test]
    fn irrational_witness_sat() {
        // x² = 2 ∧ x > 0
        let c1 = poly(&[(1, &[(0, 2)]), (-2, &[])]);
        let c2 = poly(&[(1, &[(0, 1)])]);
        match check(1, 0, &[unit(c1, Kind::Eq), unit(c2, Kind::Gt)]) {
            NlsatResult::Sat(v, _) => assert!(matches!(v[0], Alg::Irrational { .. })),
            r => panic!("{r:?}"),
        }
    }

    /// A tiny deterministic generator.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self, n: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 33) % n
        }
    }

    fn random_poly(g: &mut Lcg, nv: u32) -> Polynomial {
        let mut terms = Vec::new();
        for _ in 0..1 + g.next(3) {
            let c = g.next(7) as i64 - 3;
            let mut powers: Vec<(Var, u32)> = Vec::new();
            for _ in 0..g.next(3) {
                let v = g.next(nv as u64) as Var;
                match powers.iter_mut().find(|(w, _)| *w == v) {
                    Some(e) => e.1 += 1,
                    None => powers.push((v, 1)),
                }
            }
            powers.sort();
            terms.push((r(c), Monomial::from_powers(&powers)));
        }
        Polynomial::from_terms(terms)
    }

    /// Differential check against the complete CAD procedure: a CNF is unsat
    /// iff each choice of one literal per clause is an unsat conjunction; a
    /// `Sat` assignment must satisfy every clause exactly.
    #[test]
    fn agrees_with_cad_on_random_cnfs() {
        use crate::nlsat::cad::cad_sat;
        use crate::nlsat::icp::Rel;
        let mut g = Lcg(42);
        let (mut sat, mut unsat) = (0, 0);
        for _ in 0..400 {
            let nv = 1 + g.next(3) as u32;
            let mut clauses: Vec<Vec<(Polynomial, Kind, bool)>> = Vec::new();
            for _ in 0..1 + g.next(5) {
                let mut cl = Vec::new();
                for _ in 0..1 + g.next(3) {
                    let k = [Kind::Eq, Kind::Lt, Kind::Gt][g.next(3) as usize];
                    cl.push((random_poly(&mut g, nv), k, g.next(3) == 0));
                }
                clauses.push(cl);
            }
            let input: Vec<Vec<InLit>> = clauses
                .iter()
                .map(|c| {
                    c.iter()
                        .map(|(p, k, n)| InLit::Ineq(p.clone(), *k, *n))
                        .collect()
                })
                .collect();
            let res = check(nv as usize, 0, &input);
            let rel = |k: Kind, n: bool| match (k, n) {
                (Kind::Eq, false) => Rel::Eq,
                (Kind::Eq, true) => Rel::Ne,
                (Kind::Lt, false) => Rel::Lt,
                (Kind::Lt, true) => Rel::Ge,
                (Kind::Gt, false) => Rel::Gt,
                _ => Rel::Le,
            };
            match res {
                NlsatResult::Sat(vals, _) => {
                    sat += 1;
                    for c in &clauses {
                        assert!(
                            c.iter().any(|(p, k, n)| {
                                let s = sign_at_point(p, &vals).unwrap();
                                crate::nlsat::cad::rel_holds(s, rel(*k, *n))
                            }),
                            "model violates {c:?} in {clauses:?} at {vals:?}"
                        );
                    }
                }
                NlsatResult::Unsat if nv > 2 => unsat += 1,
                NlsatResult::Unsat => {
                    unsat += 1;
                    // Every literal choice must be an unsat conjunction.
                    let mut idx = alloc::vec![0usize; clauses.len()];
                    loop {
                        let conj: Vec<(Polynomial, Rel)> = clauses
                            .iter()
                            .zip(&idx)
                            .map(|(c, &i)| (c[i].0.clone(), rel(c[i].1, c[i].2)))
                            .collect();
                        assert_ne!(cad_sat(&conj, nv as usize), Some(true), "{clauses:?}");
                        let mut k = 0;
                        while k < idx.len() {
                            idx[k] += 1;
                            if idx[k] < clauses[k].len() {
                                break;
                            }
                            idx[k] = 0;
                            k += 1;
                        }
                        if k == idx.len() {
                            break;
                        }
                    }
                }
                NlsatResult::Unknown => {}
            }
        }
        assert!(sat > 20 && unsat > 20, "sat {sat} unsat {unsat}");
    }

    #[test]
    fn disjunction_needs_backjumping() {
        // (x·y > 1 ∨ x > 3) ∧ x < 2 ∧ y < 0 ∧ x > 0  → unsat
        let xy = poly(&[(1, &[(0, 1), (1, 1)]), (-1, &[])]);
        let x3 = poly(&[(1, &[(0, 1)]), (-3, &[])]);
        let x2 = poly(&[(1, &[(0, 1)]), (-2, &[])]);
        let y = poly(&[(1, &[(1, 1)])]);
        let x = poly(&[(1, &[(0, 1)])]);
        let cls = alloc::vec![
            alloc::vec![
                InLit::Ineq(xy, Kind::Gt, false),
                InLit::Ineq(x3, Kind::Gt, false)
            ],
            unit(x2, Kind::Lt),
            unit(y, Kind::Lt),
            unit(x, Kind::Gt),
        ];
        assert!(matches!(check(2, 0, &cls), NlsatResult::Unsat));
    }
}
