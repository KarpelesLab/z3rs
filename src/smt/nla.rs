//! Nonlinear arithmetic by **incremental linearization**: z3's `nla_solver`
//! (`z3/src/math/lp/nla_core.cpp`, `nla_basics_lemmas.cpp`,
//! `nla_tangent_lemmas.cpp`, `nla_monotone_lemmas.cpp`, MIT) on top of the
//! DPLL(T) search of [`crate::smt::solver`].
//!
//! The linear engine sees every nonlinear product as an opaque variable (see
//! [`ast_to_lin`]). After each satisfying assignment, every product whose
//! value disagrees with the product of its factors' values is *refined*: a
//! lemma valid in the theory of (integer or real) arithmetic, linear in the
//! product and its factors, that the current assignment violates, joins the
//! search as a clause, and the search resumes. The lemma schemes are z3's:
//!
//! - **zero**: `a = 0 → ab = 0`, and `ab = 0 → a = 0 ∨ b = 0`;
//! - **sign**: `a > 0 ∧ b < 0 → ab < 0` (and the other sign patterns);
//! - **monotonicity**: `|aᵢ| ≥ |vᵢ| (same signs) → |a₁⋯aₙ| ≥ |v₁⋯vₙ|`, and
//!   the dual upper bound;
//! - **tangent lines** `a = v → ab = v·b`, and **tangent planes**
//!   `(a − p)(b − q) ≷ 0` at two points around the assignment, as z3 picks
//!   them (moved away from the assignment while they still cut it off).
//!
//! Integer variables keep the search's branch and bound, so integer and mixed
//! problems are refined the same way.
//!
//! Products of more than two factors are split into binary products by
//! definitional equalities (`xyz = x·(yz)`, both sides the same value in every
//! interpretation), so the refinement only ever looks at `a·b`.
//!
//! **Soundness.** Every lemma and every definitional equality is valid, so
//! an `unsat` of the strengthened abstraction is an `unsat` of the goal. A
//! `sat` is reported only when every product agrees with its factors under
//! the assignment and the goal itself evaluates to true in the resulting model.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use puremp::{Int, Rational};

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::smt::solver::{Model, SmtCore, SmtResult, Value, ast_to_lin};

/// A binary product `t = a·b` under refinement. `factors` are all the
/// factors of `t` (for the monotonicity lemmas), `a` the first and `b` the
/// product of the others.
struct Mon {
    t: AstId,
    a: AstId,
    b: AstId,
    factors: Vec<AstId>,
}

/// The incremental linearization state: the products, and the lemmas
/// asserted so far.
struct Nla {
    mons: Vec<Mon>,
    /// Canonical product term of each sorted factor multiset.
    canon: BTreeMap<Vec<AstId>, AstId>,
    /// The definitional equalities still to assert.
    defs: Vec<AstId>,
    asserted: BTreeSet<AstId>,
}

fn rat(n: i64) -> Rational {
    Rational::from_integer(Int::from(n))
}

/// Whether `t` is a product of at least two non-constant factors (an opaque
/// variable of the linear engine).
fn is_nonlinear_mul(m: &AstManager, t: AstId) -> bool {
    m.arith_op(t) == Some(ArithOp::Mul)
        && m.as_numeral(t).is_none()
        && m.app_args(t)
            .iter()
            .filter(|&&k| ast_to_lin(m, k).as_constant().is_none())
            .count()
            >= 2
}

/// `t`'s constant coefficient and non-constant factors, flattening nested
/// products.
fn flatten(m: &AstManager, t: AstId, coeff: &mut Rational, factors: &mut Vec<AstId>) {
    for &k in m.app_args(t) {
        if let Some(c) = ast_to_lin(m, k).as_constant() {
            *coeff = &*coeff * &c;
        } else if m.arith_op(k) == Some(ArithOp::Mul) {
            flatten(m, k, coeff, factors);
        } else {
            factors.push(k);
        }
    }
}

impl Nla {
    /// The product term of the (sorted) factor multiset `fs`, registered
    /// for refinement.
    fn product(&mut self, m: &mut AstManager, fs: &[AstId]) -> AstId {
        if fs.len() == 1 {
            return fs[0];
        }
        if let Some(&p) = self.canon.get(fs) {
            return p;
        }
        let p = m.mk_mul(fs);
        self.canon.insert(fs.to_vec(), p);
        let b = self.product(m, &fs[1..]);
        if fs.len() > 2 {
            // `p = a·b` with `b` the product of the other factors: both are
            // the product of `fs`.
            let ab = m.mk_mul(&[fs[0], b]);
            let d = m.mk_eq(p, ab);
            self.defs.push(d);
            self.mons.push(Mon {
                t: ab,
                a: fs[0],
                b,
                factors: fs.to_vec(),
            });
        } else {
            self.mons.push(Mon {
                t: p,
                a: fs[0],
                b,
                factors: fs.to_vec(),
            });
        }
        p
    }

    /// Register the nonlinear product `t` of the goal: `t = c·P` for its
    /// coefficient `c` and the canonical product `P` of its factors.
    fn register(&mut self, m: &mut AstManager, t: AstId) {
        let mut c = rat(1);
        let mut fs = Vec::new();
        flatten(m, t, &mut c, &mut fs);
        if fs.len() < 2 {
            return;
        }
        fs.sort();
        let p = self.product(m, &fs);
        if p != t {
            let is_int = m.is_int_sort(m.get_sort(t));
            let rhs = if c.is_one() {
                p
            } else {
                let k = m.mk_numeral(c, is_int);
                m.mk_mul(&[k, p])
            };
            let d = m.mk_eq(t, rhs);
            self.defs.push(d);
        }
    }
}

/// The value of the arithmetic term `t` in `model`.
fn val(model: &mut Model, m: &AstManager, t: AstId) -> Rational {
    match model.eval(m, t) {
        Value::Num(r, _) => r,
        _ => rat(0),
    }
}

/// Lemma construction over the terms of one product.
struct Builder<'a> {
    m: &'a mut AstManager,
}

impl Builder<'_> {
    fn is_int(&self, t: AstId) -> bool {
        self.m.is_int_sort(self.m.get_sort(t))
    }

    /// A numeral of `t`'s sort; `None` for a fraction at an integer sort.
    fn num(&mut self, like: AstId, r: &Rational) -> Option<AstId> {
        let int = self.is_int(like);
        if int && !r.is_integer() {
            return None;
        }
        Some(self.m.mk_numeral(r.clone(), int))
    }

    /// `Σ cᵢ·tᵢ` (all terms of the same sort).
    fn sum(&mut self, terms: &[(Rational, AstId)]) -> Option<AstId> {
        let mut out = Vec::new();
        for (c, t) in terms {
            if c.is_zero() {
                continue;
            }
            out.push(if c.is_one() {
                *t
            } else {
                let k = self.num(*t, c)?;
                self.m.mk_mul(&[k, *t])
            });
        }
        Some(match out.len() {
            0 => self.num(terms[0].1, &rat(0))?,
            1 => out[0],
            _ => self.m.mk_add(&out),
        })
    }

    /// `t op k` for `op` among `<`, `≤`, `=`, `≥`, `>` (as -2..=2).
    fn cmp(&mut self, t: AstId, op: i8, k: &Rational) -> Option<AstId> {
        let k = self.num(t, k)?;
        Some(match op {
            -2 => self.m.mk_lt(t, k),
            -1 => self.m.mk_le(t, k),
            0 => self.m.mk_eq(t, k),
            1 => self.m.mk_ge(t, k),
            _ => self.m.mk_gt(t, k),
        })
    }

    /// `t ≠ k`.
    fn ne(&mut self, t: AstId, k: &Rational) -> Option<AstId> {
        let e = self.cmp(t, 0, k)?;
        Some(self.m.mk_not(e))
    }

    /// z3's `negate_relation`: the literal putting `t` (of value `v`) on the
    /// other side of `p` — `t ≥ p` when `v < p`, `t ≤ p` when `v > p`.
    fn away(&mut self, t: AstId, v: &Rational, p: &Rational) -> Option<AstId> {
        match v.cmp(p) {
            core::cmp::Ordering::Less => self.cmp(t, 1, p),
            core::cmp::Ordering::Greater => self.cmp(t, -1, p),
            core::cmp::Ordering::Equal => None,
        }
    }

    fn clause(&mut self, lits: Vec<Option<AstId>>) -> Option<AstId> {
        let mut lits: Vec<AstId> = lits.into_iter().collect::<Option<_>>()?;
        lits.dedup();
        let mut seen = BTreeSet::new();
        lits.retain(|l| seen.insert(*l));
        Some(if lits.len() == 1 {
            lits[0]
        } else {
            self.m.mk_or(&lits)
        })
    }
}

/// Sign of `r` as -1, 0, 1.
fn sign(r: &Rational) -> i8 {
    if r.is_zero() {
        0
    } else if r.is_negative() {
        -1
    } else {
        1
    }
}

/// The tangent-plane lemma at `pl` for `t = a·b` at the assignment
/// `(va, vb)`: `(a − pl.x)(b − pl.y)` keeps the sign it has in the region of
/// the assignment.
fn plane(
    bld: &mut Builder<'_>,
    mon: &Mon,
    va: &Rational,
    vb: &Rational,
    pl: &(Rational, Rational),
    below: bool,
) -> Option<AstId> {
    let la = bld.away(mon.a, va, &pl.0)?;
    let lb = bld.away(mon.b, vb, &pl.1)?;
    // t − pl.y·a − pl.x·b  ≷  −pl.x·pl.y
    let e = bld.sum(&[
        (rat(1), mon.t),
        (-pl.1.clone(), mon.a),
        (-pl.0.clone(), mon.b),
    ])?;
    let k = -(&pl.0 * &pl.1);
    let lt = bld.cmp(e, if below { 2 } else { -2 }, &k)?;
    bld.clause(alloc::vec![Some(la), Some(lb), Some(lt)])
}

/// The values of one violated product under the assignment.
struct Violation {
    mon: usize,
    va: Rational,
    vb: Rational,
    vt: Rational,
}

/// z3's basic lemmas (`nla_basics_lemmas`) refuting the value `vt` of
/// `t = a·b`: zero and sign lemmas (none when the signs already agree).
fn basic_lemmas(bld: &mut Builder<'_>, mon: &Mon, v: &Violation, out: &mut Vec<AstId>) {
    let (va, vb, vt) = (&v.va, &v.vb, &v.vt);
    let correct = va * vb;
    let zero = rat(0);
    let mut push = |l: Option<AstId>| {
        if let Some(l) = l {
            out.push(l);
        }
    };
    if va.is_zero() || vb.is_zero() {
        // a = 0 → ab = 0.
        for (f, v) in [(mon.a, va), (mon.b, vb)] {
            if v.is_zero() {
                let l = bld.ne(f, &zero);
                let r = bld.cmp(mon.t, 0, &zero);
                push(bld.clause(alloc::vec![l, r]));
            }
        }
    } else if vt.is_zero() {
        // ab = 0 → a = 0 ∨ b = 0.
        let l = bld.ne(mon.t, &zero);
        let a = bld.cmp(mon.a, 0, &zero);
        let b = bld.cmp(mon.b, 0, &zero);
        push(bld.clause(alloc::vec![l, a, b]));
    } else if sign(vt) != sign(&correct) {
        // The sign of ab from the signs of a and b.
        let la = bld.cmp(mon.a, if va.is_negative() { 1 } else { -1 }, &zero);
        let lb = bld.cmp(mon.b, if vb.is_negative() { 1 } else { -1 }, &zero);
        let lt = bld.cmp(mon.t, if correct.is_negative() { -2 } else { 2 }, &zero);
        push(bld.clause(alloc::vec![la, lb, lt]));
    }
}

/// z3's monotonicity lemma (`nla_monotone_lemmas`) over all the factors of
/// `t`, then its tangent lines and planes (`nla_tangent_lemmas`) for
/// `t = a·b`.
fn tangent_lemmas(
    bld: &mut Builder<'_>,
    model: &mut Model,
    mon: &Mon,
    v: &Violation,
    out: &mut Vec<AstId>,
) {
    let (va, vb, vt) = (&v.va, &v.vb, &v.vt);
    let correct = va * vb;
    let zero = rat(0);
    let mut push = |l: Option<AstId>| {
        if let Some(l) = l {
            out.push(l);
        }
    };
    // z3's binomial sign order lemmas (`order_lemma_on_binomial_sign`), with
    // either factor as `x`: for `y > 0`, `x ≤ v → xy ≤ v·y` (`x ≥ v → xy ≥
    // v·y`), mirrored for `y < 0`, the side the assignment gets wrong.
    if !va.is_zero() && !vb.is_zero() {
        let sign = sign(&(vt - &correct));
        for (x, vx, y, vy) in [(mon.a, va, mon.b, vb), (mon.b, vb, mon.a, va)] {
            let sy = self::sign(vy);
            let ly = bld.cmp(y, if sy == 1 { -1 } else { 1 }, &zero);
            let lx = bld.cmp(x, if sy * sign == 1 { 2 } else { -2 }, vx);
            let e = bld.sum(&[(rat(1), mon.t), (-vx.clone(), y)]);
            let lt = e.and_then(|e| bld.cmp(e, if sign == 1 { -1 } else { 1 }, &zero));
            push(bld.clause(alloc::vec![ly, lx, lt]));
            if mon.a == mon.b {
                break;
            }
        }
    }
    // Monotonicity: |fᵢ| ≥ |vᵢ| (same signs) → |t| ≥ |Π vᵢ|, or the dual.
    let fvals: Vec<Rational> = mon.factors.iter().map(|&f| val(model, bld.m, f)).collect();
    let prod = fvals.iter().fold(rat(1), |acc, v| &acc * v);
    if !fvals.iter().any(Rational::is_zero) && prod == correct {
        let below_abs = vt.abs() < prod.abs();
        let mut lits = Vec::new();
        for (&f, v) in mon.factors.iter().zip(&fvals) {
            let neg = v.is_negative();
            if below_abs {
                lits.push(bld.cmp(f, if neg { 2 } else { -2 }, v));
            } else {
                lits.push(bld.cmp(f, if neg { -2 } else { 2 }, v));
                lits.push(bld.cmp(f, if neg { 2 } else { -2 }, &zero));
            }
        }
        lits.push(if below_abs == prod.is_negative() {
            bld.cmp(mon.t, -1, &prod)
        } else {
            bld.cmp(mon.t, 1, &prod)
        });
        push(bld.clause(lits));
    }
    // Tangent lines: a = va → t = va·b, and b = vb → t = vb·a.
    let e = bld.sum(&[(rat(1), mon.t), (-va.clone(), mon.b)]);
    let l = bld.ne(mon.a, va);
    let r = e.and_then(|e| bld.cmp(e, 0, &zero));
    push(bld.clause(alloc::vec![l, r]));
    if mon.a != mon.b {
        let e = bld.sum(&[(rat(1), mon.t), (-vb.clone(), mon.a)]);
        let l = bld.ne(mon.b, vb);
        let r = e.and_then(|e| bld.cmp(e, 0, &zero));
        push(bld.clause(alloc::vec![l, r]));
    }
    // Tangent planes at two points around the assignment, each moved away
    // from it while the plane still cuts the assignment off.
    let below = *vt < correct;
    let all_int = va.is_integer() && vb.is_integer() && vt.is_integer();
    let delta = if all_int {
        rat(1)
    } else {
        let d = (&correct - vt).abs();
        if d < rat(1) { d } else { rat(1) }
    };
    let tang = |p: &(Rational, Rational)| &(&p.0 * vb) + &(&(&p.1 * va) - &(&p.0 * &p.1));
    let sgn = if below { rat(1) } else { rat(-1) };
    let cuts = |p: &(Rational, Rational)| {
        let px = tang(p);
        (&(&correct - &px) * &sgn).is_positive() && !(&(&px - vt) * &sgn).is_negative()
    };
    let (pa, pb) = if below {
        ((va - &delta, vb - &delta), (va + &delta, vb + &delta))
    } else {
        ((va - &delta, vb + &delta), (va + &delta, vb - &delta))
    };
    for mut p in [pa, pb] {
        if !cuts(&p) {
            continue;
        }
        let mut del = (&p.0 - va, &p.1 - vb);
        for _ in 0..10 {
            del = (&del.0 * &rat(2), &del.1 * &rat(2));
            let np = (va + &del.0, vb + &del.1);
            if !cuts(&np) {
                break;
            }
            p = np;
        }
        push(plane(bld, mon, va, vb, &p, below));
    }
}

/// The bounds the goal's top-level conjuncts put on its constants: `x ⋈ k`
/// comparisons (strict ones relaxed, or rounded over the integers).
fn constant_bounds(
    m: &AstManager,
    goal: AstId,
) -> BTreeMap<AstId, (Option<Rational>, Option<Rational>)> {
    let mut out: BTreeMap<AstId, (Option<Rational>, Option<Rational>)> = BTreeMap::new();
    let mut stack = alloc::vec![(goal, false)];
    while let Some((t, neg)) = stack.pop() {
        if m.is_not(t) {
            stack.push((m.app_args(t)[0], !neg));
            continue;
        }
        if (m.is_and(t) && !neg) || (m.is_or(t) && neg) {
            stack.extend(m.app_args(t).iter().map(|&a| (a, neg)));
            continue;
        }
        let Some(op) = m.arith_op(t) else { continue };
        if !matches!(op, ArithOp::Le | ArithOp::Lt | ArithOp::Ge | ArithOp::Gt) {
            continue;
        }
        let args = m.app_args(t);
        if args.len() != 2 {
            continue;
        }
        // `e ≤ 0` (or `e ≥ 0`) for e = lhs − rhs, the relation negated under
        // `not`.
        let e = ast_to_lin(m, args[0]).sub(&ast_to_lin(m, args[1]));
        let mut le = matches!(op, ArithOp::Le | ArithOp::Lt);
        // Strict unless negated (`not (x ≤ k)` is `x > k`).
        let strict = matches!(op, ArithOp::Lt | ArithOp::Gt) != neg;
        if neg {
            le = !le;
        }
        let mut vars = e.terms();
        let (Some((x, k)), None) = (vars.next(), vars.next()) else {
            continue;
        };
        if !m.is_uninterp_const(x) {
            continue;
        }
        // k·x + c ≤ 0 ⇔ x ≤ −c/k (k > 0), x ≥ −c/k (k < 0).
        let v = -(e.constant_part() / k);
        let upper = le == k.is_positive();
        let int = m.is_int_sort(m.get_sort(x));
        let entry = out.entry(x).or_insert((None, None));
        if upper {
            let v = match (int, strict) {
                (true, true) => Rational::from_integer(v.ceil().sub(&Int::from(1))),
                (true, false) => Rational::from_integer(v.floor()),
                _ => v,
            };
            if entry.1.as_ref().is_none_or(|h| v < *h) {
                entry.1 = Some(v);
            }
        } else {
            let v = match (int, strict) {
                (true, true) => Rational::from_integer(v.floor().add(&Int::from(1))),
                (true, false) => Rational::from_integer(v.ceil()),
                _ => v,
            };
            if entry.0.as_ref().is_none_or(|l| v > *l) {
                entry.0 = Some(v);
            }
        }
    }
    out
}

/// The interval of `x^k` for `x ∈ [lo, hi]`.
fn power_interval(lo: &Rational, hi: &Rational, k: u32) -> (Rational, Rational) {
    let pow = |r: &Rational| (0..k).fold(rat(1), |acc, _| &acc * r);
    let (a, b) = (pow(lo), pow(hi));
    if k.is_multiple_of(2) && lo.is_negative() && hi.is_positive() {
        (rat(0), if a > b { a } else { b })
    } else if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

/// z3's monomial bounds (`nla_monomial_bounds`), from the bounds the goal
/// puts on the constants: each product of bounded constants lies in the
/// product of their intervals. The lemmas are consequences of the goal.
fn monomial_bounds(m: &mut AstManager, goal: AstId, mons: &[Mon]) -> Vec<AstId> {
    let bounds = constant_bounds(m, goal);
    let mut out = Vec::new();
    for mon in mons {
        let mut powers: BTreeMap<AstId, u32> = BTreeMap::new();
        for &f in &mon.factors {
            *powers.entry(f).or_insert(0) += 1;
        }
        let mut iv = Some((rat(1), rat(1)));
        for (f, k) in &powers {
            let Some((Some(lo), Some(hi))) = bounds.get(f) else {
                iv = None;
                break;
            };
            let (pl, ph) = power_interval(lo, hi, *k);
            let (l, h) = iv.expect("bounded so far");
            let c = [&l * &pl, &l * &ph, &h * &pl, &h * &ph];
            let lo = c.iter().min().expect("four").clone();
            let hi = c.iter().max().expect("four").clone();
            iv = Some((lo, hi));
        }
        let Some((lo, hi)) = iv else { continue };
        let mut bld = Builder { m };
        if let Some(l) = bld.cmp(mon.t, 1, &lo) {
            out.push(l);
        }
        if let Some(h) = bld.cmp(mon.t, -1, &hi) {
            out.push(h);
        }
    }
    out
}

/// Lemmas per refinement round (z3's `nla::core::done`).
const MAX_LEMMAS: usize = 10;

/// The integer search work a final check of a round stands for (see
/// [`NlaSearch::set_work_budget`]).
const WORK_PER_FINAL_CHECK: u64 = 100;

/// The outcome of one round of [`NlaSearch::step`].
pub enum NlaStep {
    /// Decided (or given up: `Unknown`).
    Done(SmtResult, Option<Box<Model>>),
    /// The linear search ran out of its work budget (see
    /// [`NlaSearch::set_work_budget`]); the search may go on with a larger one.
    OutOfBudget,
    /// Refined with new lemmas. `support` is a set of literals (atoms of
    /// the goal and Boolean constants, each with its value) that the
    /// assignment satisfies and that suffice for the goal to hold, when
    /// there is one: a model of that conjunction is a model of the goal,
    /// and its negation is a valid clause once the conjunction is refuted.
    Refined {
        /// The supporting literals.
        support: Option<Vec<(AstId, bool)>>,
    },
}

/// An incremental linearization search over one goal (see the module docs).
pub struct NlaSearch {
    nla: Nla,
    core: SmtCore,
    goal: AstId,
    /// The formulas whose support [`NlaStep::Refined`] reports (see
    /// [`NlaSearch::set_support_roots`]).
    roots: Vec<AstId>,
    round: usize,
}

impl NlaSearch {
    /// The search for `goal`, its products registered.
    pub fn new(m: &mut AstManager, goal: AstId) -> NlaSearch {
        let mut nla = Nla {
            mons: Vec::new(),
            canon: BTreeMap::new(),
            defs: Vec::new(),
            asserted: BTreeSet::new(),
        };
        for t in m.postorder(goal) {
            if is_nonlinear_mul(m, t) {
                nla.register(m, t);
            }
        }
        let mut core = SmtCore::for_manager(m);
        core.branch_only();
        core.eager_equalities();
        core.resume_searches();
        core.assert(m, goal);
        for b in monomial_bounds(m, goal, &nla.mons) {
            if nla.asserted.insert(b) {
                core.assert(m, b);
            }
        }
        NlaSearch {
            nla,
            core,
            goal,
            roots: alloc::vec![goal],
            round: 0,
        }
    }

    /// Report the support of these formulas instead of the goal's: the
    /// goal's conjuncts other than valid ones, whose literals the goal does
    /// not rest on.
    pub fn set_support_roots(&mut self, roots: Vec<AstId>) {
        self.roots = roots;
    }

    /// Bound the integer search of each round by `budget` (see
    /// [`SmtCore::set_work_budget`]), and its final checks by one per
    /// [`WORK_PER_FINAL_CHECK`] of it.
    pub fn set_work_budget(&mut self, budget: u64) {
        self.core.set_work_budget(budget);
        self.core
            .set_round_limit(u32::try_from(budget / WORK_PER_FINAL_CHECK).unwrap_or(u32::MAX));
    }

    /// z3's patching (`nla_patcher`) at the level of models: the
    /// assignment's values of the goal's constants, every product (and every
    /// atom) then evaluated from them, as a model of the goal; failing that,
    /// the same with one constant changed so that one violated product takes
    /// the value the assignment gave it (`patch_monomial` on a factor). The
    /// goal is evaluated in each candidate, so a model returned is a model.
    fn patched_model(
        &self,
        m: &AstManager,
        model: &mut Model,
        viol: &[Violation],
    ) -> Option<Model> {
        let mut nums: BTreeMap<AstId, Rational> = BTreeMap::new();
        let mut bools: BTreeMap<AstId, bool> = BTreeMap::new();
        for t in m.postorder(self.goal) {
            if !m.is_uninterp_const(t) {
                continue;
            }
            let s = m.get_sort(t);
            if m.is_arith_sort(s) {
                let v = val(model, m, t);
                if m.is_int_sort(s) && !v.is_integer() {
                    return None;
                }
                nums.insert(t, v);
            } else if m.is_bool_sort(s) {
                let Value::Bool(b) = model.eval_value(m, t) else {
                    return None;
                };
                bools.insert(t, b);
            } else {
                return None;
            }
        }
        let holds = |nums: &BTreeMap<AstId, Rational>| {
            let mut out = Model::from_bv(BTreeMap::new());
            for (&t, v) in nums {
                out.set_arith(t, v.clone());
            }
            for (&t, &b) in &bools {
                out.set_bool(t, b);
            }
            matches!(out.eval_value(m, self.goal), Value::Bool(true)).then_some(out)
        };
        if let Some(out) = holds(&nums) {
            return Some(out);
        }
        for v in viol.iter().take(MAX_LEMMAS) {
            let fs = &self.nla.mons[v.mon].factors;
            for (i, &f) in fs.iter().enumerate() {
                if !nums.contains_key(&f) || fs.iter().filter(|&&g| g == f).count() > 1 {
                    continue;
                }
                let mut rest = rat(1);
                for (k, &g) in fs.iter().enumerate() {
                    if k != i {
                        rest = &rest * &val(model, m, g);
                    }
                }
                if rest.is_zero() {
                    continue;
                }
                let nv = &v.vt / &rest;
                if m.is_int_sort(m.get_sort(f)) && !nv.is_integer() {
                    continue;
                }
                let mut cand = nums.clone();
                cand.insert(f, nv);
                if let Some(out) = holds(&cand) {
                    return Some(out);
                }
            }
        }
        None
    }

    /// Assert the valid formula `lemma`; `false` when it already was.
    pub fn add_lemma(&mut self, m: &AstManager, lemma: AstId) -> bool {
        if !self.nla.asserted.insert(lemma) {
            return false;
        }
        self.core.assert(m, lemma);
        true
    }

    /// One round: search for an assignment, and refine the products it
    /// gets wrong.
    pub fn step(&mut self, m: &mut AstManager) -> NlaStep {
        for d in core::mem::take(&mut self.nla.defs) {
            self.add_lemma(m, d);
        }
        self.round += 1;
        let (r, model) = self.core.check(m);
        let mut model = match (r, model) {
            (SmtResult::Sat, Some(model)) => model,
            (SmtResult::Sat, None) => return NlaStep::Done(SmtResult::Unknown, None),
            (SmtResult::Unknown, _) => return NlaStep::OutOfBudget,
            (r, _) => return NlaStep::Done(r, None),
        };
        let mut viol = Vec::new();
        for (i, mon) in self.nla.mons.iter().enumerate() {
            let (va, vb, vt) = (
                val(&mut model, m, mon.a),
                val(&mut model, m, mon.b),
                val(&mut model, m, mon.t),
            );
            if &va * &vb != vt {
                viol.push(Violation { mon: i, va, vb, vt });
            }
        }
        if viol.is_empty() {
            return match model.eval_value(m, self.goal) {
                Value::Bool(true) => NlaStep::Done(SmtResult::Sat, Some(Box::new(model))),
                _ => NlaStep::Done(SmtResult::Unknown, None),
            };
        }
        // z3's patching (`nla_patcher`), in its simplest form: the
        // assignment's values of the constants may satisfy the goal once
        // every product takes its true value.
        if let Some(patched) = self.patched_model(m, &mut model, &viol) {
            return NlaStep::Done(SmtResult::Sat, Some(Box::new(patched)));
        }
        let n = viol.len();
        let shift = self.round % n;
        let mut fresh = 0;
        for pass in 0..2 {
            for k in 0..n {
                if fresh >= MAX_LEMMAS {
                    break;
                }
                let v = &viol[(k + shift) % n];
                let mon = &self.nla.mons[v.mon];
                let mon = Mon {
                    t: mon.t,
                    a: mon.a,
                    b: mon.b,
                    factors: mon.factors.clone(),
                };
                let mut out = Vec::new();
                let mut bld = Builder { m };
                if pass == 0 {
                    basic_lemmas(&mut bld, &mon, v, &mut out);
                } else {
                    tangent_lemmas(&mut bld, &mut model, &mon, v, &mut out);
                }
                for l in out {
                    if self.add_lemma(m, l) {
                        fresh += 1;
                    }
                }
            }
            if fresh > 0 {
                break;
            }
        }
        if fresh == 0 {
            return NlaStep::Done(SmtResult::Unknown, None);
        }
        let assigned = self.core.assigned();
        let mut support = Vec::new();
        let mut memo = BTreeMap::new();
        let ok = self
            .roots
            .iter()
            .all(|&r| justify(m, r, true, &assigned, &mut memo, &mut support));
        support.sort();
        support.dedup();
        NlaStep::Refined {
            support: ok.then_some(support),
        }
    }
}

/// Decide `goal` by incremental linearization alone, for at most
/// `max_rounds` rounds.
pub fn check_nla(m: &mut AstManager, goal: AstId, max_rounds: usize) -> (SmtResult, Option<Model>) {
    let mut s = NlaSearch::new(m, goal);
    for _ in 0..max_rounds {
        match s.step(m) {
            NlaStep::Done(r, model) => return (r, model.map(|m| *m)),
            NlaStep::OutOfBudget => break,
            NlaStep::Refined { .. } => {}
        }
    }
    (SmtResult::Unknown, None)
}

/// Whether `t` is a Boolean connective [`bool_value`] evaluates.
fn is_connective(m: &AstManager, t: AstId) -> bool {
    m.is_not(t)
        || m.is_and(t)
        || m.is_or(t)
        || m.is_implies(t)
        || m.is_xor(t)
        || (m.is_ite(t) && m.is_bool_sort(m.get_sort(t)))
        || (m.is_eq(t) && m.is_bool_sort(m.get_sort(m.app_args(t)[0])))
}

/// The value of the Boolean term `t` under the atoms' values `assigned`.
fn bool_value(
    m: &AstManager,
    t: AstId,
    assigned: &BTreeMap<AstId, bool>,
    memo: &mut BTreeMap<AstId, Option<bool>>,
) -> Option<bool> {
    if let Some(&b) = assigned.get(&t) {
        return Some(b);
    }
    if m.is_true(t) {
        return Some(true);
    }
    if m.is_false(t) {
        return Some(false);
    }
    if let Some(&v) = memo.get(&t) {
        return v;
    }
    let v = if is_connective(m, t) {
        let args = m.app_args(t).to_vec();
        let mut vals = Vec::with_capacity(args.len());
        let mut known = true;
        for &a in &args {
            match bool_value(m, a, assigned, memo) {
                Some(b) => vals.push(b),
                None => known = false,
            }
        }
        known.then(|| {
            if m.is_not(t) {
                !vals[0]
            } else if m.is_and(t) {
                vals.iter().all(|&b| b)
            } else if m.is_or(t) {
                vals.iter().any(|&b| b)
            } else if m.is_implies(t) {
                !vals[0] || vals[1]
            } else if m.is_xor(t) {
                vals.iter().fold(false, |acc, &b| acc ^ b)
            } else if m.is_ite(t) {
                if vals[0] { vals[1] } else { vals[2] }
            } else {
                vals.windows(2).all(|w| w[0] == w[1])
            }
        })
    } else {
        None
    };
    memo.insert(t, v);
    v
}

/// Collect into `out` literals `(atom, value)` under which the Boolean term
/// `t` has the value `want`, following z3's relevancy: one true disjunct
/// of a true disjunction, all conjuncts of a true conjunction. The atoms
/// are arithmetic comparisons and Boolean constants. `false` when `t` does
/// not have the value `want` or contains another kind of atom.
fn justify(
    m: &AstManager,
    t: AstId,
    want: bool,
    assigned: &BTreeMap<AstId, bool>,
    memo: &mut BTreeMap<AstId, Option<bool>>,
    out: &mut Vec<(AstId, bool)>,
) -> bool {
    if bool_value(m, t, assigned, memo) != Some(want) {
        return false;
    }
    if m.is_true(t) || m.is_false(t) {
        return true;
    }
    let args = m.app_args(t).to_vec();
    if is_connective(m, t) {
        if m.is_not(t) {
            return justify(m, args[0], !want, assigned, memo, out);
        }
        let conj = (m.is_and(t) && want) || (m.is_or(t) && !want);
        let disj = (m.is_and(t) && !want) || (m.is_or(t) && want);
        if conj {
            return args
                .iter()
                .all(|&a| justify(m, a, want, assigned, memo, out));
        }
        if disj {
            return args
                .iter()
                .find(|&&a| bool_value(m, a, assigned, memo) == Some(want))
                .is_some_and(|&a| justify(m, a, want, assigned, memo, out));
        }
        if m.is_implies(t) {
            return if want {
                if bool_value(m, args[0], assigned, memo) == Some(false) {
                    justify(m, args[0], false, assigned, memo, out)
                } else {
                    justify(m, args[1], true, assigned, memo, out)
                }
            } else {
                justify(m, args[0], true, assigned, memo, out)
                    && justify(m, args[1], false, assigned, memo, out)
            };
        }
        if m.is_ite(t) {
            let Some(c) = bool_value(m, args[0], assigned, memo) else {
                return false;
            };
            return justify(m, args[0], c, assigned, memo, out)
                && justify(m, args[if c { 1 } else { 2 }], want, assigned, memo, out);
        }
        // xor, and equality of Booleans: both sides.
        return args.iter().all(|&a| {
            bool_value(m, a, assigned, memo).is_some_and(|v| justify(m, a, v, assigned, memo, out))
        });
    }
    let arith_atom = (m.is_eq(t) && m.is_arith_sort(m.get_sort(args[0])))
        || matches!(
            m.arith_op(t),
            Some(ArithOp::Le | ArithOp::Lt | ArithOp::Ge | ArithOp::Gt)
        );
    if arith_atom || (m.is_uninterp_const(t) && m.is_bool_sort(m.get_sort(t))) {
        out.push((t, want));
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A value of the tiny test evaluator.
    #[derive(Debug, PartialEq)]
    enum V {
        N(Rational),
        B(bool),
    }

    /// Evaluate `t` with the constants (and products) valued by `env`.
    fn ev(m: &AstManager, t: AstId, env: &BTreeMap<AstId, Rational>) -> V {
        if let Some(r) = m.as_numeral(t) {
            return V::N(r);
        }
        if let Some(r) = env.get(&t) {
            return V::N(r.clone());
        }
        let args = m.app_args(t).to_vec();
        let num = |a: AstId| match ev(m, a, env) {
            V::N(r) => r,
            V::B(_) => panic!("number expected"),
        };
        let boolean = |a: AstId| match ev(m, a, env) {
            V::B(b) => b,
            V::N(_) => panic!("Boolean expected"),
        };
        if m.is_not(t) {
            return V::B(!boolean(args[0]));
        }
        if m.is_or(t) {
            return V::B(args.iter().any(|&a| boolean(a)));
        }
        if m.is_and(t) {
            return V::B(args.iter().all(|&a| boolean(a)));
        }
        if m.is_eq(t) {
            return V::B(num(args[0]) == num(args[1]));
        }
        V::N(match m.arith_op(t).expect("arithmetic") {
            ArithOp::Add => args.iter().fold(rat(0), |acc, &a| &acc + &num(a)),
            ArithOp::Mul => args.iter().fold(rat(1), |acc, &a| &acc * &num(a)),
            ArithOp::Uminus => -num(args[0]),
            ArithOp::Le => return V::B(num(args[0]) <= num(args[1])),
            ArithOp::Lt => return V::B(num(args[0]) < num(args[1])),
            ArithOp::Ge => return V::B(num(args[0]) >= num(args[1])),
            ArithOp::Gt => return V::B(num(args[0]) > num(args[1])),
            op => panic!("unexpected {op:?}"),
        })
    }

    /// A deterministic pseudo-random sequence.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 33) % n
        }

        fn small(&mut self, k: i64, denom: i64) -> Rational {
            let n = self.below((2 * k + 1) as u64) as i64 - k;
            Rational::new(Int::from(n), Int::from(denom))
        }
    }

    /// Every lemma refining a violated product `t = a·b` (and a square
    /// `t = a·a`) must hold wherever `t` is the product: checked on a grid
    /// around many random violated assignments, over the integers and the
    /// reals; and the lemmas must cut the violated assignment off.
    #[test]
    fn lemmas_are_valid_and_cut_off_the_assignment() {
        let mut m = AstManager::new();
        for int in [true, false] {
            let sort = if int {
                m.mk_int_sort()
            } else {
                m.mk_real_sort()
            };
            let k = |m: &mut AstManager, n: &str| {
                let d = m.mk_func_decl(crate::util::symbol::Symbol::new(n), &[], sort);
                m.mk_const(d)
            };
            let x = k(&mut m, if int { "x" } else { "u" });
            let y = k(&mut m, if int { "y" } else { "v" });
            let xy = m.mk_mul(&[x, y]);
            let xx = m.mk_mul(&[x, x]);
            let denom = if int { 1 } else { 2 };
            let mut rng = Rng(if int { 7 } else { 11 });
            for _ in 0..300 {
                let square = rng.below(3) == 0;
                let (t, b) = if square { (xx, x) } else { (xy, y) };
                let mon = Mon {
                    t,
                    a: x,
                    b,
                    factors: alloc::vec![x, b],
                };
                let va = rng.small(6, denom);
                let vb = if square {
                    va.clone()
                } else {
                    rng.small(6, denom)
                };
                let mut vt = rng.small(40, denom);
                if vt == &va * &vb {
                    vt = &vt + &rat(1);
                }
                let mut model = Model::from_bv(BTreeMap::new());
                model.set_arith(x, va.clone());
                model.set_arith(y, vb.clone());
                model.set_arith(t, vt.clone());
                let v = Violation {
                    mon: 0,
                    va: va.clone(),
                    vb: vb.clone(),
                    vt: vt.clone(),
                };
                let mut lemmas = Vec::new();
                let mut bld = Builder { m: &mut m };
                basic_lemmas(&mut bld, &mon, &v, &mut lemmas);
                tangent_lemmas(&mut bld, &mut model, &mon, &v, &mut lemmas);
                assert!(!lemmas.is_empty());
                // The violated assignment falsifies some lemma.
                let at: BTreeMap<AstId, Rational> = [(x, va.clone()), (y, vb.clone()), (t, vt)]
                    .into_iter()
                    .collect();
                assert!(lemmas.iter().any(|&l| ev(&m, l, &at) == V::B(false)));
                // Each lemma holds wherever t = a·b.
                for &l in &lemmas {
                    for i in -10..=10 {
                        for j in -10..=10 {
                            let a = &va + &Rational::new(Int::from(i), Int::from(denom));
                            let b = if square {
                                a.clone()
                            } else {
                                &vb + &Rational::new(Int::from(j), Int::from(denom))
                            };
                            let env: BTreeMap<AstId, Rational> =
                                [(x, a.clone()), (y, b.clone()), (t, &a * &b)]
                                    .into_iter()
                                    .collect();
                            assert_eq!(ev(&m, l, &env), V::B(true), "lemma fails at {a}, {b}");
                        }
                    }
                }
            }
        }
    }

    /// Products of bounded constants are bounded by the product of their
    /// intervals: `−2 ≤ x ≤ 3 ∧ 1 ≤ y < 3` gives `−4 ≤ xy ≤ 6` (`y ≤ 2`
    /// over the integers) and `0 ≤ x² ≤ 9`.
    #[test]
    fn monomial_bounds_from_the_goal() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let (lo, hi) = (m.mk_int(-2), m.mk_int(3));
        let (one, three) = (m.mk_int(1), m.mk_int(3));
        let a = m.mk_le(lo, x);
        let b = m.mk_le(x, hi);
        let c = m.mk_ge(y, one);
        let d = m.mk_lt(y, three);
        let xy = m.mk_mul(&[x, y]);
        let xx = m.mk_mul(&[x, x]);
        let zero = m.mk_int(0);
        let e = m.mk_gt(xy, zero);
        let f = m.mk_gt(xx, zero);
        let goal = m.mk_and(&[a, b, c, d, e, f]);
        let mut nla = Nla {
            mons: Vec::new(),
            canon: BTreeMap::new(),
            defs: Vec::new(),
            asserted: BTreeSet::new(),
        };
        nla.register(&mut m, xy);
        nla.register(&mut m, xx);
        let got: BTreeSet<AstId> = monomial_bounds(&mut m, goal, &nla.mons)
            .into_iter()
            .collect();
        let mut want = BTreeSet::new();
        for (t, l, h) in [(xy, -4, 6), (xx, 0, 9)] {
            let (l, h) = (m.mk_int(l), m.mk_int(h));
            want.insert(m.mk_ge(t, l));
            want.insert(m.mk_le(t, h));
        }
        assert_eq!(got, want);
    }

    /// The support of an assignment: one true disjunct per disjunction,
    /// every conjunct of a conjunction.
    #[test]
    fn justification_follows_relevancy() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let p = {
            let b = m.mk_bool_sort();
            let d = m.mk_func_decl(crate::util::symbol::Symbol::new("p"), &[], b);
            m.mk_const(d)
        };
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let a1 = m.mk_ge(x, zero);
        let a2 = m.mk_le(x, one);
        let or = m.mk_or(&[a1, a2]);
        let np = m.mk_not(p);
        let goal = m.mk_and(&[or, np]);
        let assigned: BTreeMap<AstId, bool> =
            [(a1, false), (a2, true), (p, false)].into_iter().collect();
        let mut out = Vec::new();
        let mut memo = BTreeMap::new();
        assert!(justify(&m, goal, true, &assigned, &mut memo, &mut out));
        out.sort();
        let mut want = alloc::vec![(a2, true), (p, false)];
        want.sort();
        assert_eq!(out, want);
        // A goal the assignment falsifies has no support.
        let assigned: BTreeMap<AstId, bool> =
            [(a1, false), (a2, false), (p, false)].into_iter().collect();
        let mut memo = BTreeMap::new();
        assert!(!justify(
            &m,
            goal,
            true,
            &assigned,
            &mut memo,
            &mut Vec::new()
        ));
    }
}
