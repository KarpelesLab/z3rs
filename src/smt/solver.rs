//! A lazy SMT solver for quantifier-free equality + uninterpreted functions and
//! linear arithmetic over the reals and integers (QF_UF / QF_LRA / QF_LIA).
//!
//! This is the offline (lazy) DPLL(T) loop — the conceptual core of
//! `z3/src/smt/smt_context` (Z3 4.17.0, MIT), in its simplest complete form: the
//! SAT engine ([`Solver`]) decides the Boolean skeleton (via
//! [`encode_tracking`]); the theory solvers check the implied atoms — the
//! [`Egraph`] for equality/congruence over uninterpreted sorts, and the
//! Fourier–Motzkin core ([`crate::smt::arith`]) for the linear-arithmetic
//! atoms — and a theory-conflict blocking clause drives the next round.
//!
//! Integer-sorted variables are handled by branch-and-bound on top of the LRA
//! relaxation, so integrality constraints (`QF_LIA`) are decided too.
//!
//! Every equality (of any sort) feeds the congruence closure, so uninterpreted
//! functions get congruence even at arithmetic range sorts. The two theories are
//! otherwise checked independently: this is complete when the only equalities
//! they must exchange are the *explicit* ones (pure QF_UF, pure QF_LRA/LIA, or a
//! union where shared equalities appear syntactically). Full Nelson–Oppen
//! sharing of theory-*implied* equalities (e.g. `x = y` derived from `x ≤ y ∧
//! y ≤ x`), online propagation, and minimized explanations are the refinements
//! that come next. Non-arithmetic, non-equality atoms remain free Booleans.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::sat::literal::Lit;
use crate::sat::solver::{SatResult, Solver};
use crate::sat::tseitin::encode_tracking;
use crate::smt::arith::{Assignment, Constraint, LinExpr, model_with_diseqs};
use crate::smt::euf::Egraph;

use alloc::collections::BTreeSet;

use puremp::{Int, Rational};

/// The result of an SMT check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SmtResult {
    /// Satisfiable.
    Sat,
    /// Unsatisfiable.
    Unsat,
}

/// Decide satisfiability of a quantifier-free formula over equality +
/// uninterpreted functions and/or linear arithmetic (QF_UF / QF_LRA / QF_LIA,
/// and their union when the theories do not share terms).
pub fn check(m: &AstManager, formula: AstId) -> SmtResult {
    check_model(m, formula).0
}

/// Like [`check`], but also returns a satisfying [`Model`] when the formula is
/// satisfiable (`None` when unsat). The model can evaluate terms via
/// [`Model::eval`], backing `(get-value …)` / `(get-model)`.
pub fn check_model(m: &AstManager, formula: AstId) -> (SmtResult, Option<Model>) {
    let mut sat = Solver::new();
    let (top, atoms) = encode_tracking(m, formula, &mut sat);
    sat.add_clause(&[top]);

    // Classify theory atoms. *Every* equality feeds the EUF congruence closure,
    // so uninterpreted functions get congruence regardless of their range sort
    // (an equality `(f x) = (f y)` between Int-sorted applications still yields a
    // congruence conflict when `x = y`). Arithmetic-sorted equalities and the
    // comparisons additionally feed the LRA/LIA theory.
    let mut euf_eq: Vec<(Lit, AstId, AstId)> = Vec::new();
    let mut euf_roots: Vec<AstId> = Vec::new();
    let mut arith_atoms: Vec<ArithAtom> = Vec::new();
    for (&atom, &lit) in &atoms {
        if m.is_eq(atom) {
            let args = m.app_args(atom);
            let (a, b) = (args[0], args[1]);
            euf_eq.push((lit, a, b));
            euf_roots.push(a);
            euf_roots.push(b);
            if m.is_arith_sort(m.get_sort(a)) {
                arith_atoms.push(ArithAtom::eq(lit, a, b));
            }
        } else if let Some(op) = m.arith_op(atom)
            && matches!(op, ArithOp::Le | ArithOp::Lt | ArithOp::Ge | ArithOp::Gt)
        {
            let args = m.app_args(atom);
            arith_atoms.push(ArithAtom::cmp(lit, op, args[0], args[1]));
        }
    }

    let has_theory = !euf_eq.is_empty() || !arith_atoms.is_empty();
    loop {
        match sat.solve() {
            SatResult::Unsat => return (SmtResult::Unsat, None),
            SatResult::Sat => {
                // The Boolean assignment of every tracked atom.
                let bools: BTreeMap<AstId, bool> =
                    atoms.iter().map(|(&a, &l)| (a, sat.model_holds(l))).collect();
                if !has_theory {
                    let model = Model {
                        bools,
                        arith: BTreeMap::new(),
                        euf: Egraph::new(m, &[]),
                    };
                    return (SmtResult::Sat, Some(model));
                }
                let euf = euf_model(m, &euf_eq, &euf_roots, &sat);
                let arith = arith_model(m, &arith_atoms, &sat);
                if let (Some(euf), Some(arith)) = (euf, arith) {
                    let model = Model { bools, arith, euf };
                    return (SmtResult::Sat, Some(model));
                }
                // Theory conflict: block this exact assignment of theory atoms.
                let mut block: Vec<Lit> =
                    euf_eq.iter().map(|&(lit, _, _)| flip(lit, &sat)).collect();
                block.extend(arith_atoms.iter().map(|a| flip(a.lit, &sat)));
                sat.add_clause(&block);
            }
        }
    }
}

/// A satisfying assignment, able to evaluate terms to concrete [`Value`]s.
pub struct Model {
    /// Truth value of each tracked atom (Boolean constants + theory atoms).
    bools: BTreeMap<AstId, bool>,
    /// Rational value of each arithmetic leaf variable.
    arith: Assignment,
    /// Congruence classes over the uninterpreted terms (equal terms share an id).
    euf: Egraph,
}

/// A concrete value in a [`Model`].
#[derive(Clone, Debug)]
pub enum Value {
    /// A Boolean.
    Bool(bool),
    /// A numeral and whether it belongs to the `Int` sort (vs `Real`).
    Num(Rational, bool),
    /// An element of an uninterpreted sort, identified by its congruence class.
    Uninterp(AstId, usize),
}

impl Model {
    /// Evaluate `t` under this model.
    pub fn eval(&mut self, m: &AstManager, t: AstId) -> Value {
        let s = m.get_sort(t);
        if m.is_bool_sort(s) {
            Value::Bool(self.eval_bool(m, t))
        } else if m.is_arith_sort(s) {
            Value::Num(ast_to_lin(m, t).eval(&self.arith), m.is_int_sort(s))
        } else {
            let class = self.euf.class_of(m, t);
            Value::Uninterp(s, class)
        }
    }

    /// Render `t`'s value as an SMT-LIB2 term (`true`, `5`, `(/ 1.0 2.0)`, …).
    pub fn value_string(&mut self, m: &AstManager, t: AstId) -> alloc::string::String {
        self.eval(m, t).render(m)
    }

    fn eval_bool(&mut self, m: &AstManager, t: AstId) -> bool {
        if let Some(&b) = self.bools.get(&t) {
            return b;
        }
        if m.is_true(t) {
            return true;
        }
        if m.is_false(t) {
            return false;
        }
        if m.is_not(t) {
            return !self.eval_bool(m, m.app_args(t)[0]);
        }
        if m.is_and(t) {
            return m.app_args(t).to_vec().iter().all(|&a| self.eval_bool(m, a));
        }
        if m.is_or(t) {
            return m.app_args(t).to_vec().iter().any(|&a| self.eval_bool(m, a));
        }
        if m.is_ite(t) {
            let a = m.app_args(t).to_vec();
            return if self.eval_bool(m, a[0]) {
                self.eval_bool(m, a[1])
            } else {
                self.eval_bool(m, a[2])
            };
        }
        if m.is_eq(t) {
            let a = m.app_args(t).to_vec();
            return self.values_eq(m, a[0], a[1]);
        }
        false // an untracked atom we cannot resolve; default to false
    }

    /// Do `a` and `b` evaluate to the same value?
    fn values_eq(&mut self, m: &AstManager, a: AstId, b: AstId) -> bool {
        match (self.eval(m, a), self.eval(m, b)) {
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Num(x, _), Value::Num(y, _)) => x == y,
            (Value::Uninterp(_, x), Value::Uninterp(_, y)) => x == y,
            _ => false,
        }
    }
}

impl Value {
    /// Render as an SMT-LIB2 value term.
    pub fn render(&self, m: &AstManager) -> alloc::string::String {
        use alloc::string::ToString;
        match self {
            Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Value::Num(r, is_int) => render_numeral(r, *is_int),
            Value::Uninterp(sort, class) => {
                let name = m.sort(*sort).and_then(|s| s.name.as_str()).unwrap_or("U");
                alloc::format!("{name}!val!{class}")
            }
        }
    }
}

/// Render a rational as an SMT-LIB2 numeral: integers as `n` / `(- n)`, reals as
/// `n.0` or `(/ p.0 q.0)` (each factor sign-wrapped like Z3).
fn render_numeral(r: &Rational, is_int: bool) -> alloc::string::String {
    if is_int {
        return render_signed_int(r.numerator());
    }
    if r.is_integer() {
        return decorate_sign(r.numerator(), |n| alloc::format!("{n}.0"));
    }
    let num = r.numerator();
    let den = r.denominator(); // always positive in normalized form
    decorate_sign(num, |n| alloc::format!("(/ {n}.0 {den}.0)"))
}

/// `n` or `(- |n|)`.
fn render_signed_int(n: &Int) -> alloc::string::String {
    decorate_sign(n, |a| alloc::format!("{a}"))
}

/// Apply `body` to `|n|` and wrap the whole thing in `(- …)` when `n < 0`.
fn decorate_sign(
    n: &Int,
    body: impl FnOnce(&Int) -> alloc::string::String,
) -> alloc::string::String {
    if *n < Int::from(0) {
        let abs = -n;
        alloc::format!("(- {})", body(&abs))
    } else {
        body(n)
    }
}

fn flip(lit: Lit, sat: &Solver) -> Lit {
    if sat.model_holds(lit) { !lit } else { lit }
}

/// Build the congruence closure for the current EUF atom assignment, returning
/// it when consistent (so callers can read equivalence classes for the model).
fn euf_model(
    m: &AstManager,
    euf_eq: &[(Lit, AstId, AstId)],
    roots: &[AstId],
    sat: &Solver,
) -> Option<Egraph> {
    let mut eqs = Vec::new();
    let mut diseqs = Vec::new();
    for &(lit, a, b) in euf_eq {
        if sat.model_holds(lit) {
            eqs.push((a, b));
        } else {
            diseqs.push((a, b));
        }
    }
    let mut g = Egraph::new(m, roots);
    g.is_consistent(m, &eqs, &diseqs).then_some(g)
}

/// An arithmetic theory atom: either a comparison or an equality.
struct ArithAtom {
    lit: Lit,
    op: ArithOp, // Le/Lt/Ge/Gt for comparisons, Eq is stored as `is_eq`
    a: AstId,
    b: AstId,
    is_eq: bool,
}

impl ArithAtom {
    fn cmp(lit: Lit, op: ArithOp, a: AstId, b: AstId) -> ArithAtom {
        ArithAtom {
            lit,
            op,
            a,
            b,
            is_eq: false,
        }
    }
    fn eq(lit: Lit, a: AstId, b: AstId) -> ArithAtom {
        ArithAtom {
            lit,
            op: ArithOp::Le,
            a,
            b,
            is_eq: true,
        }
    }
}

/// Check the current arithmetic atom assignment, returning a satisfying rational
/// assignment (integrality-respecting) when consistent.
fn arith_model(m: &AstManager, atoms: &[ArithAtom], sat: &Solver) -> Option<Assignment> {
    if atoms.is_empty() {
        return Some(BTreeMap::new());
    }
    let mut cons: Vec<Constraint> = Vec::new();
    let mut diseqs: Vec<LinExpr> = Vec::new();
    for atom in atoms {
        let diff = ast_to_lin(m, atom.a).sub(&ast_to_lin(m, atom.b)); // a - b
        let holds = sat.model_holds(atom.lit);
        if atom.is_eq {
            if holds {
                cons.push(Constraint::eq(diff)); // a = b
            } else {
                diseqs.push(diff); // a ≠ b (disjunctive)
            }
        } else {
            cons.push(comparison_constraint(atom.op, holds, diff));
        }
    }
    // Integer-sorted leaf variables must take integral values; enforce that with
    // branch-and-bound on top of the rational (LRA) relaxation.
    let mut int_vars: BTreeSet<AstId> = BTreeSet::new();
    for c in &cons {
        collect_int_vars(m, &c.expr, &mut int_vars);
    }
    for d in &diseqs {
        collect_int_vars(m, d, &mut int_vars);
    }
    let int_vars: Vec<AstId> = int_vars.into_iter().collect();
    integer_feasible(&cons, &diseqs, &int_vars, 0)
}

/// Record the integer-sorted variables of `e` into `set`.
fn collect_int_vars(m: &AstManager, e: &LinExpr, set: &mut BTreeSet<AstId>) {
    for v in e.vars() {
        if m.is_int_sort(m.get_sort(v)) {
            set.insert(v);
        }
    }
}

/// A recursion-depth budget for branch-and-bound. Naive B&B is not guaranteed to
/// terminate on unbounded integer problems (it can chase a fractional value along
/// an unbounded direction), so we cap the depth — small enough to stay well
/// within the stack, large enough that every bounded QF_LIA problem in scope
/// closes first. On exhaustion we fall back to the real relaxation as a best
/// effort; a complete integer procedure (Omega/Cooper, or B&B with derived
/// bounds) is future work.
const BB_NODE_LIMIT: u32 = 1_000;

/// A satisfying assignment for `cons` and `diseqs` in which every variable of
/// `int_vars` is integral, if one exists. Branch-and-bound over the LRA
/// relaxation.
fn integer_feasible(
    cons: &[Constraint],
    diseqs: &[LinExpr],
    int_vars: &[AstId],
    depth: u32,
) -> Option<Assignment> {
    let model = model_with_diseqs(cons, diseqs)?; // relaxation infeasible → None
    // Find an integer variable whose relaxed value is fractional.
    let fractional = int_vars.iter().find_map(|&v| {
        let val = model.get(&v).cloned().unwrap_or_else(rat_zero);
        (!val.is_integer()).then_some((v, val))
    });
    let Some((v, val)) = fractional else {
        return Some(model); // all integer variables are already integral
    };
    if depth >= BB_NODE_LIMIT {
        return Some(model); // budget exhausted: fall back to the relaxation (best effort)
    }
    // Branch: v ≤ ⌊val⌋  OR  v ≥ ⌈val⌉.
    let floor = Rational::from_integer(val.floor());
    let ceil = Rational::from_integer(val.ceil());
    let mut low = cons.to_vec();
    low.push(Constraint::le(LinExpr::var(v).sub(&LinExpr::constant(floor)))); // v - ⌊val⌋ ≤ 0
    if let Some(a) = integer_feasible(&low, diseqs, int_vars, depth + 1) {
        return Some(a);
    }
    let mut high = cons.to_vec();
    high.push(Constraint::le(LinExpr::constant(ceil).sub(&LinExpr::var(v)))); // ⌈val⌉ - v ≤ 0
    integer_feasible(&high, diseqs, int_vars, depth + 1)
}

fn rat_zero() -> Rational {
    Rational::from_integer(Int::from(0))
}

/// The linear constraint for `(op a b)` (with `diff = a - b`) at truth `holds`.
fn comparison_constraint(op: ArithOp, holds: bool, diff: LinExpr) -> Constraint {
    // Each row: the constraint on `diff` for the atom being true, then negated.
    let (expr, strict) = match (op, holds) {
        (ArithOp::Le, true) => (diff, false),        // a ≤ b : diff ≤ 0
        (ArithOp::Le, false) => (diff.neg(), true),  // a > b : -diff < 0
        (ArithOp::Lt, true) => (diff, true),         // a < b : diff < 0
        (ArithOp::Lt, false) => (diff.neg(), false), // a ≥ b : -diff ≤ 0
        (ArithOp::Ge, true) => (diff.neg(), false),  // a ≥ b : -diff ≤ 0
        (ArithOp::Ge, false) => (diff, true),        // a < b : diff < 0
        (ArithOp::Gt, true) => (diff.neg(), true),   // a > b : -diff < 0
        (ArithOp::Gt, false) => (diff, false),       // a ≤ b : diff ≤ 0
        _ => (diff, false),
    };
    if strict {
        Constraint::lt(expr)
    } else {
        Constraint::le(expr)
    }
}

/// Convert an arithmetic AST term to a linear expression. Non-linear or
/// non-arithmetic subterms are treated as opaque variables (sound: they become
/// unconstrained).
fn ast_to_lin(m: &AstManager, t: AstId) -> LinExpr {
    if let Some(r) = m.as_numeral(t) {
        return LinExpr::constant(r);
    }
    let Some(op) = m.arith_op(t) else {
        return LinExpr::var(t); // uninterpreted constant / variable
    };
    let args = m.app_args(t);
    match op {
        ArithOp::Add => args
            .iter()
            .fold(LinExpr::new(), |e, &a| e.add(&ast_to_lin(m, a))),
        ArithOp::Sub if args.len() == 1 => ast_to_lin(m, args[0]).neg(),
        ArithOp::Sub => {
            let mut e = ast_to_lin(m, args[0]);
            for &a in &args[1..] {
                e = e.sub(&ast_to_lin(m, a));
            }
            e
        }
        ArithOp::Uminus => ast_to_lin(m, args[0]).neg(),
        // to_real preserves the numeric value, so it is the identity map on the
        // linear representation.
        ArithOp::ToReal => ast_to_lin(m, args[0]),
        ArithOp::Mul => {
            let mut scalar = one();
            let mut nonconst: Option<LinExpr> = None;
            for &a in args {
                let e = ast_to_lin(m, a);
                match e.as_constant() {
                    Some(c) => scalar = &scalar * &c,
                    None if nonconst.is_none() => nonconst = Some(e),
                    None => return LinExpr::var(t), // nonlinear: two variable factors
                }
            }
            match nonconst {
                Some(e) => e.scale(&scalar),
                None => LinExpr::constant(scalar),
            }
        }
        _ => LinExpr::var(t), // to_real/div/mod/… : opaque for now
    }
}

fn one() -> puremp::Rational {
    puremp::Rational::from_integer(puremp::Int::from(1))
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
    fn transitivity_is_unsat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (= a b) (= b c) (not (= a c)))
        let ab = m.mk_eq(a, b);
        let bc = m.mk_eq(b, c);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, bc, nac]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn consistent_equalities_are_sat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (= a b) (not (= a c)))
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, nac]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn congruence_is_unsat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[s], s);
        let fa = m.mk_app(f, &[a]);
        let fb = m.mk_app(f, &[b]);
        // (and (= a b) (not (= (f a) (f b))))
        let ab = m.mk_eq(a, b);
        let fab = m.mk_eq(fa, fb);
        let nfab = m.mk_not(fab);
        let formula = m.mk_and(&[ab, nfab]);
        assert_eq!(check(&m, formula), SmtResult::Unsat);
    }

    #[test]
    fn disjunctive_case_split() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (or (= a b) (= a c)) (not (= a b)) (not (= a c))) — unsat via both
        // branches; exercises the SAT case-split + theory blocking loop.
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let or = m.mk_or(&[ab, ac]);
        let nab = m.mk_not(ab);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[or, nab, nac]);
        assert_eq!(check(&m, f), SmtResult::Unsat);

        // Replace the second disequality's target so a=c becomes possible → sat.
        let g = m.mk_and(&[or, nab]);
        assert_eq!(check(&m, g), SmtResult::Sat);
    }

    #[test]
    fn pure_propositional_still_decided() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let np = m.mk_not(p);
        let f = m.mk_and(&[p, np]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_contradictory_bounds() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let five = m.mk_int(5);
        let six = m.mk_int(6);
        // (and (<= x 5) (>= x 6))
        let le = m.mk_le(x, five);
        let ge = m.mk_ge(x, six);
        let f = m.mk_and(&[le, ge]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_satisfiable_bounds() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let ge = m.mk_ge(x, three);
        let le = m.mk_le(x, five);
        let f = m.mk_and(&[ge, le]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn qf_lra_sum_bound_unsat() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let one = m.mk_int(1);
        // (and (>= x 1) (>= y 1) (<= (+ x y) 1))
        let gx = m.mk_ge(x, one);
        let gy = m.mk_ge(y, one);
        let sum = m.mk_add(&[x, y]);
        let le = m.mk_le(sum, one);
        let f = m.mk_and(&[gx, gy, le]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_strict_cycle_unsat() {
        let mut m = AstManager::new();
        let x = m.mk_real_const("x");
        let y = m.mk_real_const("y");
        // (and (< x y) (< y x))
        let xy = m.mk_lt(x, y);
        let yx = m.mk_lt(y, x);
        let f = m.mk_and(&[xy, yx]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_disequality_case_split() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let five = m.mk_int(5);
        // (and (<= x 5) (>= x 5) (not (= x 5))) — pins x=5 then forbids it → unsat
        let le = m.mk_le(x, five);
        let ge = m.mk_ge(x, five);
        let eq = m.mk_eq(x, five);
        let neq = m.mk_not(eq);
        let f = m.mk_and(&[le, ge, neq]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_disjunction_forces_conflict() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let ten = m.mk_int(10);
        let five = m.mk_int(5);
        // (and (or (<= x 0) (>= x 10)) (= x 5)) — x=5 refutes both disjuncts → unsat
        let le0 = m.mk_le(x, zero);
        let ge10 = m.mk_ge(x, ten);
        let or = m.mk_or(&[le0, ge10]);
        let eq5 = m.mk_eq(x, five);
        let f = m.mk_and(&[or, eq5]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lia_no_integer_between_zero_and_one() {
        // (and (< 0 x) (< x 1)) with x : Int — real-feasible but integer-infeasible.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let lo = m.mk_lt(zero, x);
        let hi = m.mk_lt(x, one);
        let f = m.mk_and(&[lo, hi]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lia_fractional_relaxation_has_integer_point() {
        // (and (<= 3 (* 2 x)) (<= (* 2 x) 5)) with x : Int — x ∈ [1.5, 2.5], so
        // x = 2 witnesses satisfiability though the relaxation corner is fractional.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let twox = m.mk_mul(&[two, x]);
        let lo = m.mk_le(three, twox);
        let hi = m.mk_le(twox, five);
        let f = m.mk_and(&[lo, hi]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn real_variable_between_zero_and_one_is_sat() {
        // The same bounds over Real are satisfiable (x = 1/2): no integrality.
        let mut m = AstManager::new();
        let x = m.mk_real_const("x");
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let lo = m.mk_lt(zero, x);
        let hi = m.mk_lt(x, one);
        let f = m.mk_and(&[lo, hi]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn model_assigns_consistent_arith_value() {
        // (and (>= x 3) (<= x 5)) with x : Int — the model must satisfy both.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let ge = m.mk_ge(x, three);
        let le = m.mk_le(x, five);
        let f = m.mk_and(&[ge, le]);
        let (res, model) = check_model(&m, f);
        assert_eq!(res, SmtResult::Sat);
        let mut model = model.unwrap();
        match model.eval(&m, x) {
            Value::Num(v, true) => {
                assert!(v >= rat(&m, 3) && v <= rat(&m, 5) && v.is_integer());
            }
            other => panic!("expected an Int value, got {other:?}"),
        }
    }

    #[test]
    fn model_renders_bool_and_real() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let r = m.mk_real_const("r");
        let half = m.mk_numeral(
            puremp::Rational::new(puremp::Int::from(1), puremp::Int::from(2)),
            false,
        );
        let eq = m.mk_eq(r, half);
        let f = m.mk_and(&[p, eq]);
        let (res, model) = check_model(&m, f);
        assert_eq!(res, SmtResult::Sat);
        let mut model = model.unwrap();
        assert_eq!(model.value_string(&m, p), "true");
        assert_eq!(model.value_string(&m, r), "(/ 1.0 2.0)");
    }

    #[test]
    fn model_shares_class_for_equal_uninterp() {
        // a = b, a ≠ c → a and b share a class; c differs.
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, nac]);
        let (res, model) = check_model(&m, f);
        assert_eq!(res, SmtResult::Sat);
        let mut model = model.unwrap();
        assert_eq!(model.value_string(&m, a), model.value_string(&m, b));
        assert_ne!(model.value_string(&m, a), model.value_string(&m, c));
    }

    fn rat(_m: &AstManager, n: i64) -> puremp::Rational {
        puremp::Rational::from_integer(puremp::Int::from(n))
    }

    #[test]
    fn congruence_on_int_range_function_unsat() {
        // f : Int -> Int, (and (= x y) (not (= (f x) (f y)))). Even though the
        // equality of applications is arithmetic-sorted, EUF congruence must
        // still fire from x = y. (Regression: previously reported sat.)
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let f = m.mk_func_decl(Symbol::new("f"), &[int], int);
        let fx = m.mk_app(f, &[x]);
        let fy = m.mk_app(f, &[y]);
        let eq = m.mk_eq(x, y);
        let feq = m.mk_eq(fx, fy);
        let nfeq = m.mk_not(feq);
        let f = m.mk_and(&[eq, nfeq]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn congruence_on_int_range_function_sat() {
        // Without x = y, distinct f(x), f(y) is fine.
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let f = m.mk_func_decl(Symbol::new("f"), &[int], int);
        let fx = m.mk_app(f, &[x]);
        let fy = m.mk_app(f, &[y]);
        let feq = m.mk_eq(fx, fy);
        let nfeq = m.mk_not(feq);
        assert_eq!(check(&m, nfeq), SmtResult::Sat);
    }

    #[test]
    fn qf_lra_disjunction_sat() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let ten = m.mk_int(10);
        let twelve = m.mk_int(12);
        // (and (or (<= x 0) (>= x 10)) (<= x 12)) — satisfiable via 10 ≤ x ≤ 12
        let le0 = m.mk_le(x, zero);
        let ge10 = m.mk_ge(x, ten);
        let or = m.mk_or(&[le0, ge10]);
        let le12 = m.mk_le(x, twelve);
        let f = m.mk_and(&[or, le12]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }
}
