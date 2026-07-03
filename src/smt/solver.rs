//! A lazy SMT solver for quantifier-free equality + uninterpreted functions and
//! linear real arithmetic (QF_UF / QF_LRA).
//!
//! This is the offline (lazy) DPLL(T) loop — the conceptual core of
//! `z3/src/smt/smt_context` (Z3 4.17.0, MIT), in its simplest complete form: the
//! SAT engine ([`Solver`]) decides the Boolean skeleton (via
//! [`encode_tracking`]); the theory solvers check the implied atoms — the
//! [`Egraph`] for equality/congruence over uninterpreted sorts, and the
//! Fourier–Motzkin core ([`crate::smt::arith`]) for the linear-arithmetic
//! atoms — and a theory-conflict blocking clause drives the next round.
//!
//! The two theories are checked independently; this is complete when they do not
//! share terms (pure QF_UF, pure QF_LRA, or a disjoint union). Full theory
//! combination (Nelson–Oppen equality sharing), online propagation, and
//! minimized explanations are the refinements that come next. Non-arithmetic,
//! non-equality atoms remain free Booleans.

use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::sat::literal::Lit;
use crate::sat::solver::{SatResult, Solver};
use crate::sat::tseitin::encode_tracking;
use crate::smt::arith::{Constraint, LinExpr, feasible_with_diseqs};
use crate::smt::euf::Egraph;

/// The result of an SMT check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SmtResult {
    /// Satisfiable.
    Sat,
    /// Unsatisfiable.
    Unsat,
}

/// Decide satisfiability of a quantifier-free formula over equality +
/// uninterpreted functions and/or linear arithmetic (QF_UF / QF_LRA, and their
/// union when the theories do not share terms).
pub fn check(m: &AstManager, formula: AstId) -> SmtResult {
    let mut sat = Solver::new();
    let (top, atoms) = encode_tracking(m, formula, &mut sat);
    sat.add_clause(&[top]);

    // Classify theory atoms: equalities over uninterpreted sorts go to EUF;
    // arithmetic comparisons and equalities go to the LRA theory.
    let mut euf_eq: Vec<(Lit, AstId, AstId)> = Vec::new();
    let mut euf_roots: Vec<AstId> = Vec::new();
    let mut arith_atoms: Vec<ArithAtom> = Vec::new();
    for (&atom, &lit) in &atoms {
        if m.is_eq(atom) {
            let args = m.app_args(atom);
            let (a, b) = (args[0], args[1]);
            if m.is_arith_sort(m.get_sort(a)) {
                arith_atoms.push(ArithAtom::eq(lit, a, b));
            } else {
                euf_eq.push((lit, a, b));
                euf_roots.push(a);
                euf_roots.push(b);
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
            SatResult::Unsat => return SmtResult::Unsat,
            SatResult::Sat => {
                if !has_theory {
                    return SmtResult::Sat;
                }
                if euf_consistent(m, &euf_eq, &euf_roots, &sat)
                    && arith_consistent(m, &arith_atoms, &sat)
                {
                    return SmtResult::Sat;
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

fn flip(lit: Lit, sat: &Solver) -> Lit {
    if sat.model_holds(lit) { !lit } else { lit }
}

fn euf_consistent(
    m: &AstManager,
    euf_eq: &[(Lit, AstId, AstId)],
    roots: &[AstId],
    sat: &Solver,
) -> bool {
    if euf_eq.is_empty() {
        return true;
    }
    let mut eqs = Vec::new();
    let mut diseqs = Vec::new();
    for &(lit, a, b) in euf_eq {
        if sat.model_holds(lit) {
            eqs.push((a, b));
        } else {
            diseqs.push((a, b));
        }
    }
    Egraph::new(m, roots).is_consistent(m, &eqs, &diseqs)
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

fn arith_consistent(m: &AstManager, atoms: &[ArithAtom], sat: &Solver) -> bool {
    if atoms.is_empty() {
        return true;
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
    feasible_with_diseqs(&cons, &diseqs)
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
