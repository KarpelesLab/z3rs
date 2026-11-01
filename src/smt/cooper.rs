//! Cooper's quantifier elimination for linear integer arithmetic (Presburger).
//!
//! A complete decision procedure for the linear-integer quantifier fragment: it
//! eliminates a bound variable from a DNF of linear (in)equalities and
//! divisibility atoms, producing an equivalent DNF over the remaining variables
//! (with divisibility atoms). `∀x` is handled as `¬∃x.¬`. When every variable is
//! eliminated the residual atoms are ground and evaluate to a definite verdict.
//!
//! All expressions are integer-valued; coefficients are stored as [`Rational`]s
//! (always integral here). The construction over-approximates nothing — it is an
//! *exact* equivalence, so both `sat` and `unsat` are sound.

use alloc::vec;
use alloc::vec::Vec;

use puremp::{Int, Rational};

use super::arith::LinExpr;
use crate::ast::AstId;

fn int(n: i64) -> Int {
    Int::from(n)
}
fn rat_int(i: &Int) -> Rational {
    Rational::from_integer(i.clone())
}

/// A Presburger literal (all expressions integer-valued).
#[derive(Clone)]
pub enum Atom {
    /// `e < 0`
    Lt(LinExpr),
    /// `e ≤ 0`
    Le(LinExpr),
    /// `e = 0`
    Eq(LinExpr),
    /// `e ≠ 0`
    Ne(LinExpr),
    /// `m ∣ e` (`m > 0`)
    Div(Int, LinExpr),
    /// `¬(m ∣ e)`
    Ndiv(Int, LinExpr),
}

/// A formula in disjunctive normal form: a union of cubes (conjunctions).
pub type Dnf = Vec<Vec<Atom>>;

fn expr_of(a: &Atom) -> &LinExpr {
    match a {
        Atom::Lt(e) | Atom::Le(e) | Atom::Eq(e) | Atom::Ne(e) => e,
        Atom::Div(_, e) | Atom::Ndiv(_, e) => e,
    }
}

/// Integer coefficient of `x` in `e` (0 if absent). Returns `None` if not integral.
fn icoeff(e: &LinExpr, x: AstId) -> Option<Int> {
    e.coeff_of(x).to_integer()
}

fn has_var(a: &Atom, x: AstId) -> bool {
    !expr_of(a).coeff_of(x).is_zero()
}

/// Multiply the expression (and, for divisibility, the modulus) by a positive
/// integer factor — preserving the atom's meaning.
fn scale_atom(a: &Atom, f: &Int) -> Atom {
    let fr = rat_int(f);
    match a {
        Atom::Lt(e) => Atom::Lt(e.scale(&fr)),
        Atom::Le(e) => Atom::Le(e.scale(&fr)),
        Atom::Eq(e) => Atom::Eq(e.scale(&fr)),
        Atom::Ne(e) => Atom::Ne(e.scale(&fr)),
        Atom::Div(m, e) => Atom::Div(m * f, e.scale(&fr)),
        Atom::Ndiv(m, e) => Atom::Ndiv(m * f, e.scale(&fr)),
    }
}

/// Replace `x`'s coefficient in the atom's expression by its sign (±1), used
/// after scaling so `x`'s coefficient is `±δ`.
fn unitize_x(a: &Atom, x: AstId) -> Atom {
    let e = expr_of(a);
    let c = e.coeff_of(x); // ±δ
    let sign = if c.is_negative() {
        Rational::from_integer(int(-1))
    } else {
        Rational::from_integer(int(1))
    };
    // e' = e − c·x + sign·x
    let e2 = e
        .sub(&LinExpr::var(x).scale(&c))
        .add(&LinExpr::var(x).scale(&sign));
    match a {
        Atom::Lt(_) => Atom::Lt(e2),
        Atom::Le(_) => Atom::Le(e2),
        Atom::Eq(_) => Atom::Eq(e2),
        Atom::Ne(_) => Atom::Ne(e2),
        Atom::Div(m, _) => Atom::Div(m.clone(), e2),
        Atom::Ndiv(m, _) => Atom::Ndiv(m.clone(), e2),
    }
}

/// Substitute `x := val` (a linear expression over the other variables) into the
/// atom.
fn subst(a: &Atom, x: AstId, val: &LinExpr) -> Atom {
    let e = expr_of(a);
    let c = e.coeff_of(x);
    let e2 = e.sub(&LinExpr::var(x).scale(&c)).add(&val.scale(&c));
    match a {
        Atom::Lt(_) => Atom::Lt(e2),
        Atom::Le(_) => Atom::Le(e2),
        Atom::Eq(_) => Atom::Eq(e2),
        Atom::Ne(_) => Atom::Ne(e2),
        Atom::Div(m, _) => Atom::Div(m.clone(), e2),
        Atom::Ndiv(m, _) => Atom::Ndiv(m.clone(), e2),
    }
}

/// If the atom is variable-free, its truth value.
fn eval_ground(a: &Atom) -> Option<bool> {
    let e = expr_of(a);
    if !e.is_constant() {
        return None;
    }
    let k = e.const_term();
    Some(match a {
        Atom::Lt(_) => k.is_negative(),
        Atom::Le(_) => k.is_negative() || k.is_zero(),
        Atom::Eq(_) => k.is_zero(),
        Atom::Ne(_) => !k.is_zero(),
        Atom::Div(m, _) => k.to_integer().is_some_and(|i| i.rem_euclid(m).is_zero()),
        Atom::Ndiv(m, _) => k.to_integer().is_some_and(|i| !i.rem_euclid(m).is_zero()),
    })
}

fn neg_atom(a: &Atom) -> Atom {
    match a {
        Atom::Lt(e) => Atom::Le(e.neg()),
        Atom::Le(e) => Atom::Lt(e.neg()),
        Atom::Eq(e) => Atom::Ne(e.clone()),
        Atom::Ne(e) => Atom::Eq(e.clone()),
        Atom::Div(m, e) => Atom::Ndiv(m.clone(), e.clone()),
        Atom::Ndiv(m, e) => Atom::Div(m.clone(), e.clone()),
    }
}

/// The `−∞` limit of an atom in `x` (`x`-coefficient already `±1`): bound atoms
/// collapse to `true`/`false`; divisibility atoms are periodic, so they are kept.
/// Returns `None` for "keep as-is" (divisibilities), `Some(b)` for a constant.
fn minus_inf(a: &Atom, x: AstId) -> Option<bool> {
    let e = expr_of(a);
    let c = e.coeff_of(x); // ±1
    let neg = c.is_negative();
    match a {
        // e = x + t < 0 → as x→−∞: true; e = −x + t < 0 → x > t → false.
        Atom::Lt(_) | Atom::Le(_) => Some(!neg),
        Atom::Eq(_) => Some(false),
        Atom::Ne(_) => Some(true),
        Atom::Div(_, _) | Atom::Ndiv(_, _) => None,
    }
}

/// Eliminate `x` from a single cube `∃x. ⋀ atoms`, returning an equivalent DNF.
fn cube_exists(cube: &[Atom], x: AstId, budget: &mut u64) -> Option<Dnf> {
    let mut with_x = Vec::new();
    let mut without: Vec<Atom> = Vec::new();
    for a in cube {
        if has_var(a, x) {
            with_x.push(a.clone());
        } else {
            without.push(a.clone());
        }
    }
    if with_x.is_empty() {
        return Some(vec![without]);
    }
    // Normalize `x`'s coefficient to ±1: scale by δ/|c|, unitize, add δ∣x.
    let mut delta = int(1);
    for a in &with_x {
        delta = delta.lcm(&icoeff(expr_of(a), x)?.abs());
    }
    let mut norm: Vec<Atom> = Vec::new();
    for a in &with_x {
        let c = icoeff(expr_of(a), x)?;
        let factor = &delta / &c.abs();
        norm.push(unitize_x(&scale_atom(a, &factor), x));
    }
    if delta != int(1) {
        norm.push(Atom::Div(delta.clone(), LinExpr::var(x)));
    }
    // D = lcm of all divisibility moduli.
    let mut dd = int(1);
    for a in &norm {
        if let Atom::Div(m, _) | Atom::Ndiv(m, _) = a {
            dd = dd.lcm(m);
        }
    }
    let d_span = dd.to_i64().filter(|&n| (1..=5000).contains(&n))?;
    // Lower-bound points B (`x > b`), and the `−∞` cube.
    let mut bset: Vec<LinExpr> = Vec::new();
    let mut minf: Vec<Atom> = Vec::new();
    let mut minf_dead = false;
    for a in &norm {
        let e = expr_of(a);
        let c = e.coeff_of(x);
        let neg = c.is_negative();
        // t = e − c·x (the x-free remainder); with |c|=1, e = ±x + t.
        let t = e.sub(&LinExpr::var(x).scale(&c));
        match a {
            // −x + t < 0 ⇒ x > t (strict lower, b = t). −x + t ≤ 0 ⇒ x ≥ t ⇒ x > t−1.
            Atom::Lt(_) if neg => bset.push(t),
            Atom::Le(_) if neg => bset.push(t.sub(&LinExpr::constant(rat_int(&int(1))))),
            // Equality x = ±t: the single point; feed both bounds via b = point−1.
            Atom::Eq(_) => {
                // e = c·x + t = 0 ⇒ x = −t/c. With c=±1: point = −t·c⁻¹ = −t·c.
                let point = t.scale(&c).neg(); // = −t·c  (c=±1 ⇒ c⁻¹=c)
                bset.push(point.sub(&LinExpr::constant(rat_int(&int(1)))));
            }
            // Disequality x ≠ point: its `x > point` half is a lower bound.
            Atom::Ne(_) => bset.push(t.scale(&c).neg()),
            _ => {}
        }
        match minus_inf(a, x) {
            Some(true) => {}                 // drop (true conjunct)
            Some(false) => minf_dead = true, // the −∞ cube is unsatisfiable
            None => minf.push(a.clone()),    // keep divisibility (periodic)
        }
    }
    let mut out: Dnf = Vec::new();
    // −∞ disjunct: ⋁_{j=1..D} (without ∧ minf[x:=j]) — skipped if a bound atom
    // makes the whole −∞ cube false.
    if !minf_dead {
        for j in 1..=d_span {
            take(budget)?;
            let jv = LinExpr::constant(rat_int(&int(j)));
            let mut c2 = without.clone();
            if push_subst(&mut c2, &minf, x, &jv) {
                out.push(c2);
            }
        }
    }
    // bound disjuncts: ⋁_{b∈B} ⋁_{j=1..D} (without ∧ norm[x:=b+j])
    for b in &bset {
        for j in 1..=d_span {
            take(budget)?;
            let val = b.add(&LinExpr::constant(rat_int(&int(j))));
            let mut c2 = without.clone();
            if push_subst(&mut c2, &norm, x, &val) {
                out.push(c2);
            }
        }
    }
    Some(out)
}

fn take(budget: &mut u64) -> Option<()> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    Some(())
}

/// Append `atoms[x:=val]` to `cube`; return `false` if a substituted atom is a
/// constant `false` (the cube is dead).
fn push_subst(cube: &mut Vec<Atom>, atoms: &[Atom], x: AstId, val: &LinExpr) -> bool {
    for a in atoms {
        let s = subst(a, x, val);
        match eval_ground(&s) {
            Some(true) => {}
            Some(false) => return false,
            None => cube.push(s),
        }
    }
    true
}

/// `∃x. dnf`.
pub fn exists(dnf: &Dnf, x: AstId, budget: &mut u64) -> Option<Dnf> {
    let mut out = Vec::new();
    for cube in dnf {
        out.extend(cube_exists(cube, x, budget)?);
    }
    Some(simplify(out))
}

/// A normalized atom, or its constant truth value.
enum Norm {
    True,
    False,
    Atom(Atom),
}

/// Comparable identity of a (normalized) atom: kind, modulus, terms, constant.
type AtomKey = (u8, Int, Vec<(AstId, Rational)>, Rational);

fn key(a: &Atom) -> AtomKey {
    let (k, m) = match a {
        Atom::Lt(_) => (0, int(0)),
        Atom::Le(_) => (1, int(0)),
        Atom::Eq(_) => (2, int(0)),
        Atom::Ne(_) => (3, int(0)),
        Atom::Div(m, _) => (4, m.clone()),
        Atom::Ndiv(m, _) => (5, m.clone()),
    };
    let e = expr_of(a);
    (
        k,
        m,
        e.terms().map(|(v, c)| (v, c.clone())).collect(),
        e.const_term().clone(),
    )
}

/// Rebuild `Σ cᵢ·vᵢ + k` from terms.
fn build(terms: &[(AstId, Int)], k: &Int) -> LinExpr {
    let mut e = LinExpr::constant(rat_int(k));
    for (v, c) in terms {
        e = e.add(&LinExpr::var(*v).scale(&rat_int(c)));
    }
    e
}

/// Integer normal form: `<` as `≤ −1`, coefficients divided by their gcd
/// (rounding the constant of a bound, deciding an equality's divisibility),
/// equalities sign-normalized, divisibility reduced modulo `m`.
fn normalize(a: &Atom) -> Norm {
    if let Some(b) = eval_ground(a) {
        return if b { Norm::True } else { Norm::False };
    }
    let e = expr_of(a);
    let Some(terms) = e
        .terms()
        .map(|(v, c)| c.to_integer().map(|i| (v, i)))
        .collect::<Option<Vec<_>>>()
    else {
        return Norm::Atom(a.clone());
    };
    let Some(k) = e.const_term().to_integer() else {
        return Norm::Atom(a.clone());
    };
    let g = terms.iter().fold(int(0), |g, (_, c)| g.gcd(&c.abs()));
    let div = |ts: &[(AstId, Int)], d: &Int| -> Vec<(AstId, Int)> {
        ts.iter().map(|(v, c)| (*v, c / d)).collect()
    };
    match a {
        Atom::Lt(_) | Atom::Le(_) => {
            // e ≤ 0 (or e + 1 ≤ 0 for a strict bound) ⇔ Σ (cᵢ/g)·vᵢ + ⌈k/g⌉ ≤ 0.
            let k = if matches!(a, Atom::Lt(_)) {
                &k + &int(1)
            } else {
                k
            };
            let kc = -(&(-&k).div_floor(&g));
            Norm::Atom(Atom::Le(build(&div(&terms, &g), &kc)))
        }
        Atom::Eq(_) | Atom::Ne(_) => {
            let eq = matches!(a, Atom::Eq(_));
            if !k.rem_euclid(&g).is_zero() {
                return if eq { Norm::False } else { Norm::True };
            }
            let mut ts = div(&terms, &g);
            let mut kk = &k / &g;
            if ts.first().is_some_and(|(_, c)| c.is_negative()) {
                ts = ts.into_iter().map(|(v, c)| (v, -c)).collect();
                kk = -kk;
            }
            let e = build(&ts, &kk);
            Norm::Atom(if eq { Atom::Eq(e) } else { Atom::Ne(e) })
        }
        Atom::Div(m, _) | Atom::Ndiv(m, _) => {
            let ts: Vec<(AstId, Int)> = terms
                .iter()
                .map(|(v, c)| (*v, c.rem_euclid(m)))
                .filter(|(_, c)| !c.is_zero())
                .collect();
            let e = build(&ts, &k.rem_euclid(m));
            let r = if matches!(a, Atom::Div(..)) {
                Atom::Div(m.clone(), e)
            } else {
                Atom::Ndiv(m.clone(), e)
            };
            match eval_ground(&r) {
                Some(true) => Norm::True,
                Some(false) => Norm::False,
                None => Norm::Atom(r),
            }
        }
    }
}

/// Normalize every cube, dropping true atoms, false cubes (a false atom,
/// `e = 0 ∧ e ≠ 0`, or bounds `e ≤ 0 ∧ f ≤ 0` with `e + f` a positive
/// constant), duplicates, and cubes subsumed by a smaller one.
fn simplify(dnf: Dnf) -> Dnf {
    let mut cubes: Vec<(alloc::collections::BTreeSet<AtomKey>, Vec<Atom>)> = Vec::new();
    'cube: for cube in dnf {
        let mut keys = alloc::collections::BTreeSet::new();
        let mut atoms: Vec<Atom> = Vec::new();
        for a in &cube {
            match normalize(a) {
                Norm::True => {}
                Norm::False => continue 'cube,
                Norm::Atom(n) => {
                    if keys.insert(key(&n)) {
                        atoms.push(n);
                    }
                }
            }
        }
        for (i, a) in atoms.iter().enumerate() {
            for b in &atoms[i + 1..] {
                let clash = match (a, b) {
                    (Atom::Le(e), Atom::Le(f)) => {
                        let s = e.add(f);
                        s.is_constant() && s.const_term().is_positive()
                    }
                    (Atom::Eq(e), Atom::Ne(f)) | (Atom::Ne(f), Atom::Eq(e)) => {
                        let d = e.sub(f);
                        d.is_constant() && d.const_term().is_zero()
                    }
                    _ => false,
                };
                if clash {
                    continue 'cube;
                }
            }
        }
        cubes.push((keys, atoms));
    }
    cubes.sort_by_key(|(k, _)| k.len());
    let mut kept: Vec<(alloc::collections::BTreeSet<AtomKey>, Vec<Atom>)> = Vec::new();
    for (k, atoms) in cubes {
        if kept.iter().any(|(s, _)| s.is_subset(&k)) {
            continue;
        }
        kept.push((k, atoms));
    }
    kept.into_iter().map(|(_, a)| a).collect()
}

/// Negate a DNF into a DNF (`¬⋁cube = ⋀¬cube`, distributed). Bounded.
fn negate(dnf: &Dnf, budget: &mut u64) -> Option<Dnf> {
    // Start from `true` (one empty cube), and for each cube form the product
    // with its negation `⋁¬atom`.
    let mut acc: Dnf = vec![Vec::new()];
    for cube in dnf {
        let mut next: Dnf = Vec::new();
        for a in cube {
            let na = neg_atom(a);
            for c in &acc {
                take(budget)?;
                let mut c2 = c.clone();
                c2.push(na.clone());
                next.push(c2);
                if next.len() > 4000 {
                    return None;
                }
            }
        }
        acc = simplify(next);
        if acc.is_empty() {
            return Some(Vec::new()); // ¬(true) contribution
        }
    }
    Some(acc)
}

/// `∀x. dnf` = `¬∃x. ¬dnf`.
pub fn forall(dnf: &Dnf, x: AstId, budget: &mut u64) -> Option<Dnf> {
    let n = negate(dnf, budget)?;
    let e = exists(&n, x, budget)?;
    negate(&e, budget)
}

/// Is a variable-free DNF satisfiable? (Every remaining atom must be ground.)
pub fn ground_sat(dnf: &Dnf) -> Option<bool> {
    let mut any = false;
    for cube in dnf {
        let mut all = true;
        for a in cube {
            match eval_ground(a) {
                Some(true) => {}
                Some(false) => {
                    all = false;
                    break;
                }
                None => return None, // not ground — caller error
            }
        }
        if all {
            any = true;
        }
    }
    Some(any)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::AstId;

    fn c(n: i64) -> LinExpr {
        LinExpr::constant(Rational::from_integer(int(n)))
    }
    // e = coeff·x + k
    fn lin(coeff: i64, x: AstId, k: i64) -> LinExpr {
        LinExpr::var(x)
            .scale(&Rational::from_integer(int(coeff)))
            .add(&c(k))
    }

    // ∀x ∃y. y > x  ⇒  sat
    #[test]
    fn forall_exists_gt() {
        let (x, y) = (AstId(1000), AstId(1001));
        // y > x ⇔ x − y < 0
        let phi: Dnf = vec![vec![Atom::Lt(lin(1, x, 0).sub(&LinExpr::var(y)))]];
        let mut b = 1_000_000u64;
        let ey = exists(&phi, y, &mut b).unwrap();
        let all = forall(&ey, x, &mut b).unwrap();
        assert_eq!(ground_sat(&all), Some(true));
    }

    // ∀x ∃y. y > x ∧ y < x  ⇒  unsat
    #[test]
    fn forall_exists_empty() {
        let (x, y) = (AstId(1000), AstId(1001));
        let phi: Dnf = vec![vec![
            Atom::Lt(lin(1, x, 0).sub(&LinExpr::var(y))), // x − y < 0  (y > x)
            Atom::Lt(LinExpr::var(y).sub(&lin(1, x, 0))), // y − x < 0  (y < x)
        ]];
        let mut b = 1_000_000u64;
        let ey = exists(&phi, y, &mut b).unwrap();
        let all = forall(&ey, x, &mut b).unwrap();
        assert_eq!(ground_sat(&all), Some(false));
    }

    // ∀x ∃y. 2y = x  ⇒  unsat (x must be even, but ∀x)
    #[test]
    fn forall_exists_even() {
        let (x, y) = (AstId(1000), AstId(1001));
        // 2y − x = 0
        let e = LinExpr::var(y)
            .scale(&Rational::from_integer(int(2)))
            .sub(&LinExpr::var(x));
        let phi: Dnf = vec![vec![Atom::Eq(e)]];
        let mut b = 1_000_000u64;
        let ey = exists(&phi, y, &mut b).unwrap();
        let all = forall(&ey, x, &mut b).unwrap();
        assert_eq!(ground_sat(&all), Some(false));
    }

    // `∃x` of random boxed cubes against brute force over the box, for each
    // value of the free `y` (disequalities included: they need a boundary).
    #[test]
    fn exists_matches_brute_force() {
        let (x, y) = (AstId(1000), AstId(1001));
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rnd = |n: i64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            ((seed >> 33) % n as u64) as i64
        };
        let eval = |cube: &[Atom], xv: i64, yv: i64| {
            cube.iter().all(|a| {
                let g = subst(&subst(a, x, &c(xv)), y, &c(yv));
                eval_ground(&g) == Some(true)
            })
        };
        for _ in 0..400 {
            let mut cube = vec![Atom::Le(lin(-1, x, -20)), Atom::Le(lin(1, x, -20))];
            for _ in 0..1 + rnd(3) {
                let cx = [-3, -2, -1, 1, 2, 3][rnd(6) as usize];
                let e = lin(cx, x, rnd(11) - 5)
                    .add(&LinExpr::var(y).scale(&Rational::from_integer(int(rnd(5) - 2))));
                cube.push(match rnd(6) {
                    0 => Atom::Lt(e),
                    1 => Atom::Le(e),
                    2 => Atom::Eq(e),
                    3 => Atom::Ne(e),
                    4 => Atom::Div(int(2 + rnd(2)), e),
                    _ => Atom::Ndiv(int(2 + rnd(2)), e),
                });
            }
            let mut b = 1_000_000u64;
            let ex = exists(&vec![cube.clone()], x, &mut b).unwrap();
            for yv in -8..=8 {
                let want = (-20..=20).any(|xv| eval(&cube, xv, yv));
                let got = ex.iter().any(|cb| {
                    cb.iter()
                        .all(|a| eval_ground(&subst(a, y, &c(yv))) == Some(true))
                });
                assert_eq!(got, want, "y = {yv}");
            }
        }
    }

    // `∀x` of random two-cube DNFs (x boxed by `x < −20 ∨ x > 20 ∨ φ`) against
    // brute force; exercises `negate` and the cube simplifier.
    #[test]
    fn forall_matches_brute_force() {
        let (x, y) = (AstId(1000), AstId(1001));
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut rnd = |n: i64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            ((seed >> 33) % n as u64) as i64
        };
        let holds = |a: &Atom, xv: i64, yv: i64| {
            eval_ground(&subst(&subst(a, x, &c(xv)), y, &c(yv))) == Some(true)
        };
        for _ in 0..300 {
            let mut dnf: Dnf = vec![
                vec![Atom::Lt(lin(1, x, 20))],
                vec![Atom::Lt(lin(-1, x, 20))],
            ];
            for _ in 0..2 {
                let mut cube = Vec::new();
                for _ in 0..1 + rnd(2) {
                    let cx = [-3, -2, -1, 1, 2, 3][rnd(6) as usize];
                    let e = lin(cx, x, rnd(11) - 5)
                        .add(&LinExpr::var(y).scale(&Rational::from_integer(int(rnd(5) - 2))));
                    cube.push(match rnd(6) {
                        0 => Atom::Lt(e),
                        1 => Atom::Le(e),
                        2 => Atom::Eq(e),
                        3 => Atom::Ne(e),
                        4 => Atom::Div(int(2 + rnd(2)), e),
                        _ => Atom::Ndiv(int(2 + rnd(2)), e),
                    });
                }
                dnf.push(cube);
            }
            let mut b = 1_000_000u64;
            let Some(fx) = forall(&dnf, x, &mut b) else {
                continue;
            };
            for yv in -8..=8 {
                let want =
                    (-25..=25).all(|xv| dnf.iter().any(|cb| cb.iter().all(|a| holds(a, xv, yv))));
                let got = fx.iter().any(|cb| {
                    cb.iter()
                        .all(|a| eval_ground(&subst(a, y, &c(yv))) == Some(true))
                });
                assert_eq!(got, want, "y = {yv}");
            }
        }
    }

    // ∀x ∃y. 2y = 2x  ⇒  sat (y = x)
    #[test]
    fn forall_exists_double() {
        let (x, y) = (AstId(1000), AstId(1001));
        // 2y − 2x = 0
        let e = LinExpr::var(y)
            .scale(&Rational::from_integer(int(2)))
            .sub(&LinExpr::var(x).scale(&Rational::from_integer(int(2))));
        let phi: Dnf = vec![vec![Atom::Eq(e)]];
        let mut b = 1_000_000u64;
        let ey = exists(&phi, y, &mut b).unwrap();
        let all = forall(&ey, x, &mut b).unwrap();
        assert_eq!(ground_sat(&all), Some(true));
    }
}
