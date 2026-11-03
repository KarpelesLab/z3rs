//! z3's own model for a conjunction of linear real atoms.
//!
//! The solver decides such a goal soundly but stops at a vertex of its own;
//! z3 prints the vertex its `lar_solver` reaches. For the plain first
//! `check-sat` of a pure linear real conjunction that z3 hands to
//! `theory_lra`, that vertex depends only on the goal as z3's preprocessing
//! leaves it, so it is rebuilt here and replayed through [`Lar`]:
//!
//! * `propagate-values` substitutes each `x = k` into the other atoms;
//! * an atom becomes a bound on a constant (one variable, scaled away) or
//!   on the term `Σ c·x` (variables in z3's expression-id order — their
//!   first occurrence — negated when the leading coefficient is negative,
//!   a strict comparison as the negation of the opposite non-strict one, an
//!   equality as the two non-strict bounds);
//! * `theory_lra` creates the columns `1, 1.0, 0, 0.0`, then internalizes
//!   the atoms in order: a term's variables last-argument first (its
//!   `linearize` work list), then the term column; all bounds are then
//!   asserted and one feasibility search runs.
//!
//! z3 hands a difference-logic goal (only `x ⋈ k` and `x − y ⋈ k`) to
//! another arithmetic solver, so those are left alone, as is everything
//! else outside this fragment. The result is only used after checking that
//! it satisfies every atom.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use puremp::{Int, Rational};

use super::{Context, SExpr, parse_numeral};
use crate::math::lar::{Kind, Lar, umap_order};

/// `Σ c·x + k` over the constants, by index in first-occurrence order.
#[derive(Clone, Debug)]
struct Lin {
    coeffs: BTreeMap<usize, Rational>,
    k: Rational,
}

fn rat(n: i64) -> Rational {
    Rational::from_integer(Int::from(n))
}

impl Lin {
    fn constant(k: Rational) -> Lin {
        Lin {
            coeffs: BTreeMap::new(),
            k,
        }
    }
    fn add_scaled(&mut self, o: &Lin, c: &Rational) {
        for (v, a) in &o.coeffs {
            let e = self.coeffs.entry(*v).or_insert_with(|| rat(0));
            e.addmul(a, c);
        }
        self.coeffs.retain(|_, a| !a.is_zero());
        self.k.addmul(&o.k, c);
    }
    fn eval(&self, vals: &[Rational]) -> Rational {
        let mut s = self.k.clone();
        for (v, a) in &self.coeffs {
            s.addmul(a, &vals[*v]);
        }
        s
    }
}

/// An asserted comparison `form ⋈ 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rel {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

impl Rel {
    fn holds(self, v: &Rational) -> bool {
        match self {
            Rel::Le => !v.is_positive(),
            Rel::Lt => v.is_negative(),
            Rel::Ge => !v.is_negative(),
            Rel::Gt => v.is_positive(),
            Rel::Eq => v.is_zero(),
        }
    }
    /// The relation after multiplying both sides by a negative number.
    fn flip(self) -> Rel {
        match self {
            Rel::Le => Rel::Ge,
            Rel::Lt => Rel::Gt,
            Rel::Ge => Rel::Le,
            Rel::Gt => Rel::Lt,
            Rel::Eq => Rel::Eq,
        }
    }
}

/// A bound z3 asserts: on a constant's column or on a term's.
enum Target {
    Var(usize),
    Term(Vec<(usize, Rational)>),
}

impl Context {
    /// z3's values of the real constants for the current assertions, when
    /// they form a linear real conjunction z3 decides with `theory_lra` on a
    /// plain first `check-sat` (see the module documentation), as `(name,
    /// value)` pairs. `None` outside that fragment or when the replay does
    /// not end feasible.
    pub(super) fn z3_lra_conj_model(&mut self) -> Option<Vec<(String, Rational)>> {
        if !matches!(self.logic.as_deref(), None | Some("QF_LRA")) {
            return None;
        }
        // Options that steer z3's search or its arithmetic solver change the
        // vertex; only output options are allowed.
        for k in self.params.keys() {
            let k = k.trim_start_matches(':').replace('-', "_");
            if !(matches!(k.as_str(), "produce_models" | "model" | "print_success")
                || k.starts_with("pp."))
            {
                return None;
            }
        }
        let real = self.m.mk_real_sort();
        let mut forms: Vec<SExpr> = Vec::new();
        for (_, e) in &self.raw_asserts {
            let mut todo = alloc::vec![e.clone()];
            while let Some(f) = todo.pop() {
                match &f {
                    SExpr::List(l) if matches!(l.first(), Some(SExpr::Atom(a)) if a == "and") => {
                        todo.extend(l[1..].iter().rev().cloned());
                    }
                    _ => forms.push(f),
                }
            }
        }
        let mut names: Vec<String> = Vec::new();
        let mut atoms: Vec<(Rel, Lin)> = Vec::new();
        for f in &forms {
            let (neg, f) = match f {
                SExpr::List(l) if l.len() == 2 && matches!(&l[0], SExpr::Atom(a) if a == "not") => {
                    (true, &l[1])
                }
                _ => (false, f),
            };
            let SExpr::List(l) = f else {
                return None;
            };
            let [SExpr::Atom(op), lhs, rhs] = l.as_slice() else {
                return None;
            };
            let rel = match op.as_str() {
                "<=" => Rel::Le,
                "<" => Rel::Lt,
                ">=" => Rel::Ge,
                ">" => Rel::Gt,
                "=" => Rel::Eq,
                _ => return None,
            };
            let mut form = self.lra_conj_lin(lhs, real, &mut names, 0)?;
            let r = self.lra_conj_lin(rhs, real, &mut names, 0)?;
            form.add_scaled(&r, &rat(-1));
            let rel = match (neg, rel) {
                (false, r) => r,
                (true, Rel::Le) => Rel::Gt,
                (true, Rel::Lt) => Rel::Ge,
                (true, Rel::Ge) => Rel::Lt,
                (true, Rel::Gt) => Rel::Le,
                (true, Rel::Eq) => return None,
            };
            atoms.push((rel, form));
        }
        let original = atoms.clone();
        // `propagate-values`: an asserted `x = k` replaces `x` in the others.
        loop {
            let mut vals: BTreeMap<usize, (usize, Rational)> = BTreeMap::new();
            for (i, (rel, f)) in atoms.iter().enumerate() {
                if *rel == Rel::Eq
                    && f.coeffs.len() == 1
                    && let Some((&v, c)) = f.coeffs.iter().next()
                {
                    vals.entry(v).or_insert((i, f.k.neg().div(c)));
                }
            }
            let mut changed = false;
            for (i, (_, f)) in atoms.iter_mut().enumerate() {
                let subst: Vec<(usize, Rational)> = f
                    .coeffs
                    .keys()
                    .filter_map(|v| {
                        vals.get(v)
                            .filter(|(at, _)| *at != i)
                            .map(|(_, k)| (*v, k.clone()))
                    })
                    .collect();
                for (v, k) in subst {
                    let c = f.coeffs.remove(&v).unwrap();
                    f.k.addmul(&c, &k);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // z3's normal form, as (target, upper bound?, bound, strict?).
        let mut bounds: Vec<(Target, bool, Rational, bool)> = Vec::new();
        for (rel, f) in &atoms {
            let mut vs: Vec<usize> = f.coeffs.keys().copied().collect();
            vs.sort_unstable();
            let Some(&lead) = vs.first() else {
                if !rel.holds(&f.k) {
                    return None;
                }
                continue;
            };
            let c0 = f.coeffs[&lead].clone();
            if vs.len() == 1 {
                // c·x + k ⋈ 0  ⟹  x ⋈' −k/c.
                let b = f.k.neg().div(&c0);
                let rel = if c0.is_negative() { rel.flip() } else { *rel };
                let t = || Target::Var(lead);
                match rel {
                    Rel::Le => bounds.push((t(), true, b, false)),
                    Rel::Lt => bounds.push((t(), true, b, true)),
                    Rel::Ge => bounds.push((t(), false, b, false)),
                    Rel::Gt => bounds.push((t(), false, b, true)),
                    Rel::Eq => {
                        bounds.push((t(), true, b.clone(), false));
                        bounds.push((t(), false, b, false));
                    }
                }
                continue;
            }
            // Σ c·x ⋈ −k, negated when the leading coefficient is negative.
            let sign = if c0.is_negative() { rat(-1) } else { rat(1) };
            let rel = if c0.is_negative() { rel.flip() } else { *rel };
            let terms: Vec<(usize, Rational)> =
                vs.iter().map(|v| (*v, f.coeffs[v].mul(&sign))).collect();
            let b = f.k.neg().mul(&sign);
            let t = || Target::Term(terms.clone());
            match rel {
                Rel::Le => bounds.push((t(), true, b, false)),
                Rel::Lt => bounds.push((t(), true, b, true)),
                Rel::Ge => bounds.push((t(), false, b, false)),
                Rel::Gt => bounds.push((t(), false, b, true)),
                Rel::Eq => {
                    bounds.push((t(), true, b.clone(), false));
                    bounds.push((t(), false, b, false));
                }
            }
        }
        // Difference logic goes to another solver.
        let diff = bounds.iter().all(|(t, ..)| match t {
            Target::Var(_) => true,
            Target::Term(ts) => {
                ts.len() == 2 && {
                    let mut cs: Vec<&Rational> = ts.iter().map(|(_, c)| c).collect();
                    cs.sort();
                    *cs[0] == rat(-1) && *cs[1] == rat(1)
                }
            }
        });
        if diff {
            return None;
        }
        // Replay `theory_lra`.
        let mut lar = Lar::new(0);
        for (v, _) in [(1, true), (1, false), (0, true), (0, false)] {
            let j = lar.add_var();
            lar.add_bound(j, Kind::Ge, &rat(v));
            lar.add_bound(j, Kind::Le, &rat(v));
        }
        let mut col: BTreeMap<usize, usize> = BTreeMap::new();
        // The constants in internalization order.
        let mut order: Vec<usize> = Vec::new();
        let mut term_col: BTreeMap<Vec<(usize, Rational)>, usize> = BTreeMap::new();
        let mut asserted: Vec<(usize, Kind, Rational)> = Vec::new();
        for (target, upper, b, strict) in bounds {
            let j = match target {
                Target::Var(v) => *col.entry(v).or_insert_with(|| {
                    order.push(v);
                    lar.add_var()
                }),
                Target::Term(ts) => match term_col.get(&ts) {
                    Some(&j) => j,
                    None => {
                        // `linearize` takes the last argument first.
                        let mut lin_order = alloc::vec![ts[ts.len() - 1].clone()];
                        lin_order.extend(ts[..ts.len() - 1].iter().cloned());
                        let mut left: Vec<(usize, Rational)> = Vec::new();
                        for (v, c) in &lin_order {
                            let j = *col.entry(*v).or_insert_with(|| {
                                order.push(*v);
                                lar.add_var()
                            });
                            left.push((j, c.clone()));
                        }
                        let keys: Vec<usize> = left.iter().map(|(j, _)| *j).collect();
                        let coeffs: Vec<(usize, Rational)> = umap_order(&keys)
                            .into_iter()
                            .map(|j| left.iter().find(|(k, _)| *k == j).unwrap().clone())
                            .collect();
                        let j = lar.add_term(&coeffs);
                        term_col.insert(ts, j);
                        j
                    }
                },
            };
            let kind = match (upper, strict) {
                (true, false) => Kind::Le,
                (true, true) => Kind::Lt,
                (false, false) => Kind::Ge,
                (false, true) => Kind::Gt,
            };
            asserted.push((j, kind, b));
        }
        // Every mentioned constant must be internalized (else z3's model
        // would not list it where ours does).
        if order.len() != names.len() {
            return None;
        }
        for (j, kind, b) in &asserted {
            if !lar.add_bound(*j, *kind, b) {
                return None;
            }
        }
        if lar.solve(100_000) != Some(true) {
            return None;
        }
        let values = lar.values();
        let mut vals: Vec<Rational> = alloc::vec![rat(0); names.len()];
        for (v, j) in &col {
            vals[*v] = values[*j].clone();
        }
        if !original.iter().all(|(rel, f)| rel.holds(&f.eval(&vals))) {
            return None;
        }
        Some(names.iter().cloned().zip(vals).collect())
    }

    /// The linear form of `e` over the declared real constants (indexed in
    /// `names` by first occurrence); `None` outside linear real arithmetic.
    fn lra_conj_lin(
        &self,
        e: &SExpr,
        real: crate::ast::AstId,
        names: &mut Vec<String>,
        depth: u32,
    ) -> Option<Lin> {
        if depth > 200 {
            return None;
        }
        match e {
            SExpr::Atom(a) => {
                if let Some((r, _)) = parse_numeral(a) {
                    return Some(Lin::constant(r));
                }
                if self.macros.contains_key(a.as_str()) {
                    return None;
                }
                let d = *self.funcs.get(a.as_str())?;
                let fd = self.m.func_decl(d)?;
                if fd.arity() != 0 || fd.range != real {
                    return None;
                }
                let i = match names.iter().position(|n| n == a) {
                    Some(i) => i,
                    None => {
                        names.push(a.clone());
                        names.len() - 1
                    }
                };
                let mut l = Lin::constant(rat(0));
                l.coeffs.insert(i, rat(1));
                Some(l)
            }
            SExpr::List(l) => {
                let (SExpr::Atom(op), args) = (l.first()?, &l[1..]) else {
                    return None;
                };
                let sub = |x: &SExpr, names: &mut Vec<String>| {
                    self.lra_conj_lin(x, real, names, depth + 1)
                };
                match op.as_str() {
                    "+" if !args.is_empty() => {
                        let mut acc = Lin::constant(rat(0));
                        for x in args {
                            acc.add_scaled(&sub(x, names)?, &rat(1));
                        }
                        Some(acc)
                    }
                    "-" if args.len() == 1 => {
                        let mut acc = Lin::constant(rat(0));
                        acc.add_scaled(&sub(&args[0], names)?, &rat(-1));
                        Some(acc)
                    }
                    "-" if args.len() > 1 => {
                        let mut acc = sub(&args[0], names)?;
                        for x in &args[1..] {
                            acc.add_scaled(&sub(x, names)?, &rat(-1));
                        }
                        Some(acc)
                    }
                    "*" if !args.is_empty() => {
                        let mut acc = Lin::constant(rat(1));
                        for x in args {
                            let f = sub(x, names)?;
                            if f.coeffs.is_empty() {
                                let mut scaled = Lin::constant(rat(0));
                                scaled.add_scaled(&acc, &f.k);
                                acc = scaled;
                            } else if acc.coeffs.is_empty() {
                                let mut scaled = Lin::constant(rat(0));
                                scaled.add_scaled(&f, &acc.k);
                                acc = scaled;
                            } else {
                                return None;
                            }
                        }
                        Some(acc)
                    }
                    "/" if args.len() == 2 => {
                        let num = sub(&args[0], names)?;
                        let den = sub(&args[1], names)?;
                        if !den.coeffs.is_empty() || den.k.is_zero() {
                            return None;
                        }
                        let mut acc = Lin::constant(rat(0));
                        acc.add_scaled(&num, &den.k.recip());
                        Some(acc)
                    }
                    _ => None,
                }
            }
        }
    }

    /// Replace the real constants' values in `model` by z3's (see
    /// [`Context::z3_lra_conj_model`]) when the goal is in that fragment and
    /// every assertion still evaluates to `true`.
    pub(super) fn apply_z3_lra_conj_model(&mut self, model: &mut crate::smt::Model) {
        let Some(vals) = self.z3_lra_conj_model() else {
            return;
        };
        let mut old: Vec<(crate::ast::AstId, Option<Rational>)> = Vec::new();
        for (name, v) in vals {
            let Some(&d) = self.funcs.get(&name) else {
                return;
            };
            let c = self.m.mk_const(d);
            old.push((c, model.assigned_num(c).cloned()));
            model.set_arith(c, v);
        }
        let ok = self
            .assertions
            .iter()
            .all(|&a| matches!(model.eval_value(&self.m, a), crate::smt::Value::Bool(true)));
        if !ok {
            for (c, v) in old {
                match v {
                    Some(v) => model.set_arith(c, v),
                    None => model.unassign(c),
                }
            }
        }
    }
}
