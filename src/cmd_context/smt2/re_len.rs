//! Regular membership and length constraints on independent string
//! variables, decided exactly (the regex/length part of z3's sequence
//! solver: `seq_regex` derivatives with the length abstraction).
//!
//! When every assertion is a conjunction of atoms that each concern one
//! string variable — membership in a constant regex or its negation, a
//! comparison of its length with a numeral, an equality or disequality with a
//! literal — the variables are independent, and each is decided on the
//! derivative automaton of the intersection of its regexes: the sets of
//! automaton states reached by the words of each length form an eventually
//! periodic sequence, so exploring lengths until that sequence repeats (past
//! the largest length bound) either finds a word whose length satisfies the
//! length constraints or proves there is none.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use puremp::Rational;

use super::{Context, Model, Regex, SmtResult};
use crate::ast::AstId;
use crate::ast::arith::ArithOp;

/// The derivative states one exploration may create.
const STATE_BUDGET: usize = 4000;
/// The longest word explored.
const MAX_LEN: usize = 2000;

/// The constraints on one variable.
#[derive(Default)]
struct VarCons {
    /// Regexes the value must belong to.
    regexes: Vec<Regex>,
    /// Allowed lengths: `lo <= len <= hi` and none of `holes`.
    lo: i64,
    hi: Option<i64>,
    holes: BTreeSet<i64>,
}

impl VarCons {
    fn allows(&self, n: i64) -> bool {
        n >= self.lo && self.hi.is_none_or(|h| n <= h) && !self.holes.contains(&n)
    }
}

impl Context {
    /// Decide the assertions when they are regex/length/literal constraints
    /// on independent string variables. `None` outside that fragment or when
    /// a budget is exceeded.
    pub(super) fn check_sat_regex_vars(&mut self) -> Option<(SmtResult, Option<Model>)> {
        if !self.universals.is_empty() || self.assertions.is_empty() {
            return None;
        }
        let string_sort = self.string_sort?;
        let mut atoms: Vec<(AstId, bool)> = Vec::new();
        let mut stack: Vec<(AstId, bool)> = self.assertions.iter().map(|&a| (a, true)).collect();
        while let Some((t, pol)) = stack.pop() {
            if let Some(a) = self.m.app(t)
                && self.m.is_not(t)
            {
                stack.push((a.args[0], !pol));
            } else if pol && self.m.is_and(t) {
                stack.extend(self.m.app_args(t).iter().map(|&a| (a, true)));
            } else if (pol && self.m.is_true(t)) || (!pol && self.m.is_false(t)) {
            } else {
                atoms.push((t, pol));
            }
        }
        let mut vars: BTreeMap<AstId, VarCons> = BTreeMap::new();
        let mut any_regex = false;
        for (t, pol) in atoms {
            let (x, cs) = self.re_len_atom(t, pol, string_sort)?;
            let vc = vars.entry(x).or_default();
            for c in cs {
                match c {
                    Atom::Re(r) => {
                        any_regex = true;
                        vc.regexes.push(r);
                    }
                    Atom::Len(op, k) => match op {
                        LenOp::Ge => vc.lo = vc.lo.max(k),
                        LenOp::Le => vc.hi = Some(vc.hi.map_or(k, |h| h.min(k))),
                        LenOp::Ne => {
                            vc.holes.insert(k);
                        }
                    },
                }
            }
        }
        if !any_regex {
            return None;
        }
        let mut pins: Vec<(AstId, Vec<u32>)> = Vec::new();
        for (&x, vc) in &vars {
            match decide_var(vc)? {
                Some(w) => pins.push((x, w)),
                None => return Some((SmtResult::Unsat, None)),
            }
        }
        // A model with every variable pinned to its witness.
        let mut eqs = Vec::new();
        let mut witness = Vec::new();
        for (x, w) in &pins {
            let text: alloc::string::String = w.iter().filter_map(|&c| char::from_u32(c)).collect();
            if text.chars().count() != w.len() {
                return None;
            }
            let lit = self.mk_str_lit(&text);
            eqs.push(self.m.mk_eq(*x, lit));
            witness.push((*x, lit));
        }
        let saved = core::mem::replace(&mut self.assertions, eqs);
        let (r, model) = self.check_sat_split();
        self.assertions = saved;
        match (r, model) {
            (SmtResult::Sat, Some(md)) => {
                self.str_witness = witness;
                Some((SmtResult::Sat, Some(md)))
            }
            _ => None,
        }
    }

    /// One atom (with its polarity) as a constraint on a string variable.
    fn re_len_atom(&self, t: AstId, pol: bool, string_sort: AstId) -> Option<(AstId, Vec<Atom>)> {
        let is_var = |x: AstId| {
            self.m.is_uninterp_const(x)
                && self.m.get_sort(x) == string_sort
                && self.str_value(x).is_none()
                && !self.str_symbolic.contains(&x)
        };
        let app = self.m.app(t)?;
        if let Some(op) = self.str_op_decls.get(&app.decl)
            && (op == "str.in_re" || op == "str.in.re")
            && app.args.len() == 2
            && is_var(app.args[0])
        {
            let r = self.regex_of.get(&app.args[1])?.clone();
            let r = if pol { r } else { Regex::Comp(Box::new(r)) };
            return Some((app.args[0], alloc::vec![Atom::Re(r)]));
        }
        if self.m.is_eq(t) && app.args.len() == 2 {
            let (a, b) = (app.args[0], app.args[1]);
            for (x, l) in [(a, b), (b, a)] {
                if is_var(x)
                    && let Some(cps) = self.str_value(l)
                {
                    let r = Regex::Lit(cps);
                    let r = if pol { r } else { Regex::Comp(Box::new(r)) };
                    return Some((x, alloc::vec![Atom::Re(r)]));
                }
            }
            // len x = k
            if let Some((x, k)) = self.len_vs_num(a, b).or_else(|| self.len_vs_num(b, a)) {
                let cs = if pol {
                    alloc::vec![Atom::Len(LenOp::Ge, k), Atom::Len(LenOp::Le, k)]
                } else {
                    alloc::vec![Atom::Len(LenOp::Ne, k)]
                };
                return Some((x, cs));
            }
            return None;
        }
        let op = self.m.arith_op(t)?;
        if app.args.len() != 2 {
            return None;
        }
        let (a, b) = (app.args[0], app.args[1]);
        // Normalize to `len x OP k` with OP ∈ {<=, <, >=, >}.
        let (x, k, op) = if let Some((x, k)) = self.len_vs_num(a, b) {
            (x, k, op)
        } else if let Some((x, k)) = self.len_vs_num(b, a) {
            let flipped = match op {
                ArithOp::Le => ArithOp::Ge,
                ArithOp::Lt => ArithOp::Gt,
                ArithOp::Ge => ArithOp::Le,
                ArithOp::Gt => ArithOp::Lt,
                _ => return None,
            };
            (x, k, flipped)
        } else {
            return None;
        };
        // Apply the polarity: ¬(len ≤ k) is len ≥ k+1, …
        let c = match (op, pol) {
            (ArithOp::Le, true) | (ArithOp::Gt, false) => Atom::Len(LenOp::Le, k),
            (ArithOp::Lt, true) | (ArithOp::Ge, false) => Atom::Len(LenOp::Le, k - 1),
            (ArithOp::Ge, true) | (ArithOp::Lt, false) => Atom::Len(LenOp::Ge, k),
            (ArithOp::Gt, true) | (ArithOp::Le, false) => Atom::Len(LenOp::Ge, k + 1),
            _ => return None,
        };
        Some((x, alloc::vec![c]))
    }

    /// `(str.len x)` against an integer numeral: `(x, k)`.
    fn len_vs_num(&self, l: AstId, n: AstId) -> Option<(AstId, i64)> {
        let app = self.m.app(l)?;
        if Some(app.decl) != self.str_len_decl || app.args.len() != 1 {
            return None;
        }
        let x = app.args[0];
        if !self.m.is_uninterp_const(x) || self.str_value(x).is_some() {
            return None;
        }
        let k: Rational = self.m.as_numeral(n)?;
        Some((x, k.to_i64()?))
    }
}

/// A constraint on one variable.
enum Atom {
    Re(Regex),
    Len(LenOp, i64),
}

#[derive(Clone, Copy)]
enum LenOp {
    Ge,
    Le,
    Ne,
}

/// Decide one variable: `Some(Some(word))` (a witness), `Some(None)` (no
/// value), `None` (budget exceeded).
fn decide_var(vc: &VarCons) -> Option<Option<Vec<u32>>> {
    let mut r = vc
        .regexes
        .iter()
        .cloned()
        .reduce(|a, b| Regex::Inter(Box::new(a), Box::new(b)))
        .unwrap_or(Regex::All);
    if vc.hi.is_some_and(|h| h < vc.lo.max(0)) {
        return Some(None);
    }
    r = r.normalize();
    let mut cuts: BTreeSet<u32> = BTreeSet::new();
    cuts.insert(0);
    r.collect_cuts(&mut cuts);
    // One representative code point per class of the cuts, a printable one
    // when the class has one.
    let cuts: Vec<u32> = cuts.into_iter().collect();
    let reps: Vec<u32> = cuts
        .iter()
        .enumerate()
        .map(|(i, &lo)| {
            let hi = cuts.get(i + 1).copied().unwrap_or(u32::MAX);
            ['a' as u32, 'A' as u32, '0' as u32]
                .into_iter()
                .find(|&c| lo <= c && c < hi)
                .unwrap_or(lo)
        })
        .collect();
    // The largest length any constraint mentions: past it, the constraints
    // allow every length or none.
    let bound = vc
        .hi
        .unwrap_or(0)
        .max(vc.lo)
        .max(vc.holes.iter().copied().max().unwrap_or(0))
        .max(0) as usize;
    // Layered exploration: the states reached by the words of length n, each
    // with one such word.
    let mut layer: BTreeMap<Regex, Vec<u32>> = BTreeMap::new();
    layer.insert(r, Vec::new());
    let mut seen_layers: BTreeSet<Vec<Regex>> = BTreeSet::new();
    let mut states: BTreeSet<Regex> = BTreeSet::new();
    for n in 0..=MAX_LEN {
        if layer.is_empty() {
            return Some(None);
        }
        if vc.allows(n as i64) {
            for (st, w) in &layer {
                if st.nullable() {
                    return Some(Some(w.clone()));
                }
            }
        }
        if vc.hi.is_some_and(|h| n as i64 >= h) {
            return Some(None);
        }
        // A repeated layer past every length bound: the lengths ahead bring
        // no state set not already explored with the same verdict.
        let key: Vec<Regex> = layer.keys().cloned().collect();
        if n > bound && !seen_layers.insert(key) {
            return Some(None);
        }
        let mut next: BTreeMap<Regex, Vec<u32>> = BTreeMap::new();
        for (st, w) in &layer {
            for &c in &reps {
                let d = st.derivative(c).normalize();
                if d == Regex::None {
                    continue;
                }
                if let alloc::collections::btree_map::Entry::Vacant(slot) = next.entry(d) {
                    states.insert(slot.key().clone());
                    if states.len() > STATE_BUDGET {
                        return None;
                    }
                    let mut w2 = w.clone();
                    w2.push(c);
                    slot.insert(w2);
                }
            }
        }
        layer = next;
    }
    None
}
