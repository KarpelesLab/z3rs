//! The `seq.nth_u` interpretation z3 prints in a model.
//!
//! z3's sequence rewriter reads `seq.nth s i` as `ite(0 <= i < |s|,
//! seq.nth_i s i, seq.nth_u s i)` (unless `s` is a unit read at 0, or its
//! length is known and `i` a numeral, see `seq_rewriter::mk_seq_nth`). The
//! `seq.nth_u` application is internalized whatever the guard, so the model
//! generator gives the function an entry for it at its arguments' values:
//!
//! - out of range, the read's value (what the read was constrained to);
//! - in range, the term is in a class of its own without an arithmetic
//!   variable, so `model_generator::mk_value_procs` gives it a fresh value:
//!   `simple_factory::get_fresh_value` counts up from 0 past the values the
//!   arithmetic model registered.
//!
//! `proto_model::complete_partial_func` sets the else branch to the most
//! frequent entry value and `func_interp::compress` drops the entries equal to
//! it, so when every entry has the same value the function prints as that
//! value alone: the only case listed here.

use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use super::{Context, Model, SExpr, Value, sexpr_any};
use crate::ast::AstId;
use crate::util::symbol::Symbol;

/// The name of the out-of-range read function.
pub(super) const NTH_U: &str = "seq.nth_u";

impl Context {
    /// The elements of the sequence `s` under `model`: a concrete sequence,
    /// or a constant the witness search assigned one.
    fn seq_nth_model_elems(&self, s: AstId) -> Option<(AstId, usize)> {
        if let Some(es) = self.seq_of.get(&s) {
            return Some((s, es.len()));
        }
        if !self.m.is_uninterp_const(s) {
            return None;
        }
        let &(_, w) = self.str_witness.iter().find(|(c, _)| *c == s)?;
        Some((w, self.seq_of.get(&w)?.len()))
    }

    /// The `seq.nth_u` declaration and the body z3 prints for it in the last
    /// model, when the reads of the assertions give it a single value.
    pub(super) fn seq_nth_u_listing(&mut self, model: &mut Model) -> Option<(AstId, String)> {
        if !self.universals.is_empty() {
            return None;
        }
        let in_assertions: BTreeSet<AstId> = self
            .m
            .postorder_many(&self.assertions)
            .into_iter()
            .collect();
        // Every read: (sequence, index, read term).
        let mut reads: Vec<(AstId, AstId, AstId)> = Vec::new();
        for (&(s, i), &c) in &self.seq_nth_sym {
            reads.push((s, i, c));
        }
        for (&(s, k), &c) in &self.seq_nth_oob.clone() {
            let kv = self.m.mk_int(k);
            reads.push((s, kv, c));
        }
        for &t in &in_assertions {
            if let Some(a) = self.m.app(t)
                && a.args.len() == 2
                && self
                    .m
                    .func_decl(a.decl)
                    .and_then(|d| d.name.as_str())
                    .is_some_and(|n| n == NTH_U)
            {
                reads.push((a.args[0], a.args[1], t));
            }
        }
        let mut seq_sort = None;
        // The value of each out-of-range read, and the in-range reads, of
        // the assertions; the out-of-range values of the solver's own reads.
        let mut forced: Vec<((String, i64), String)> = Vec::new();
        let mut in_range: BTreeSet<(String, i64)> = BTreeSet::new();
        let mut internal: Vec<((String, i64), String, AstId)> = Vec::new();
        let read_terms: BTreeSet<AstId> = reads
            .iter()
            .map(|r| r.2)
            .filter(|c| in_assertions.contains(c))
            .collect();
        for (s, i, c) in reads {
            let asserted = in_assertions.contains(&c);
            let elems = self.seq_nth_model_elems(s);
            let index = match model.eval_value(&self.m, i) {
                Value::Num(r, true) => r.to_integer().and_then(|v| v.to_i64()),
                _ => None,
            };
            let (Some((w, len)), Some(index)) = (elems, index) else {
                if asserted {
                    return None;
                }
                continue;
            };
            if asserted {
                let sort = self.m.get_sort(s);
                if seq_sort.is_some_and(|t| t != sort) {
                    return None;
                }
                seq_sort = Some(sort);
            }
            if index >= 0 && (index as usize) < len {
                if asserted && !self.seq_nth_guard_known(s, i, index) {
                    let key = self.model_term_render(model, w);
                    in_range.insert((key, index));
                }
                continue;
            }
            let key = (self.model_term_render(model, w), index);
            let v = self.model_term_render(model, c);
            if asserted {
                forced.push((key, v));
            } else {
                internal.push((key, v, c));
            }
        }
        let seq_sort = seq_sort?;
        // A read only a definition `x = t` that `solve-eqs` eliminates
        // mentions is never internalized: the model converter evaluates it
        // under the completed model instead.
        if !self.inc_mode && self.only_in_eliminated_definition(&read_terms) {
            return None;
        }
        let elem = self.seq_elem_sort(seq_sort)?;
        // Of the solver's reads of a sequence value at an index, the oldest
        // is the one it constrained (the others are re-targeted to it, see
        // `unify_nth_oob`), and the read of the assertions' term takes its
        // value: once a constant is given its witness sequence, its reads are
        // those of the witness.
        internal.sort_by_key(|r| r.2);
        let mut oldest: Vec<((String, i64), String)> = Vec::new();
        for (k, v, _) in internal {
            if !oldest.iter().any(|o| o.0 == k) {
                oldest.push((k, v));
            }
        }
        let internal = oldest;
        for (k, v) in &internal {
            for f in forced.iter_mut().filter(|f| f.0 == *k) {
                f.1 = v.clone();
            }
        }
        let value = match (forced.first(), in_range.len()) {
            (Some((_, v)), 0) if forced.iter().all(|f| f.1 == *v) => v.clone(),
            (None, 1) if self.m.is_int_sort(elem) => self.seq_nth_u_fresh_int(model).to_string(),
            _ => return None,
        };
        // When a macro the assertions use reads sequences (inside a fold or
        // map, the solver's own reads), its out-of-range reads must agree
        // with it too: the assertions are evaluated with this interpretation.
        let used = self.asserted_names();
        let macro_reads = self.macros.iter().any(|(n, (_, body))| {
            used.contains(n.as_str())
                && sexpr_any(body, |e| matches!(e, SExpr::Atom(a) if a == "seq.nth"))
        });
        if macro_reads
            && internal
                .iter()
                .any(|(k, v)| *v != value && !forced.iter().any(|f| f.0 == *k))
        {
            return None;
        }
        let int = self.m.mk_int_sort();
        let d = self
            .m
            .mk_func_decl(Symbol::new(NTH_U), &[seq_sort, int], elem);
        let text = alloc::format!(
            "  (define-fun {NTH_U} ((x!0 {}) (x!1 Int)) {}\n    {value})",
            self.sort_display(seq_sort),
            self.sort_display(elem)
        );
        Some((d, text))
    }

    /// Is the range guard `0 <= i < |s|` of the read `seq.nth s i` (`i` the
    /// numeral `index`) decided by z3's `propagate_values` before the search?
    /// It is when an asserted literal is the guard's atom `|x| <= index` (or
    /// its negation, as `|x| > index` or `|x| >= index + 1` normalize) or
    /// fixes `|x|`, where `x` is `s` itself or, `s` being eliminated by
    /// `solve-eqs`, the sequence its definition maps (`|map f x| = |x|`).
    fn seq_nth_guard_known(&self, s: AstId, i: AstId, index: i64) -> bool {
        if self.int_arg(i).is_none() {
            return false;
        }
        let name_of = |t: AstId| -> Option<String> {
            self.m
                .func_decl(self.m.app_decl(t))
                .and_then(|d| d.name.as_str().map(String::from))
        };
        let mut bases = alloc::vec![s];
        if !self.inc_mode
            && self.m.is_uninterp_const(s)
            && self
                .decl_name(self.m.app_decl(s))
                .is_some_and(|n| self.solved_vars.contains(&n))
        {
            for &a in &self.assertions {
                if !self.m.is_eq(a) {
                    continue;
                }
                let args = self.m.app_args(a);
                for j in 0..2 {
                    let (x, t) = (args[j], args[1 - j]);
                    if x == s
                        && self.m.is_app(t)
                        && name_of(t).is_some_and(|n| {
                            n.starts_with("!seqop!seq.map!") || n.starts_with("!seqop!seq.mapi!")
                        })
                        && let Some(&last) = self.m.app_args(t).last()
                    {
                        bases.push(last);
                    }
                }
            }
        }
        let is_len_of_base = |t: AstId| {
            self.m.is_app(t)
                && self.m.app_args(t).len() == 1
                && bases.contains(&self.m.app_args(t)[0])
                && name_of(t).is_some_and(|n| n == "seq.len" || n.starts_with("!seqop!seq.len"))
        };
        let mut todo = self.assertions.clone();
        while let Some(a) = todo.pop() {
            if self.m.is_and(a) {
                todo.extend(self.m.app_args(a).iter().copied());
                continue;
            }
            let lit = if self.m.is_not(a) {
                self.m.app_args(a)[0]
            } else {
                a
            };
            let Some(app) = self.m.app(lit) else {
                continue;
            };
            if app.args.len() != 2 {
                continue;
            }
            let (l, r) = (app.args[0], app.args[1]);
            // `len op k`, flipped to have the length on the left.
            let (op, k) = match (is_len_of_base(l), is_len_of_base(r)) {
                (true, false) => match self.int_arg(r) {
                    Some(k) => (name_of(lit), k),
                    None => continue,
                },
                (false, true) => match self.int_arg(l) {
                    Some(k) => (
                        name_of(lit).map(|n| {
                            match n.as_str() {
                                "<" => ">",
                                ">" => "<",
                                "<=" => ">=",
                                ">=" => "<=",
                                o => o,
                            }
                            .to_string()
                        }),
                        k,
                    ),
                    None => continue,
                },
                _ => continue,
            };
            let decided = match op.as_deref() {
                Some("=") => !self.m.is_not(a),
                Some("<=") | Some(">") => k == index,
                Some("<") | Some(">=") => k == index + 1,
                _ => false,
            };
            if decided {
                return true;
            }
        }
        false
    }

    /// Does one of `terms` occur in an asserted definition `x = t` of a
    /// constant `solve-eqs` eliminates (`t` not mentioning `x`) that no other
    /// assertion mentions?
    fn only_in_eliminated_definition(&self, terms: &BTreeSet<AstId>) -> bool {
        let subterms: Vec<BTreeSet<AstId>> = self
            .assertions
            .iter()
            .map(|&a| self.m.postorder(a).into_iter().collect())
            .collect();
        self.assertions.iter().enumerate().any(|(k, &a)| {
            if !self.m.is_eq(a) {
                return false;
            }
            let args = self.m.app_args(a);
            args.iter().enumerate().any(|(j, &x)| {
                let t = args[1 - j];
                self.m.is_uninterp_const(x)
                    && self
                        .decl_name(self.m.app_decl(x))
                        .is_some_and(|n| self.solved_vars.contains(&n))
                    && !self.m.postorder(t).contains(&x)
                    && subterms
                        .iter()
                        .enumerate()
                        .all(|(o, sub)| o == k || !sub.contains(&x))
                    && self.m.postorder(t).iter().any(|u| terms.contains(u))
            })
        })
    }

    /// The fresh integer z3's arithmetic value factory hands out first: the
    /// least natural number no arithmetic value of the model took. Those are
    /// the numerals of the assertions, the values of the integer and
    /// integer-sequence constants, the numerals 0 and 1 z3's arithmetic solver
    /// always has, and the lengths the sequence solver's unfolding leaves:
    /// a sequence of length `n` is split into units and tails, with
    /// `|tail(s, i)| = n - i - 1` and `1 + |tail(s, i)| = n - i`, so every
    /// length up to `n`. A folded (or mapped) sequence that ends up empty was
    /// first split as non-empty (`tail(s, 0) = ε` is decided false, z3's
    /// default phase), which introduces `tail(s, 1)`: the arithmetic values
    /// `|tail(s, 0)| = 1 + |tail(s, 1)| = 1` and `1 + |tail(s, 0)| = 2` stay.
    fn seq_nth_u_fresh_int(&mut self, model: &mut Model) -> u64 {
        let mut taken: BTreeSet<u64> = [0, 1].into_iter().collect();
        for t in self.m.postorder_many(&self.assertions) {
            if self.m.is_int_sort(self.m.get_sort(t))
                && let Some(v) = self.m.as_numeral(t)
                && let Some(v) = v.to_integer().and_then(|v| v.to_u64())
            {
                taken.insert(v);
            }
            if self.m.is_app(t)
                && matches!(
                    self.seqop_ops.get(&self.m.app_decl(t)).map(String::as_str),
                    Some("seq.map" | "seq.mapi" | "seq.foldl" | "seq.foldli")
                )
                && let Some(&s) = self.m.app_args(t).last()
                && self.seq_nth_model_elems(s).is_some_and(|(_, n)| n == 0)
            {
                taken.extend([1, 2]);
            }
        }
        let decls: Vec<AstId> = self
            .decl_order
            .iter()
            .filter_map(|n| self.funcs.get(n).copied())
            .filter(|&d| self.m.func_decl(d).is_some_and(|f| f.domain.is_empty()))
            .collect();
        let consts: Vec<AstId> = decls.into_iter().map(|d| self.m.mk_const(d)).collect();
        for c in consts {
            let sort = self.m.get_sort(c);
            let int_seq = self
                .seq_elem_sort(sort)
                .is_some_and(|e| self.m.is_int_sort(e));
            if !self.m.is_int_sort(sort) && !int_seq {
                continue;
            }
            let mut shown = c;
            if int_seq && let Some((w, len)) = self.seq_nth_model_elems(c) {
                taken.extend(0..=len as u64);
                shown = w;
            }
            let text = self.model_term_render(model, shown);
            let text = text.replace('(', " ( ").replace(')', " ) ");
            let toks: Vec<&str> = text.split_whitespace().collect();
            for (k, tok) in toks.iter().enumerate() {
                if k > 0 && toks[k - 1] == "-" {
                    continue;
                }
                if let Ok(v) = tok.parse::<u64>() {
                    taken.insert(v);
                }
            }
        }
        let mut n = 0;
        while taken.contains(&n) {
            n += 1;
        }
        n
    }
}
