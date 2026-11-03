//! `seq.nth` of a concrete sequence at a symbolic index, as z3's sequence
//! rewriter and solver read it: the element at each in-range position, and
//! out of range the uninterpreted `seq.nth_u` — a function of the sequence's
//! value and the index, so two reads of equal sequences at equal indices
//! agree (the congruence axioms below; the sequences are constants with
//! known contents here, compared by content).

use alloc::vec::Vec;

use super::Context;
use crate::ast::AstId;
use crate::util::symbol::Symbol;

/// The longest concrete sequence whose reads are expanded by cases.
const MAX_LEN: usize = 16;

/// The name of the out-of-range read function.
const NTH_U: &str = "seq.nth_u";

impl Context {
    /// `seq.nth s i` for the concrete sequence `s` (elements `elems`) and a
    /// symbolic index `i`: `ite(i = 0, s₀, ite(i = 1, s₁, … nth_u(s, i)))`.
    /// `None` for a sequence too long to expand.
    pub(super) fn seq_nth_cases(&mut self, s: AstId, elems: &[AstId], i: AstId) -> Option<AstId> {
        if elems.len() > MAX_LEN {
            return None;
        }
        let seq_sort = self.m.get_sort(s);
        let elem = self.seq_elem_sort(seq_sort)?;
        let int = self.m.mk_int_sort();
        let d = self
            .m
            .mk_func_decl(Symbol::new(NTH_U), &[seq_sort, int], elem);
        let mut r = self.m.mk_app(d, &[s, i]);
        for (k, &e) in elems.iter().enumerate().rev() {
            let kv = self.m.mk_int(k as i64);
            let at_k = self.m.mk_eq(i, kv);
            r = self.m.mk_ite(at_k, e, r);
        }
        Some(r)
    }

    /// `seq.at s i` for the concrete sequence `s` (elements `elems`) and a
    /// symbolic index `i`: the unit of the element at `i` in range, else the
    /// empty sequence.
    pub(super) fn seq_at_cases(&mut self, s: AstId, elems: &[AstId], i: AstId) -> Option<AstId> {
        if elems.len() > MAX_LEN || self.int_arg(i).is_some() {
            return None;
        }
        let sort = self.m.get_sort(s);
        let mut r = self.seq_empty_of(sort);
        for (k, &e) in elems.iter().enumerate().rev() {
            let kv = self.m.mk_int(k as i64);
            let at_k = self.m.mk_eq(i, kv);
            let u = self.seq_op("seq.unit", &[e]).ok()?;
            r = self.m.mk_ite(at_k, u, r);
        }
        Some(r)
    }

    /// `seq.extract s i n` for the concrete sequence `s` (elements `elems`)
    /// with a symbolic offset or length: the slice from `i` of length
    /// `min(n, |s| − i)` for each offset in range and each positive length,
    /// else the empty sequence.
    pub(super) fn seq_extract_cases(
        &mut self,
        s: AstId,
        elems: &[AstId],
        i: AstId,
        n: AstId,
    ) -> Option<AstId> {
        const MAX_EXTRACT: usize = 8;
        let len = elems.len();
        if len > MAX_EXTRACT || (self.int_arg(i).is_some() && self.int_arg(n).is_some()) {
            return None;
        }
        let sort = self.m.get_sort(s);
        let mut r = self.seq_empty_of(sort);
        for k in (0..len).rev() {
            let kv = self.m.mk_int(k as i64);
            let at_k = self.m.mk_eq(i, kv);
            // Lengths 1 … len − k: exactly m below the rest, at least it at the rest.
            let rest = len - k;
            let mut by_len = self.seq_empty_of(sort);
            for m in (1..=rest).rev() {
                let mv = self.m.mk_int(m as i64);
                let cond = if m == rest {
                    self.m.mk_ge(n, mv)
                } else {
                    self.m.mk_eq(n, mv)
                };
                let slice = self.mk_seq(elems[k..k + m].to_vec());
                by_len = self.m.mk_ite(cond, slice, by_len);
            }
            r = self.m.mk_ite(at_k, by_len, r);
        }
        Some(r)
    }

    /// Congruence of the out-of-range reads in `goal` by content: equal
    /// sequence values and indices give equal `nth_u` values, also against
    /// the out-of-range reads at constant indices (`seq_nth_oob`).
    pub(super) fn seq_nth_u_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        let mut reads: Vec<(AstId, AstId, AstId)> = Vec::new(); // (seq, index, value)
        for t in self.m.postorder(goal) {
            if let Some(a) = self.m.app(t)
                && a.args.len() == 2
                && self.seq_of.contains_key(&a.args[0])
                && self
                    .m
                    .func_decl(a.decl)
                    .and_then(|d| d.name.as_str())
                    .is_some_and(|n| n == NTH_U)
            {
                reads.push((a.args[0], a.args[1], t));
            }
        }
        if reads.is_empty() {
            return Vec::new();
        }
        let consts: alloc::collections::BTreeSet<AstId> =
            self.m.postorder(goal).into_iter().collect();
        let oob: Vec<((AstId, i64), AstId)> = self
            .seq_nth_oob
            .iter()
            .filter(|(_, c)| consts.contains(c))
            .map(|(&k, &c)| (k, c))
            .collect();
        for ((s, k), c) in oob {
            let kv = self.m.mk_int(k);
            reads.push((s, kv, c));
        }
        let mut ax = Vec::new();
        for x in 0..reads.len() {
            for y in x + 1..reads.len() {
                let (s1, i1, v1) = reads[x];
                let (s2, i2, v2) = reads[y];
                if self.m.get_sort(s1) != self.m.get_sort(s2) {
                    continue;
                }
                let (Some(c1), Some(c2)) =
                    (self.seq_of.get(&s1).cloned(), self.seq_of.get(&s2).cloned())
                else {
                    continue;
                };
                let same_seq = self.seq_content_eq(&c1, &c2);
                if self.m.is_false(same_seq) {
                    continue;
                }
                let same_idx = self.m.mk_eq(i1, i2);
                let hyp = self.m.mk_and(&[same_seq, same_idx]);
                let concl = self.m.mk_eq(v1, v2);
                ax.push(self.m.mk_implies(hyp, concl));
            }
        }
        ax
    }
}
