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
