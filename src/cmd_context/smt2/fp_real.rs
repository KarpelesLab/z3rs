//! Floating-point values as reals, read off their bit-vector images, and the
//! rounding of a symbolic real into a float (z3's `fpa2bv_converter::
//! mk_to_fp_real` for a non-numeral argument): the result is fresh bits tied
//! to the real by the rounding relation, stated in terms of the result's
//! real value and the gaps to its neighbouring floats. Linear once the
//! exponent field is split into cases, so the bit-blasting combination
//! (`bv_bool`) decides it with the arithmetic.

use alloc::vec::Vec;

use puremp::{Int, Rational};

use super::{Context, pow2};
use crate::ast::AstId;

/// The widest exponent field enumerated.
pub(super) const MAX_EB: u32 = 8;
/// The widest exponent field of a `to_fp` of a symbolic real encoded by its
/// rounding relation (wider formats keep the folding of pinned reals).
pub(super) const ROUND_MAX_EB: u32 = 5;

/// The fields of a float's bit-vector image and the real-valued pieces of
/// its value.
pub(super) struct FpParts {
    pub exp: AstId,
    pub sig: AstId,
    /// `sign = 1`.
    pub is_neg: AstId,
    /// The exponent field is all ones (an infinity or NaN).
    pub special: AstId,
    /// The significand field is zero.
    pub sig_zero: AstId,
    /// `|value|` of a finite float.
    pub mag: AstId,
    /// The distance to the next float of larger magnitude (one ulp).
    pub gap_up: AstId,
}

/// `2^k` as a rational.
fn pow2r(k: i64) -> Rational {
    let p = Rational::from_integer(pow2(k.unsigned_abs() as u32));
    if k >= 0 {
        p
    } else {
        Rational::from_integer(Int::from(1)) / p
    }
}

impl Context {
    /// The pieces of the float whose bit-vector image is `bv`, of format
    /// `(eb, sb)`. `None` for an exponent wider than [`MAX_EB`].
    pub(super) fn fp_parts(&mut self, bv: AstId, eb: u32, sb: u32) -> Option<FpParts> {
        if !(2..=MAX_EB).contains(&eb) || sb < 2 {
            return None;
        }
        let w = eb + sb;
        let sign = self.m.mk_bv_extract(w - 1, w - 1, bv);
        let exp = self.m.mk_bv_extract(w - 2, sb - 1, bv);
        let sig = self.m.mk_bv_extract(sb - 2, 0, bv);
        let int = self.m.mk_int_sort();
        let sig_sort = self.m.get_sort(sig);
        let b2n = self
            .m
            .mk_func_decl(crate::util::symbol::Symbol::new("bv2nat"), &[sig_sort], int);
        let sig_int = self.m.mk_app(b2n, &[sig]);
        let sigv = self.m.mk_to_real(sig_int);
        let bias = (1i64 << (eb - 1)) - 1;
        let hidden = Rational::from_integer(pow2(sb - 1));
        // Per finite exponent field value, the largest last (the default).
        let top = (1i64 << eb) - 2;
        let mut mag: Option<AstId> = None;
        let mut gap: Option<AstId> = None;
        for k in (0..=top).rev() {
            let scale = pow2r(k.max(1) - bias - (sb as i64 - 1));
            let base = if k == 0 {
                Rational::from_integer(Int::from(0))
            } else {
                &scale * &hidden
            };
            let c = self.m.mk_numeral(scale.clone(), false);
            let scaled = self.m.mk_mul(&[c, sigv]);
            let b = self.m.mk_numeral(base, false);
            let mk = self.m.mk_add(&[b, scaled]);
            let gk = self.m.mk_numeral(scale, false);
            let kv = self.m.mk_bv_numeral(Int::from(k), eb);
            let is_k = self.m.mk_eq(exp, kv);
            mag = Some(match mag {
                None => mk,
                Some(rest) => self.m.mk_ite(is_k, mk, rest),
            });
            gap = Some(match gap {
                None => gk,
                Some(rest) => self.m.mk_ite(is_k, gk, rest),
            });
        }
        let one = self.m.mk_bv(1, 1);
        let is_neg = self.m.mk_eq(sign, one);
        let ones = self.m.mk_bv_numeral(pow2(eb) - Int::from(1), eb);
        let special = self.m.mk_eq(exp, ones);
        let zero_sig = self.m.mk_bv(0, sb - 1);
        let sig_zero = self.m.mk_eq(sig, zero_sig);
        Some(FpParts {
            exp,
            sig,
            is_neg,
            special,
            sig_zero,
            mag: mag?,
            gap_up: gap?,
        })
    }

    /// The constraints tying the fresh image `r` of `((_ to_fp eb sb) rm x)`
    /// to the real `x` (`rm` a rounding-mode term): `r` is no NaN, keeps the
    /// sign of `x`, is `+0` at `x = 0`, is infinite only past the overflow
    /// thresholds, and a finite `r` is `x` rounded by `rm` (in magnitudes:
    /// nearest within half the gaps with the tie rules, away from or toward
    /// zero within one gap, rounding toward zero saturating at the largest
    /// finite value).
    pub(super) fn fp_round_real_axioms(
        &mut self,
        r: AstId,
        rm: AstId,
        x: AstId,
        eb: u32,
        sb: u32,
    ) -> Option<Vec<AstId>> {
        let p = self.fp_parts(r, eb, sb)?;
        let rmb = self.rm_bits(rm)?;
        let mut ax = Vec::new();
        let real = |m: &mut crate::ast::manager::AstManager, q: Rational| m.mk_numeral(q, false);
        let zero = real(&mut self.m, Rational::from_integer(Int::from(0)));
        let half = real(
            &mut self.m,
            Rational::from_integer(Int::from(1)) / Rational::from_integer(Int::from(2)),
        );
        // Not NaN.
        let nan_sig = self.m.mk_not(p.sig_zero);
        let nan = self.m.mk_and(&[p.special, nan_sig]);
        ax.push(self.m.mk_not(nan));
        let is_inf = self.m.mk_and(&[p.special, p.sig_zero]);
        let not_neg = self.m.mk_not(p.is_neg);
        let pinf = self.m.mk_and(&[is_inf, not_neg]);
        let ninf = self.m.mk_and(&[is_inf, p.is_neg]);
        // The rounding mode.
        let mode = |ctx: &mut Self, c: i64| {
            let v = ctx.m.mk_bv(c, 3);
            ctx.m.mk_eq(rmb, v)
        };
        let rm_nte = mode(self, 0);
        let rm_nta = mode(self, 1);
        let rm_tp = mode(self, 2);
        let rm_tn = mode(self, 3);
        // Magnitudes.
        let x_neg = self.m.mk_lt(x, zero);
        let neg_x = self.m.mk_uminus(x);
        let abs_x = self.m.mk_ite(x_neg, neg_x, x);
        let abs_r = p.mag;
        let gap_up = p.gap_up;
        let w = eb + sb;
        let e0 = self.m.mk_bv(0, eb);
        let e1 = self.m.mk_bv(1, eb);
        let exp_zero = self.m.mk_eq(p.exp, e0);
        let exp_one = self.m.mk_eq(p.exp, e1);
        let sig_nz = self.m.mk_not(p.sig_zero);
        let full_gap = self.m.mk_or(&[exp_zero, exp_one, sig_nz]);
        let half_gap = self.m.mk_mul(&[half, gap_up]);
        let gap_down = self.m.mk_ite(full_gap, gap_up, half_gap);
        let half_down = self.m.mk_mul(&[half, gap_down]);
        let half_up = self.m.mk_mul(&[half, gap_up]);
        let lower_mid = self.m.mk_sub(&[abs_r, half_down]);
        let upper_mid = self.m.mk_add(&[abs_r, half_up]);
        let lo_ok = self.m.mk_le(lower_mid, abs_x);
        let hi_ok = self.m.mk_le(abs_x, upper_mid);
        let in_nearest = self.m.mk_and(&[lo_ok, hi_ok]);
        let tie_lo = self.m.mk_eq(abs_x, lower_mid);
        let tie_hi = self.m.mk_eq(abs_x, upper_mid);
        let lsb = self.m.mk_bv_extract(0, 0, p.sig);
        let b0 = self.m.mk_bv(0, 1);
        let sig_even = self.m.mk_eq(lsb, b0);
        let tie = self.m.mk_or(&[tie_lo, tie_hi]);
        let tie_even = self.m.mk_implies(tie, sig_even);
        let nte = self.m.mk_and(&[in_nearest, tie_even]);
        let not_tie_hi = self.m.mk_not(tie_hi);
        let nta = self.m.mk_and(&[in_nearest, not_tie_hi]);
        let emax = self.m.mk_bv_numeral(pow2(eb) - Int::from(2), eb);
        let at_emax = self.m.mk_eq(p.exp, emax);
        let sig_ones = self.m.mk_bv_numeral(pow2(sb - 1) - Int::from(1), sb - 1);
        let at_sig_max = self.m.mk_eq(p.sig, sig_ones);
        let is_max_finite = self.m.mk_and(&[at_emax, at_sig_max]);
        let below = self.m.mk_sub(&[abs_r, gap_down]);
        let a1 = self.m.mk_le(abs_x, abs_r);
        let a2 = self.m.mk_lt(below, abs_x);
        let away = self.m.mk_and(&[a1, a2]);
        let above = self.m.mk_add(&[abs_r, gap_up]);
        let z1 = self.m.mk_le(abs_r, abs_x);
        let z2 = self.m.mk_lt(abs_x, above);
        let z2 = self.m.mk_or(&[z2, is_max_finite]);
        let to_zero = self.m.mk_and(&[z1, z2]);
        let x_nonneg = self.m.mk_ge(x, zero);
        let tp = self.m.mk_ite(x_nonneg, away, to_zero);
        let tn = self.m.mk_ite(x_nonneg, to_zero, away);
        let mut cond = to_zero;
        cond = self.m.mk_ite(rm_tn, tn, cond);
        cond = self.m.mk_ite(rm_tp, tp, cond);
        cond = self.m.mk_ite(rm_nte, nte, cond);
        cond = self.m.mk_ite(rm_nta, nta, cond);
        let finite = self.m.mk_not(p.special);
        ax.push(self.m.mk_implies(finite, cond));
        // The sign.
        let x_pos = self.m.mk_gt(x, zero);
        ax.push(self.m.mk_implies(x_pos, not_neg));
        ax.push(self.m.mk_implies(x_neg, p.is_neg));
        // Zero is +0.
        let x_zero = self.m.mk_eq(x, zero);
        let pzero = self.m.mk_bv(0, w);
        let r_pzero = self.m.mk_eq(r, pzero);
        ax.push(self.m.mk_implies(x_zero, r_pzero));
        // Overflow: directed rounding past the largest finite value, nearest
        // rounding from the midpoint to the next binade.
        let bias = (1i64 << (eb - 1)) - 1;
        let max_real =
            (Rational::from_integer(Int::from(2)) - pow2r(-(sb as i64 - 1))) * pow2r(bias);
        let nearest_max = &max_real + &pow2r(bias - sb as i64);
        let e_max = real(&mut self.m, max_real.clone());
        let e_max_neg = real(&mut self.m, -max_real);
        let e_near = real(&mut self.m, nearest_max.clone());
        let e_near_neg = real(&mut self.m, -nearest_max);
        let nearest = self.m.mk_or(&[rm_nte, rm_nta]);
        let gt_max = self.m.mk_gt(x, e_max);
        let d_over = self.m.mk_and(&[rm_tp, gt_max]);
        let ge_near = self.m.mk_ge(x, e_near);
        let n_over = self.m.mk_and(&[nearest, ge_near]);
        let over = self.m.mk_or(&[d_over, n_over]);
        ax.push(self.m.mk_implies(pinf, over));
        let lt_max = self.m.mk_lt(x, e_max_neg);
        let d_under = self.m.mk_and(&[rm_tn, lt_max]);
        let le_near = self.m.mk_le(x, e_near_neg);
        let n_under = self.m.mk_and(&[nearest, le_near]);
        let under = self.m.mk_or(&[d_under, n_under]);
        ax.push(self.m.mk_implies(ninf, under));
        Some(ax)
    }

    /// The rounding constraints of every `to_fp` of a symbolic real whose
    /// image occurs in `goal` (see [`Self::fp_round_real_axioms`]).
    pub(super) fn fp_round_real_goal_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        if self.fp_round_real.is_empty() {
            return Vec::new();
        }
        // A worklist: a rounded real may itself mention another rounding.
        let mut out = Vec::new();
        let mut done = alloc::collections::BTreeSet::new();
        let mut todo = alloc::vec![goal];
        while let Some(root) = todo.pop() {
            for t in self.m.postorder(root) {
                if let Some(&(rm, x, eb, sb)) = self.fp_round_real.get(&t)
                    && done.insert(t)
                    && let Some(ax) = self.fp_round_real_axioms(t, rm, x, eb, sb)
                {
                    todo.extend(ax.iter().copied());
                    out.extend(ax);
                }
            }
        }
        out
    }
}
