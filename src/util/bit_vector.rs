//! Ported from `z3/src/util/bit_vector.{h,cpp}` (Z3 4.17.0, MIT). See NOTICE.
//!
//! A simple growable bit vector over 32-bit words. Bits past `len` in the final
//! word are "don't care" and are masked out by the content operations (`==`,
//! `|=`, `&=`, `contains`), matching Z3's semantics exactly.

use alloc::vec::Vec;
use core::hash::{Hash, Hasher};

use crate::util::hash::string_hash;

/// Words needed to hold `n` bits.
#[inline]
const fn num_words(n: usize) -> usize {
    n.div_ceil(32)
}

/// Bit position mask within a word.
#[inline]
const fn pos_mask(bit_idx: usize) -> u32 {
    1u32 << (bit_idx % 32)
}

/// Mask of the low `n` bits (`n` in `0..32`). `MK_MASK` in Z3.
#[inline]
const fn mk_mask(n: usize) -> u32 {
    // For n == 0 this is 0; callers special-case a fully-used last word.
    (1u32 << n).wrapping_sub(1)
}

/// A growable vector of bits.
#[derive(Clone, Default)]
pub struct BitVector {
    words: Vec<u32>,
    num_bits: usize,
}

impl BitVector {
    /// An empty bit vector.
    #[inline]
    pub const fn new() -> BitVector {
        BitVector {
            words: Vec::new(),
            num_bits: 0,
        }
    }

    /// An empty bit vector with room reserved for `reserve_num_bits` bits.
    pub fn with_capacity(reserve_num_bits: usize) -> BitVector {
        BitVector {
            words: Vec::with_capacity(num_words(reserve_num_bits)),
            num_bits: 0,
        }
    }

    /// Number of bits.
    #[inline]
    pub const fn len(&self) -> usize {
        self.num_bits
    }

    /// Is the bit vector empty?
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.num_bits == 0
    }

    /// Number of 32-bit words in use.
    #[inline]
    pub const fn num_words(&self) -> usize {
        num_words(self.num_bits)
    }

    /// The `word_idx`-th raw word.
    #[inline]
    pub fn word(&self, word_idx: usize) -> u32 {
        self.words[word_idx]
    }

    /// Clear all bits and set the length to zero (keeps capacity).
    pub fn reset(&mut self) {
        for w in &mut self.words {
            *w = 0;
        }
        self.num_bits = 0;
    }

    /// Zero every bit, keeping the length.
    pub fn fill0(&mut self) {
        for w in &mut self.words {
            *w = 0;
        }
    }

    /// Grow the backing store so that `n` words are available (zero-filled).
    #[inline]
    fn ensure_words(&mut self, n: usize) {
        if self.words.len() < n {
            self.words.resize(n, 0);
        }
    }

    /// Get bit `bit_idx`.
    #[inline]
    pub fn get(&self, bit_idx: usize) -> bool {
        debug_assert!(bit_idx < self.num_bits);
        (self.words[bit_idx / 32] & pos_mask(bit_idx)) != 0
    }

    /// Set bit `bit_idx` to 1.
    #[inline]
    pub fn set(&mut self, bit_idx: usize) {
        debug_assert!(bit_idx < self.num_bits);
        self.words[bit_idx / 32] |= pos_mask(bit_idx);
    }

    /// Set bit `bit_idx` to 0.
    #[inline]
    pub fn unset(&mut self, bit_idx: usize) {
        debug_assert!(bit_idx < self.num_bits);
        self.words[bit_idx / 32] &= !pos_mask(bit_idx);
    }

    /// Set bit `bit_idx` to `val`.
    #[inline]
    pub fn set_to(&mut self, bit_idx: usize, val: bool) {
        if val {
            self.set(bit_idx);
        } else {
            self.unset(bit_idx);
        }
    }

    /// Append a bit.
    pub fn push(&mut self, val: bool) {
        let idx = self.num_bits;
        self.num_bits += 1;
        self.ensure_words(num_words(self.num_bits));
        self.set_to(idx, val);
    }

    /// Remove the last bit.
    pub fn pop(&mut self) {
        debug_assert!(self.num_bits > 0);
        self.num_bits -= 1;
    }

    /// The last bit.
    #[inline]
    pub fn back(&self) -> bool {
        debug_assert!(!self.is_empty());
        self.get(self.num_bits - 1)
    }

    /// Truncate to `new_size` bits (must not grow).
    pub fn shrink(&mut self, new_size: usize) {
        debug_assert!(new_size <= self.num_bits);
        self.num_bits = new_size;
    }

    /// Resize to `new_size` bits, filling any new bits with `val`.
    pub fn resize(&mut self, new_size: usize, val: bool) {
        if new_size <= self.num_bits {
            self.num_bits = new_size;
            return;
        }
        let ewidx = num_words(new_size);
        self.ensure_words(ewidx);

        let bwidx = self.num_bits / 32;
        let pos = self.num_bits % 32;
        let mask = mk_mask(pos);
        let cval: u32 = if val {
            self.words[bwidx] |= !mask; // set the high bits of the partial word
            u32::MAX
        } else {
            self.words[bwidx] &= mask; // clear the high bits of the partial word
            0
        };
        // Fill the whole words above the partial one.
        for w in self.words[bwidx + 1..ewidx].iter_mut() {
            *w = cval;
        }
        self.num_bits = new_size;
    }

    /// Grow to at least `sz` bits, filling new bits with `val`.
    pub fn reserve(&mut self, sz: usize, val: bool) {
        if sz > self.num_bits {
            self.resize(sz, val);
        }
    }

    /// Increase the size by `k` zero bits, shifting existing bits up by `k`.
    pub fn shift_right(&mut self, k: usize) {
        if k == 0 {
            return;
        }
        let old_num_words = num_words(self.num_bits);
        let new_num_bits = self.num_bits + k;
        self.resize(new_num_bits, false);
        let new_num_words = num_words(new_num_bits);
        let bit_shift = k % 32;
        let word_shift = k / 32;
        if word_shift > 0 {
            let mut j = old_num_words;
            let mut i = old_num_words + word_shift;
            while j > 0 {
                j -= 1;
                i -= 1;
                self.words[i] = self.words[j];
            }
            while i > 0 {
                i -= 1;
                self.words[i] = 0;
            }
        }
        if bit_shift > 0 {
            let comp_shift = 32 - bit_shift;
            let mut prev = 0u32;
            for i in word_shift..new_num_words {
                let new_prev = self.words[i] >> comp_shift;
                self.words[i] <<= bit_shift;
                self.words[i] |= prev;
                prev = new_prev;
            }
        }
    }

    /// In-place OR with `source` (grows to fit `source`).
    pub fn or_assign(&mut self, source: &BitVector) {
        if self.num_bits < source.num_bits {
            self.resize(source.num_bits, false);
        }
        let n2 = source.num_words();
        if n2 == 0 {
            return;
        }
        let bit_rest = source.num_bits % 32;
        if bit_rest == 0 {
            for i in 0..n2 {
                self.words[i] |= source.words[i];
            }
        } else {
            for i in 0..n2 - 1 {
                self.words[i] |= source.words[i];
            }
            self.words[n2 - 1] |= source.words[n2 - 1] & mk_mask(bit_rest);
        }
    }

    /// In-place AND with `source`.
    pub fn and_assign(&mut self, source: &BitVector) {
        let n1 = self.num_words();
        let n2 = source.num_words();
        if n1 == 0 {
            return;
        }
        if n2 > n1 {
            for i in 0..n1 {
                self.words[i] &= source.words[i];
            }
        } else {
            let bit_rest = source.num_bits % 32;
            if bit_rest == 0 {
                for i in 0..n2 {
                    self.words[i] &= source.words[i];
                }
            } else {
                for i in 0..n2 - 1 {
                    self.words[i] &= source.words[i];
                }
                self.words[n2 - 1] &= source.words[n2 - 1] & mk_mask(bit_rest);
            }
            for w in self.words[n2..n1].iter_mut() {
                *w = 0;
            }
        }
    }

    /// Complement every bit in `0..len`.
    pub fn negate(&mut self) {
        let n = self.num_words();
        for w in self.words[..n].iter_mut() {
            *w = !*w;
        }
    }

    /// Does `self` cover every set bit of `other` (bitwise superset)?
    pub fn contains(&self, other: &BitVector) -> bool {
        let n = self.num_words();
        if n == 0 {
            return true;
        }
        for i in 0..n - 1 {
            if (self.words[i] & other.words[i]) != other.words[i] {
                return false;
            }
        }
        let bit_rest = self.num_bits % 32;
        let mask = if bit_rest == 0 {
            u32::MAX
        } else {
            mk_mask(bit_rest)
        };
        let other_data = other.words[n - 1] & mask;
        (self.words[n - 1] & other_data) == other_data
    }

    /// Z3's `get_hash`: Bob Jenkins hash over the first `len/8` bytes.
    pub fn get_hash(&self) -> u32 {
        let nbytes = self.num_bits / 8;
        let mut bytes = Vec::with_capacity(nbytes);
        'outer: for w in &self.words {
            for b in w.to_ne_bytes() {
                if bytes.len() == nbytes {
                    break 'outer;
                }
                bytes.push(b);
            }
        }
        string_hash(&bytes, 0)
    }

    /// Iterate the bits low-to-high.
    pub fn iter(&self) -> impl Iterator<Item = bool> + '_ {
        (0..self.num_bits).map(move |i| self.get(i))
    }
}

impl PartialEq for BitVector {
    fn eq(&self, other: &BitVector) -> bool {
        if self.num_bits != other.num_bits {
            return false;
        }
        let n = self.num_words();
        if n == 0 {
            return true;
        }
        for i in 0..n - 1 {
            if self.words[i] != other.words[i] {
                return false;
            }
        }
        let bit_rest = self.num_bits % 32;
        let mask = if bit_rest == 0 {
            u32::MAX
        } else {
            mk_mask(bit_rest)
        };
        (self.words[n - 1] & mask) == (other.words[n - 1] & mask)
    }
}

impl Eq for BitVector {}

impl Hash for BitVector {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Consistent with `Eq`: hash the length and the meaningful bits, masking
        // the partial final word so equal vectors hash equally.
        self.num_bits.hash(state);
        let n = self.num_words();
        if n == 0 {
            return;
        }
        for i in 0..n - 1 {
            state.write_u32(self.words[i]);
        }
        let bit_rest = self.num_bits % 32;
        let mask = if bit_rest == 0 {
            u32::MAX
        } else {
            mk_mask(bit_rest)
        };
        state.write_u32(self.words[n - 1] & mask);
    }
}

impl core::fmt::Display for BitVector {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for i in 0..self.num_bits {
            f.write_str(if self.get(i) { "1" } else { "0" })?;
        }
        Ok(())
    }
}

impl core::fmt::Debug for BitVector {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "BitVector[{self}]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn push_get_set() {
        let mut b = BitVector::new();
        for i in 0..100 {
            b.push(i % 3 == 0);
        }
        assert_eq!(b.len(), 100);
        for i in 0..100 {
            assert_eq!(b.get(i), i % 3 == 0);
        }
        b.set(1);
        assert!(b.get(1));
        b.unset(1);
        assert!(!b.get(1));
        b.set_to(1, true);
        assert!(b.get(1));
        assert_eq!(b.back(), b.get(99));
    }

    #[test]
    fn resize_fills_and_masks_partial_word() {
        let mut b = BitVector::new();
        b.resize(5, true);
        for i in 0..5 {
            assert!(b.get(i));
        }
        // Grow across a word boundary with 1-fill.
        b.resize(40, true);
        for i in 0..40 {
            assert!(b.get(i), "bit {i}");
        }
        // Shrink then grow with 0-fill: stale high bits must read as 0.
        b.shrink(5);
        b.resize(40, false);
        for i in 5..40 {
            assert!(!b.get(i), "bit {i} should be 0");
        }
    }

    #[test]
    fn equality_ignores_bits_past_len() {
        let mut a = BitVector::new();
        let mut b = BitVector::new();
        for _ in 0..5 {
            a.push(true);
            b.push(true);
        }
        // Poke a stale high bit into a's last word via resize/shrink dance.
        a.resize(20, true);
        a.shrink(5);
        assert_eq!(a, b);
        assert_eq!(a.get_hash(), b.get_hash());
    }

    #[test]
    fn bitwise_ops() {
        let mut a = BitVector::new();
        let mut b = BitVector::new();
        for i in 0..40 {
            a.push(i % 2 == 0);
            b.push(i % 3 == 0);
        }
        let mut or = a.clone();
        or.or_assign(&b);
        let mut and = a.clone();
        and.and_assign(&b);
        for i in 0..40 {
            assert_eq!(or.get(i), (i % 2 == 0) || (i % 3 == 0));
            assert_eq!(and.get(i), (i % 2 == 0) && (i % 3 == 0));
        }
        assert!(a.contains(&and));
        assert!(or.contains(&a));
        assert!(!a.contains(&or) || a == or);
    }

    #[test]
    fn shift_right_inserts_low_zeros() {
        let mut a = BitVector::new();
        for i in 0..10 {
            a.push(i % 2 == 0); // bits: 1010101010
        }
        a.shift_right(3);
        assert_eq!(a.len(), 13);
        for i in 0..3 {
            assert!(!a.get(i), "low bit {i} must be 0");
        }
        for i in 0..10 {
            assert_eq!(a.get(i + 3), i % 2 == 0);
        }
    }

    #[test]
    fn negate_and_display() {
        let mut a = BitVector::new();
        for _ in 0..4 {
            a.push(false);
        }
        a.set(1);
        assert_eq!(format!("{a}"), "0100");
        a.negate();
        assert_eq!(format!("{a}"), "1011");
    }
}
