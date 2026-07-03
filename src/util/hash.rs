//! Ported from `z3/src/util/hash.{h,cpp}` (Z3 4.17.0, MIT). See NOTICE.
//!
//! Bob Jenkins' hash (lookup2) and the small integer mixers Z3 uses throughout.
//! All arithmetic is `u32`/`u64` wrapping, matching C's unsigned overflow.
//!
//! Note on faithfulness: the 12-byte block reads use native-endian loads and the
//! trailing-byte reads use signed-`char` sign extension, exactly mirroring Z3's
//! `memcpy`/`char const*` behaviour, so on the same platform the hash values are
//! bit-identical to upstream (as in Z3, they are not stable across endianness or
//! `char` signedness).

/// Bob Jenkins' `mix` — reversibly mixes three 32-bit words.
#[inline]
fn mix(mut a: u32, mut b: u32, mut c: u32) -> (u32, u32, u32) {
    a = a.wrapping_sub(b); a = a.wrapping_sub(c); a ^= c >> 13;
    b = b.wrapping_sub(c); b = b.wrapping_sub(a); b ^= a << 8;
    c = c.wrapping_sub(a); c = c.wrapping_sub(b); c ^= b >> 13;
    a = a.wrapping_sub(b); a = a.wrapping_sub(c); a ^= c >> 12;
    b = b.wrapping_sub(c); b = b.wrapping_sub(a); b ^= a << 16;
    c = c.wrapping_sub(a); c = c.wrapping_sub(b); c ^= b >> 5;
    a = a.wrapping_sub(b); a = a.wrapping_sub(c); a ^= c >> 3;
    b = b.wrapping_sub(c); b = b.wrapping_sub(a); b ^= a << 10;
    c = c.wrapping_sub(a); c = c.wrapping_sub(b); c ^= b >> 15;
    (a, b, c)
}

/// Hash a single 32-bit value.
#[inline]
pub fn hash_u(a: u32) -> u32 {
    let a = a.wrapping_add(0x7ed5_5d16).wrapping_add(a << 12);
    let a = (a ^ 0xc761_c23c) ^ (a >> 19);
    let a = a.wrapping_add(0x1656_67b1).wrapping_add(a << 5);
    let a = a.wrapping_add(0xd3a2_646c) ^ (a << 9);
    let a = a.wrapping_add(0xfd70_46c5).wrapping_add(a << 3);
    (a ^ 0xb55a_4f09) ^ (a >> 16)
}

/// Hash a single 64-bit value down to 32 bits.
#[inline]
pub fn hash_ull(mut a: u64) -> u32 {
    a = (!a).wrapping_add(a << 18);
    a ^= a >> 31;
    a = a.wrapping_add((a << 2).wrapping_add(a << 4));
    a ^= a >> 11;
    a = a.wrapping_add(a << 6);
    a ^= a >> 22;
    a as u32
}

/// Combine two hash codes into one (order-sensitive).
#[inline]
pub fn combine_hash(mut h1: u32, mut h2: u32) -> u32 {
    h2 = h2.wrapping_sub(h1); h2 ^= h1 << 8;
    h1 = h1.wrapping_sub(h2); h2 ^= h1 << 16;
    h2 = h2.wrapping_sub(h1); h2 ^= h1 << 10;
    h2
}

/// Hash a pair of 32-bit values.
#[inline]
pub fn hash_u_u(a: u32, b: u32) -> u32 {
    combine_hash(hash_u(a), hash_u(b))
}

#[inline]
fn read_u32(data: &[u8]) -> u32 {
    // Mirrors Z3's `memcpy(&n, s, 4)`: a native-endian load of 4 bytes.
    u32::from_ne_bytes([data[0], data[1], data[2], data[3]])
}

/// Bob Jenkins' string hash, seeded with `init_value`.
///
/// This is the workhorse hash used for symbols and byte-keyed tables.
pub fn string_hash(data: &[u8], init_value: u32) -> u32 {
    let length = data.len() as u32;
    let mut a = 0x9e37_79b9u32;
    let mut b = 0x9e37_79b9u32;
    let mut c = init_value;

    let mut off = 0usize;
    let mut len = length;
    while len >= 12 {
        a = a.wrapping_add(read_u32(&data[off..]));
        b = b.wrapping_add(read_u32(&data[off + 4..]));
        c = c.wrapping_add(read_u32(&data[off + 8..]));
        (a, b, c) = mix(a, b, c);
        off += 12;
        len -= 12;
    }

    c = c.wrapping_add(length);
    // Trailing 0..=11 bytes; sign-extend each like a signed `char`.
    let sb = |i: usize| data[off + i] as i8 as i32 as u32;
    // Fall-through switch: a length `len` runs every case `<= len`.
    if len >= 11 { c = c.wrapping_add(sb(10) << 24); }
    if len >= 10 { c = c.wrapping_add(sb(9) << 16); }
    if len >= 9  { c = c.wrapping_add(sb(8) << 8); }
    if len >= 8  { b = b.wrapping_add(sb(7) << 24); }
    if len >= 7  { b = b.wrapping_add(sb(6) << 16); }
    if len >= 6  { b = b.wrapping_add(sb(5) << 8); }
    if len >= 5  { b = b.wrapping_add(sb(4)); }
    if len >= 4  { a = a.wrapping_add(sb(3) << 24); }
    if len >= 3  { a = a.wrapping_add(sb(2) << 16); }
    if len >= 2  { a = a.wrapping_add(sb(1) << 8); }
    if len >= 1  { a = a.wrapping_add(sb(0)); }

    (_, _, c) = mix(a, b, c);
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_and_seed_sensitive() {
        assert_eq!(string_hash(b"hello", 17), string_hash(b"hello", 17));
        assert_ne!(string_hash(b"hello", 17), string_hash(b"hellp", 17));
        assert_ne!(string_hash(b"hello", 17), string_hash(b"hello", 18));
    }

    #[test]
    fn handles_long_keys_past_the_12_byte_block() {
        // >12 bytes exercises the main loop and the tail.
        let a = string_hash(b"the quick brown fox", 0);
        let b = string_hash(b"the quick brown fox", 0);
        assert_eq!(a, b);
        assert_ne!(a, string_hash(b"the quick brown fex", 0));
    }

    #[test]
    fn empty_key_is_init_dependent() {
        assert_ne!(string_hash(b"", 0), string_hash(b"", 1));
    }

    #[test]
    fn integer_mixers_are_stable() {
        assert_eq!(hash_u(0), hash_u(0));
        assert_ne!(hash_u(1), hash_u(2));
        assert_eq!(hash_u_u(3, 4), combine_hash(hash_u(3), hash_u(4)));
        assert_ne!(hash_u_u(3, 4), hash_u_u(4, 3));
        assert_eq!(hash_ull(0), hash_ull(0));
    }
}
