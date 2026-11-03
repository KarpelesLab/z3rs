//! A replica of z3's structural AST hash for sorts and function declarations
//! (`get_node_hash` in `z3/src/ast/ast.cpp`), and of the slot order of the
//! `obj_map<func_decl, …>` a model keeps its constants in.
//!
//! z3's `proto_model::mk_model` copies the solver's constant interpretations
//! into the final model by iterating that map, so the order `get-model` lists
//! the solver-interpreted constants in is the map's physical slot layout:
//! decided by each declaration's hash (name, range sort, skolem info) and the
//! order the model generator registered them in. The hash combinators here are
//! those of z3 5.3.2's `util/hash.h` (its `combine_hash` mixes through
//! `hash_u`, unlike the older one in [`crate::util::hash`]).

use crate::util::hash::{hash_u, string_hash};
use alloc::vec;
use alloc::vec::Vec;

/// z3's `basic_family_id`.
pub const BASIC_FID: i32 = 0;
/// z3's `user_sort_family_id`.
pub const USER_SORT_FID: i32 = 4;
/// z3's `arith_family_id`.
pub const ARITH_FID: i32 = 5;
/// The family ids the command context's manager hands out as the theories
/// are first named (as observed in z3 5.3.2: `datatype` before `bv` and
/// `array`, then `recfun`, `char`, `seq`, `pb`, `fpa`, …): `datatype`.
pub const DATATYPE_FID: i32 = 7;
/// `bv`.
pub const BV_FID: i32 = 8;
/// `array`.
pub const ARRAY_FID: i32 = 9;
/// `char`.
pub const CHAR_FID: i32 = 11;
/// `seq`.
pub const SEQ_FID: i32 = 12;
/// `fpa`.
pub const FPA_FID: i32 = 14;

/// Bob Jenkins' `mix` (z3's `mix` macro), returning `c`'s final value along
/// with `a` and `b`.
#[rustfmt::skip]
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

/// z3 5.3.2's `combine_hash`.
pub fn combine_hash(h1: u32, h2: u32) -> u32 {
    let h1 = h1
        ^ h2.wrapping_add(0x9e37_79b9)
            .wrapping_add(h1 << 6)
            .wrapping_add(h1 >> 2);
    hash_u(h1)
}

/// The hash of a string symbol (`string_hash` seeded with 17, as z3's symbol
/// table stores it).
pub fn symbol_hash(name: &str) -> u32 {
    string_hash(name.as_bytes(), 17)
}

/// z3's `get_composite_hash` with the default kind hash (17) over the given
/// child hashes.
fn composite_hash(ch: &[u32]) -> u32 {
    let kind = 17u32;
    let (mut a, mut b, mut c) = (0x9e37_79b9u32, 0x9e37_79b9u32, 11u32);
    match ch.len() {
        0 => c,
        1 => {
            a = a.wrapping_add(kind);
            b = ch[0];
            mix(a, b, c).2
        }
        2 => {
            a = a.wrapping_add(kind);
            b = b.wrapping_add(ch[0]);
            c = c.wrapping_add(ch[1]);
            mix(a, b, c).2
        }
        3 => {
            a = a.wrapping_add(ch[0]);
            b = b.wrapping_add(ch[1]);
            c = c.wrapping_add(ch[2]);
            (a, b, c) = mix(a, b, c);
            a = a.wrapping_add(kind);
            mix(a, b, c).2
        }
        _ => {
            let mut n = ch.len();
            while n >= 3 {
                n -= 1;
                a = a.wrapping_add(ch[n]);
                n -= 1;
                b = b.wrapping_add(ch[n]);
                n -= 1;
                c = c.wrapping_add(ch[n]);
                (a, b, c) = mix(a, b, c);
            }
            a = a.wrapping_add(kind);
            if n == 2 {
                b = b.wrapping_add(ch[1]);
            }
            if n >= 1 {
                c = c.wrapping_add(ch[0]);
            }
            mix(a, b, c).2
        }
    }
}

/// `decl_info::hash` of `(family id, kind, parameters)`, the parameters given
/// by their hashes (an integer is itself, a sort or symbol its hash).
pub fn info_hash(fid: i32, kind: i32, params: &[u32]) -> u32 {
    let c = if params.is_empty() {
        0
    } else {
        composite_hash(params)
    };
    mix(fid as u32, kind as u32, c).2
}

/// The hash of a sort named `name` with sort info hash `info` (`None` for a
/// sort without info).
pub fn sort_hash(name: &str, info: Option<u32>) -> u32 {
    match info {
        None => symbol_hash(name),
        Some(i) => combine_hash(symbol_hash(name), i),
    }
}

/// z3's `ast_array_hash` of the child hashes `hs` seeded with `init`.
fn ast_array_hash(hs: &[u32], init: u32) -> u32 {
    match hs.len() {
        0 => init,
        1 => combine_hash(hs[0], init),
        2 => combine_hash(combine_hash(hs[0], hs[1]), init),
        3 => combine_hash(combine_hash(hs[0], hs[1]), combine_hash(hs[2], init)),
        _ => {
            let (mut a, mut b, mut c) = (0x9e37_79b9u32, 0x9e37_79b9u32, init);
            let mut n = hs.len();
            while n >= 3 {
                n -= 1;
                a = a.wrapping_add(hs[n]);
                n -= 1;
                b = b.wrapping_add(hs[n]);
                n -= 1;
                c = c.wrapping_add(hs[n]);
                (a, b, c) = mix(a, b, c);
            }
            if n == 2 {
                b = b.wrapping_add(hs[1]);
            }
            if n >= 1 {
                c = c.wrapping_add(hs[0]);
            }
            mix(a, b, c).2
        }
    }
}

/// The hash of the function declaration `name : domain → range` (sort
/// hashes), with declaration info hash `info` (0 for a user declaration).
pub fn decl_hash(name: &str, domain: &[u32], range: u32, info: u32) -> u32 {
    let h = combine_hash(symbol_hash(name), range);
    ast_array_hash(domain, combine_hash(h, info))
}

/// The info hash of a skolem constant z3 makes with `mk_fresh_const`
/// (`func_decl_info(null_family_id, null_decl_kind)`).
pub fn skolem_info_hash() -> u32 {
    info_hash(-1, -1, &[])
}

/// z3's `Bool` sort hash.
pub fn bool_sort_hash() -> u32 {
    sort_hash("Bool", Some(info_hash(BASIC_FID, 0, &[])))
}

/// z3's `String` sort hash: `(Seq Unicode)` named `String`.
pub fn string_sort_hash() -> u32 {
    let ch = sort_hash("Unicode", Some(info_hash(CHAR_FID, 0, &[])));
    sort_hash("String", Some(info_hash(SEQ_FID, 0, &[ch])))
}

/// The order an `obj_map` (z3's `core_hashtable`: capacity 8, linear probing,
/// doubling once `size * 4 > capacity * 3`) iterates entries inserted with
/// `hashes`, in that order: indexes into `hashes`, by slot. `relookup`: one
/// more `insert_if_not_there` of an existing key follows (its growth check
/// runs before the key is found).
pub fn obj_map_slot_order(hashes: &[u32], relookup: bool) -> Vec<usize> {
    fn grow(slots: &mut Vec<Option<usize>>, size: usize, hashes: &[u32]) {
        if size * 4 <= slots.len() * 3 {
            return;
        }
        let cap = slots.len() * 2;
        let mut grown = vec![None; cap];
        for e in slots.iter().flatten() {
            let mut i = (hashes[*e] as usize) & (cap - 1);
            while grown[i].is_some() {
                i = (i + 1) & (cap - 1);
            }
            grown[i] = Some(*e);
        }
        *slots = grown;
    }
    let mut slots: Vec<Option<usize>> = vec![None; 8];
    // Every key is new, so the table holds `k` entries before the `k`-th.
    for (k, &h) in hashes.iter().enumerate() {
        grow(&mut slots, k, hashes);
        let cap = slots.len();
        let mut i = (h as usize) & (cap - 1);
        while slots[i].is_some() {
            i = (i + 1) & (cap - 1);
        }
        slots[i] = Some(k);
    }
    if relookup {
        grow(&mut slots, hashes.len(), hashes);
    }
    slots.into_iter().flatten().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_sort_hash() -> u32 {
        sort_hash("Int", Some(info_hash(ARITH_FID, 1, &[])))
    }

    #[test]
    fn decl_hashes_match_z3() {
        // Values printed by an instrumented z3 5.3.2.
        assert_eq!(decl_hash("x", &[], int_sort_hash(), 0), 432_115_295);
        assert_eq!(decl_hash("y", &[], int_sort_hash(), 0), 1_365_890_499);
        assert_eq!(decl_hash("a", &[], string_sort_hash(), 0), 3_264_453_520);
        assert_eq!(decl_hash("b", &[], string_sort_hash(), 0), 2_817_032_688);
        let poly = decl_hash("poly!14", &[], bool_sort_hash(), skolem_info_hash());
        assert_eq!(poly, 3_293_742_520);
        let real = sort_hash("Real", Some(info_hash(ARITH_FID, 0, &[])));
        assert_eq!(decl_hash("r1", &[], real, 0), 1_360_868_736);
        let bv8 = sort_hash("bv", Some(info_hash(BV_FID, 0, &[8])));
        assert_eq!(decl_hash("bv1", &[], bv8, 0), 68_205_273);
        let bools = [int_sort_hash(), bool_sort_hash()];
        let arr = sort_hash("Array", Some(info_hash(ARRAY_FID, 0, &bools)));
        assert_eq!(decl_hash("ar", &[], arr, 0), 4_021_008_398);
        let fp = sort_hash("FloatingPoint", Some(info_hash(FPA_FID, 0, &[8, 24])));
        assert_eq!(decl_hash("f1", &[], fp, 0), 2_912_923_465);
        let rm = sort_hash("RoundingMode", Some(info_hash(FPA_FID, 1, &[])));
        assert_eq!(decl_hash("rm1", &[], rm, 0), 3_126_055_695);
        let sq = sort_hash("Seq", Some(info_hash(SEQ_FID, 0, &[int_sort_hash()])));
        assert_eq!(decl_hash("sq", &[], sq, 0), 2_909_291_098);
        let dt = sort_hash("D", Some(info_hash(DATATYPE_FID, 0, &[symbol_hash("D")])));
        assert_eq!(decl_hash("d1", &[], dt, 0), 1_369_883_122);
        let ps = [symbol_hash("L"), int_sort_hash()];
        let list = sort_hash("L", Some(info_hash(DATATYPE_FID, 0, &ps)));
        assert_eq!(decl_hash("l1", &[], list, 0), 4_118_404_278);
        // The first declared sort is user-sort kind 1.
        let u = sort_hash("U", Some(info_hash(USER_SORT_FID, 1, &[])));
        assert_eq!(decl_hash("u1", &[], u, 0), 70_173_403);
    }

    #[test]
    fn slot_order_probes_and_grows() {
        // Three keys of slot 0 keep their insertion order; slot 4 sorts after.
        assert_eq!(obj_map_slot_order(&[8, 16, 4, 0], false), [0, 1, 3, 2]);
        let many: Vec<u32> = (0..10).rev().collect();
        assert_eq!(
            obj_map_slot_order(&many, false),
            (0..10).rev().collect::<Vec<_>>()
        );
        // Seven keys fill a capacity-8 table; a later lookup doubles it.
        let seven = [6, 4, 6, 0, 12, 4, 0];
        assert_eq!(obj_map_slot_order(&seven, false), [3, 5, 6, 1, 4, 0, 2]);
        assert_eq!(obj_map_slot_order(&seven, true), [3, 6, 5, 1, 0, 2, 4]);
    }
}
