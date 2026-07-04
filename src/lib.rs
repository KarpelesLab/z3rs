//! # z3rs — a pure-Rust port of the Z3 theorem prover
//!
//! `z3rs` is a from-scratch reimplementation of
//! [Z3](https://github.com/Z3Prover/z3) (v4.17.0) in safe, idiomatic Rust.
//! The goal is a 1:1 behavioural port of 100% of Z3 with **no third-party or
//! native dependency** — no GMP, no C. The crate is `no_std` (needs only
//! `alloc`) by default; the optional `std` feature adds std-backed conveniences.
//! Its sole dependency is our own pure-Rust, dependency-free numeric core
//! [`puremp`], re-exported below and used directly throughout the port.
//!
//! This is a large, multi-phase effort. See [`ROADMAP.md`](../ROADMAP.md) for the
//! staged plan, and [`PORTING.md`](../PORTING.md) for the porting methodology and
//! differential-testing strategy against upstream Z3.
//!
//! ## Attribution
//!
//! z3rs is a derivative work of Z3, Copyright (c) Microsoft Corporation, used
//! under the MIT License. See [`LICENSE`](../LICENSE) and [`NOTICE`](../NOTICE).
//!
//! ## Architecture
//!
//! The module tree mirrors Z3's `src/` component layering. Modules are ordered
//! bottom-up by dependency (each layer only uses layers above it in this list):
//!
//! | Module          | Phase | Upstream `z3/src/…`                                   |
//! |-----------------|-------|-------------------------------------------------------|
//! | [`util`]        | 0     | `util` (bignum, containers, symbols, params infra)    |
//! | [`math`]        | 1     | `math/*` (polynomial, interval, simplex, dd, lp, …)   |
//! | [`ast`]         | 1     | `ast` (terms, sorts, decls, theory decl_plugins)      |
//! | [`params`]      | 1     | `params`                                              |
//! | [`rewriter`]    | 2     | `ast/rewriter`, `ast/euf`, `ast/normal_forms`, …      |
//! | [`model`]       | 3     | `model`                                               |
//! | [`tactic`]      | 3     | `tactic` + tactic portfolio                           |
//! | [`sat`]         | 4     | `sat`, `sat/smt`                                      |
//! | [`nlsat`]       | 5     | `nlsat`, `math/realclosure`                           |
//! | [`smt`]         | 5     | `smt` (core SMT engine)                               |
//! | [`solver`]      | 6     | `solver`                                              |
//! | [`cmd_context`] | 6     | `cmd_context`, `parsers/smt2`                         |
//! | [`qe`]          | 7     | `qe`, `qe/mbp`                                         |
//! | [`muz`]         | 7     | `muz` (Datalog / Spacer / Horn)                       |
//! | [`opt`]         | 7     | `opt` (MaxSAT / optimization)                         |
//! | [`parsers`]     | 8     | `parsers`                                             |
//! | [`api`]         | 9     | `api` (C ABI + safe Rust surface)                     |
//!
//! Nothing below is functional yet — every module is a documented scaffold.

// `no_std` by default; `alloc` is always required. `std` (feature) or `test`
// builds pull in the standard library.
#![cfg_attr(not(any(feature = "std", test)), no_std)]
// Keep the dependency-free, safety-first posture visible and enforced.
#![forbid(unsafe_op_in_unsafe_fn)]
#![deny(rust_2018_idioms)]
#![allow(dead_code)] // expected while modules are scaffolds

// Established now so the `no_std` posture holds from the start; used as modules land.
#[allow(unused_extern_crates)]
extern crate alloc;

/// The arbitrary-precision numeric core, re-exported so consumers of z3rs's API
/// get the numeral types (`puremp::Int`, `puremp::Rational`, `puremp::Float`)
/// without adding their own dependency. z3rs uses these types directly — there
/// is no wrapper layer.
pub use puremp;

// --- Phase 0: foundation ---
pub mod util;

// --- Phase 1: math + AST ---
pub mod ast;
pub mod math;
pub mod params;

// --- Phase 2: rewriting / simplification ---
pub mod rewriter;

// --- Phase 3: models + tactics ---
pub mod model;
pub mod tactic;

// --- Phase 4: SAT ---
pub mod sat;

// --- Phase 5: nonlinear SAT + core SMT ---
pub mod nlsat;
pub mod smt;

// --- Phase 6: solver abstraction + command context ---
pub mod cmd_context;
pub mod solver;

// --- Phase 7: quantifier elimination, fixedpoint, optimization ---
pub mod muz;
pub mod opt;
pub mod qe;

// --- Phase 8: parsers ---
pub mod parsers;

// --- Phase 9: public API ---
pub mod api;

// The C ABI (opt-in via the `ffi` feature); the only module that uses `unsafe`.
#[cfg(feature = "ffi")]
pub mod ffi;

/// The upstream Z3 version this port tracks.
pub const Z3_UPSTREAM_VERSION: &str = "4.17.0";

/// z3rs crate version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[cfg(test)]
mod tests {
    use puremp::{Dyadic, Int, Rational};

    /// Smoke-test that the `puremp` numeric backend — including the numeral
    /// types z3rs needs beyond integers/rationals — is wired and usable.
    #[test]
    fn numeric_backend_is_wired() {
        let a: Int = "123456789012345678901234567890".parse().unwrap();
        let b: Int = Int::from(1_000_000_007i64);
        assert!(&a * &b > a);

        let half = Rational::new(Int::from(1), Int::from(2));
        let third = Rational::new(Int::from(1), Int::from(3));
        assert_eq!(&half + &third, Rational::new(Int::from(5), Int::from(6)));

        // Dyadic (Z3's `mpbq`): `new(n, k)` is n·2⁻ᵏ, so new(3, 1) == 3/2.
        let three_halves = Dyadic::new(Int::from(3), 1);
        assert_eq!(
            three_halves.to_rational(),
            Rational::new(Int::from(3), Int::from(2))
        );
        // canonical form has an odd numerator: 3·2⁻¹.
        assert_eq!(*three_halves.numerator(), Int::from(3));
        assert_eq!(three_halves.scale(), 1);
    }
}
