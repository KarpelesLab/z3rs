//! # z3rs — a pure-Rust port of the Z3 theorem prover
//!
//! `z3rs` is a from-scratch, **zero-external-dependency** reimplementation of
//! [Z3](https://github.com/Z3Prover/z3) (v4.17.0) in safe, idiomatic Rust.
//! The goal is a 1:1 behavioural port of 100% of Z3 that links against nothing
//! but the Rust standard library — no GMP, no C, no third-party crates.
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

// Keep the zero-dependency, safety-first posture visible and enforced.
#![forbid(unsafe_op_in_unsafe_fn)]
#![deny(rust_2018_idioms)]
#![allow(dead_code)] // expected while modules are scaffolds

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

/// The upstream Z3 version this port tracks.
pub const Z3_UPSTREAM_VERSION: &str = "4.17.0";

/// z3rs crate version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
