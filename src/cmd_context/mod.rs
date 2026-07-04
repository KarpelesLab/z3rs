//! # `cmd_context` — SMT-LIB2 command interpreter
//!
//! **Port phase 6.** Ported from `z3/src/cmd_context` + `z3/src/parsers/smt2`
//! (Z3 4.17.0, MIT). See [`ROADMAP.md`](../../ROADMAP.md) for the plan.
//!
//! ## Ported so far
//! - [x] a minimal SMT-LIB2 front end for the QF_UF subset → [`smt2`]
//! - [ ] full command set (`push`/`pop`, `get-model`, `get-value`, options),
//!   the arithmetic/bit-vector/array sorts, and the streaming interpreter
//!
//! ## Status: IN PROGRESS

pub mod smt2;

pub use smt2::{Session, run as run_smt2};
