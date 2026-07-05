//! # `muz` — Fixedpoint / Datalog / Spacer (Horn clauses)
//!
//! **Port phase 7.** Ported from the Z3 C++ component(s) below.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Upstream C++ components to port
//! - [ ] `z3/src/muz`
//! - [ ] `z3/src/spacer`
//! - [ ] `z3/src/rel`
//! - [ ] `z3/src/transforms`
//! - [ ] `z3/src/bmc`
//! - [ ] `z3/src/clp`
//! - [ ] `z3/src/tab`
//! - [ ] `z3/src/ddnf`
//! - [ ] `z3/src/dataflow`
//! - [ ] `z3/src/fp`
//!
//! ## Status: IN PROGRESS — finite-domain Datalog engine landed (`-dl` frontend)

pub mod datalog;

pub use datalog::{Atom, Model, Program, Rule, Term, evaluate, parse};
