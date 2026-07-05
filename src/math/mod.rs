//! # `math` — Exact math: polynomial arithmetic, intervals, simplex, decision diagrams, Groebner, linear programming
//!
//! **Port phase 1.** Ported from the Z3 C++ component(s) below.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Upstream C++ components to port
//! - [x] `z3/src/math/polynomial` → [`polynomial`] (multivariate over `Rational`)
//! - [x] `z3/src/math/interval` → [`interval`] (rational interval arithmetic)
//! - [ ] `z3/src/simplex`
//! - [ ] `z3/src/dd`
//! - [ ] `z3/src/hilbert`
//! - [ ] `z3/src/subpaving`
//! - [ ] `z3/src/grobner`
//! - [ ] `z3/src/lp`
//!
//! ## Status: IN PROGRESS — exact polynomial & interval kernels landed

pub mod interval;
pub mod polynomial;
pub mod resultant;
pub mod upoly;

pub use interval::{Bound, Interval};
pub use polynomial::{Monomial, Polynomial};
pub use resultant::{discriminant, resultant};
pub use upoly::UPoly;
