//! # `util` — Foundation: numerals, containers, hashtables, symbols, vectors, params infra, rlimit, memory, sexpr
//!
//! **Port phase 0.** Ported from the Z3 C++ `util` component.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Numerals
//!
//! Z3's **entire** `util` numeral stack is provided by our first-party,
//! dependency-free [`puremp`](https://github.com/KarpelesLab/puremp) crate, used
//! directly throughout z3rs (also re-exported as [`crate::puremp`]) — no wrapper
//! layer. The mapping from Z3's numeral types:
//!
//! | Z3 `util`                     | `puremp`               |
//! |-------------------------------|------------------------|
//! | `mpn` / `mpz`                 | `Nat` / `Int`          |
//! | `mpq` / `rational`            | `Rational`             |
//! | `inf_rational` (ε-augmented)  | `InfRational`          |
//! | `mpbq` (dyadic `n·2^-k`)      | `Dyadic`               |
//! | `mpf` (software IEEE-754)     | `Float`                |
//! | `mpff` / `mpfx` (fixed prec.) | `FixedFloat`           |
//!
//! ## Upstream C++ components to port
//! - [x] `z3/src/util/{mpn,mpz,mpq,rational,inf_rational,mpbq,mpf,mpff,mpfx}`
//!       → all provided by `puremp`
//! - [ ] `z3/src/util` containers/hashtables/symbol/vector/params/rlimit/…
//!
//! ## Status: SCAFFOLD (numerals fully provided by `puremp`; rest to port)

// Submodules are declared here as components are ported, mirroring the upstream
// file layout (e.g. `pub mod symbol;` for `z3/src/util/symbol.{h,cpp}`).
