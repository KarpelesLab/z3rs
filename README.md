# z3rs

[![CI](https://github.com/KarpelesLab/z3rs/actions/workflows/ci.yml/badge.svg)](https://github.com/KarpelesLab/z3rs/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/z3rs.svg)](https://crates.io/crates/z3rs)
[![docs.rs](https://img.shields.io/docsrs/z3rs)](https://docs.rs/z3rs)
[![MSRV](https://img.shields.io/badge/MSRV-1.88-blue.svg)](https://blog.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A **pure-Rust, `no_std`** port of the [Z3 theorem prover](https://github.com/Z3Prover/z3),
free of any third-party or native dependency.

`z3rs` reimplements Z3 (pinned at **v4.17.0**) as a single Rust crate with **no
GMP, no C, no `-sys` crate**. Its only dependency is our own pure-Rust,
dependency-free numeric core [`puremp`](https://github.com/KarpelesLab/puremp),
so the resolved dependency tree is just `z3rs → puremp`. The library is
`no_std` (needs only `alloc`); the optional `std` feature adds std-backed
conveniences. It aims to be behaviourally faithful to upstream Z3.

> **Status: feature-complete port, sound, hardening toward full parity.** Every
> Z3 theory has a present, **sound** implementation driven by a full **SMT-LIB 2**
> front end (`check-sat(-assuming)`, `get-value`, `get-model`, `get-unsat-core`,
> `get-proof`, `push`/`pop`, `define-fun`, datatypes, …) and a **C ABI** (`z3_api.h`
> slice big enough to link and run real find-model programs). In place:
>
> - a hash-consing AST, a simplifying rewriter, a **CDCL SAT core** (DIMACS), and a
>   **lazy DPLL(T)** engine with **bidirectional Nelson–Oppen** combination;
> - **QF_UF** (congruence closure), **QF_LIA/LRA** (Fourier–Motzkin + Omega +
>   branch-and-bound), **QF_BV** (full bit-blasting), **arrays** (read-over-write,
>   extensionality, const/`map`/`lambda`), **datatypes** (recursive, mutual,
>   parametric; occurs-check, enum pigeonhole);
> - **floating-point** bit-exact over the common surface (all arithmetic + rounding
>   modes + conversions), **QF_NRA** (full CAD), **QF_NIA** (CAD + witness + symbolic
>   `div`/`mod`), **strings & sequences** (order theories, word equations, witness),
>   **regex**, **quantifiers** (E-matching + Presburger/nonlinear ∀∃), and
>   **CHC/Horn** (BMC + k-induction + polyhedral reachability).
>
> The governing invariant is **soundness before completeness**: a work budget (or an
> undecided fragment) yields a sound **`unknown`**, never a wrong verdict or a hang.
> This is enforced by **continuous differential fuzzing against upstream z3** —
> ~90k+ scripts across every fragment, **0 known wrong verdict**; the method has
> driven out **20+ real soundness bugs**, each captured as a regression test. On a
> broad, common fragment of every theory z3rs returns the *same definite verdict* as
> z3; the remaining work (see [`ROADMAP.md`](ROADMAP.md)) is closing the hard
> completeness tail where z3rs still soundly declines, and performance on the largest
> circuits. Per-theory coverage: [`PARITY.md`](PARITY.md).
>
> ```sh
> $ z3rs problem.cnf          # DIMACS CNF
> s SATISFIABLE
> v 1 2 3 0
>
> $ z3rs problem.smt2         # SMT-LIB2 (all theories above)
> unsat
> ```

## Why

- **No native dependencies.** `cargo add z3rs` and go — no linking GMP or a C++
  toolchain, no `-sys` crate, works anywhere Rust does (incl. cross-compilation).
- **`no_std` + `alloc`.** The reasoning core runs without the standard library
  (embedded, wasm, kernel); `std` is an opt-in feature for timers/threads/I-O.
- **Memory safety.** A safe Rust surface over an SMT solver.
- **Legibility.** Ported file-by-file from Z3 so the two stay diffable.

## Layout

```
z3rs/
├── Cargo.toml        # package `z3rs`; only dependency is our own `puremp`
├── src/
│   ├── lib.rs        # module tree (mirrors z3/src), dependency-ordered
│   ├── main.rs       # the `z3rs` binary (CLI-compatible with `z3`)
│   ├── util/         # Phase 0: foundation (numerals via `puremp`)
│   ├── math/  ast/  params/          # Phase 1
│   ├── rewriter/                     # Phase 2
│   ├── model/  tactic/               # Phase 3
│   ├── sat/                          # Phase 4
│   ├── nlsat/  smt/                  # Phase 5
│   ├── solver/  cmd_context/         # Phase 6
│   ├── qe/  muz/  opt/               # Phase 7
│   ├── parsers/                      # Phase 8
│   └── api/                          # Phase 9
├── ROADMAP.md        # the master plan
├── PORTING.md        # how we translate C++ → Rust + testing strategy
└── z3/               # upstream Z3 4.17.0 (reference oracle; git-ignored)
```

## Build

```sh
cargo build                    # no_std library + `z3rs` binary
cargo run -- --version
cargo test
cargo build --lib --target thumbv7em-none-eabi   # proves the lib is no_std
```

The library is `no_std` by default. Enable std-backed features with
`--features std`. (The bundled `z3rs` binary links std itself for CLI I/O.)

## License & attribution

MIT. `z3rs` is a derivative work of Z3 (© Microsoft Corporation, MIT-licensed).
Not affiliated with or endorsed by Microsoft. See [`LICENSE`](LICENSE) and
[`NOTICE`](NOTICE).
