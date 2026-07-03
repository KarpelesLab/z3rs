# z3rs — Roadmap to a 100% pure-Rust Z3

> **Mission:** reimplement **all** of [Z3](https://github.com/Z3Prover/z3) (pinned
> at **v4.17.0**, ~695k LOC of C++) as a single Rust crate, `z3rs`, free of any
> third-party or native dependency — no GMP, no C — while remaining
> behaviourally faithful to upstream Z3. Its only dependency is our own
> pure-Rust, dependency-free numeric core, [`puremp`](https://github.com/KarpelesLab/puremp).

This document is the master plan: scope, architecture, the dependency-freedom
strategy, the phase-by-phase porting order, and a live progress tracker.
Methodology and per-module conventions live in [`PORTING.md`](PORTING.md).

---

## 1. Goals & hard constraints

1. **No third-party / native dependencies.** `std` only, plus the single
   first-party crate `puremp` (itself dependency-free) for arbitrary-precision
   arithmetic — pinned to its `default-features = false` core so the resolved
   tree stays free of any external crate. No GMP, no C, no `-sys` crates. This is
   enforced by the guard tests and CI (see §7).
2. **Single crate, single binary.** One crate `z3rs` exposing a library and the
   `z3rs` executable (the CLI-compatible counterpart of the `z3` shell).
3. **100% coverage.** Every upstream `src/` component (theory solvers, tactics,
   fixedpoint engines, quantifier elimination, optimization, parsers, C API) is
   in scope. Language bindings other than the C ABI are explicitly out of scope
   (see §2).
4. **Behavioural fidelity.** For any input, `z3rs` should return the same
   sat/unsat/unknown verdict and equivalent models/proofs as upstream Z3 4.17.0.
   Validated by differential testing (see §7).
5. **Safe Rust by default.** `unsafe` is permitted only where it buys correctness
   or performance that safe Rust cannot express (e.g. the bignum core), always
   localized and documented. No `unsafe` in the public API surface.

### Non-goals

- Bit-for-bit identical *internal* search traces (heuristic tie-breaks may
  differ); only the externally observable result must match.
- .NET / Java / Python / OCaml / Go / JS / Julia bindings. We port the **C ABI**
  (`api/z3_api.h` surface) so existing FFI consumers work, plus a native safe
  Rust API. Higher-level bindings can be layered on later, out of tree.
- Reproducing Z3's build system, Python codegen (`mk_*`), or CI tooling.

---

## 2. What "100% of Z3" means (scope inventory)

Ported, in dependency order (LOC = upstream C++, approximate):

| Upstream component        | LOC   | z3rs module                | Phase |
|---------------------------|-------|----------------------------|-------|
| `util`                    | 44.6k | `util`                     | 0     |
| `ast` (core files)        | 34.0k | `ast`                      | 1     |
| `math/polynomial`         | 21.4k | `math::polynomial`         | 1     |
| `math/lp`                 | 33.0k | `math::lp`                 | 1/5   |
| `math/{interval,simplex,dd,hilbert,subpaving,grobner}` | 23.0k | `math::*` | 1 |
| `params`                  | 2.2k  | `params`                   | 1     |
| `ast/rewriter`            | 41.8k | `rewriter`                 | 2     |
| `ast/euf`                 | 11.1k | `rewriter::euf`            | 2     |
| `ast/{normal_forms,substitution,macros,proofs,pattern,fpa,converters}` | 20.5k | `rewriter::*` | 2 |
| `model`                   | 6.9k  | `model`                    | 3     |
| `tactic` + portfolio      | 36.0k | `tactic`                   | 3     |
| `ast/simplifiers`         | 13.0k | `tactic::simplifiers`      | 3     |
| `ast/sls`                 | 21.3k | `tactic::sls`              | 3     |
| `sat` (+ `sat/smt`)       | 57.5k | `sat`                      | 4     |
| `nlsat`                   | 15.1k | `nlsat`                    | 5     |
| `math/realclosure`        | 7.6k  | `nlsat::realclosure`       | 5     |
| `smt`                     | 92.5k | `smt`                      | 5     |
| `solver`                  | 8.4k  | `solver`                   | 6     |
| `cmd_context` + `parsers/smt2` | 11.8k | `cmd_context`         | 6     |
| `qe`                      | 24.5k | `qe`                       | 7     |
| `muz` (Datalog/Spacer)    | 75.6k | `muz`                      | 7     |
| `opt`                     | 10.4k | `opt`                      | 7     |
| `parsers`                 | 5.0k  | `parsers`                  | 8     |
| `api` (C ABI + Rust API)  | 31.9k | `api`                      | 9     |
| **Total**                 | **~695k** |                        |       |

The `test/` tree (~41k LOC) is ported opportunistically into Rust `#[test]`s and
`tests/` as we go, not as a phase of its own.

---

## 3. Architecture

`z3rs` is one crate whose module tree mirrors Z3's `src/` layout. Within a crate
Rust modules may reference each other freely, which conveniently matches Z3's
occasionally-cyclic component graph. Modules are layered bottom-up: see the table
in [`src/lib.rs`](src/lib.rs).

The dependency DAG (derived from Z3's CMake `COMPONENT_DEPENDENCIES`):

```
util
 ├─ math (interval, polynomial, simplex, dd, hilbert, subpaving, grobner, lp)
 ├─ ast ──────────────┐
 │   └─ params        │
 │       └─ rewriter (euf, normal_forms, substitution, macros, proofs, pattern, fpa)
 │           ├─ model ── tactic
 │           └─ sat ──── nlsat
 │                        └─ smt ── solver ── cmd_context
 │                                    ├─ qe
 │                                    ├─ muz
 │                                    └─ opt
 └─ parsers ── api ── z3rs (bin)
```

---

## 4. The dependency-freedom strategy

The only place "no external library" is genuinely hard is **arbitrary-precision
arithmetic**, which upstream Z3 delegates to **GMP by default**. We solve it with
a first-party, pure-Rust, dependency-free crate,
[`puremp`](https://github.com/KarpelesLab/puremp), which provides:

- `puremp::Nat` / `puremp::Int` — arbitrary-precision naturals / signed integers
  (Z3's `mpn` / `mpz`)
- `puremp::Rational` — exact rationals (Z3's `mpq` / `rational`)
- `puremp::Float` — MPFR-class binary floats with directed rounding (backs Z3's
  `mpf` / the FloatingPoint theory)

z3rs depends on `puremp` with `default-features = false, features =
["std","rational","float"]`, so it pulls in **no** transitive crate
(`cargo tree` for z3rs is just `z3rs → puremp`). The dependency-free arithmetic
core keeps the whole "no GMP / no native code" guarantee intact.

z3rs uses `puremp`'s types **directly** throughout — `puremp` is ours, so there
is no wrapper/facade layer; the crate is re-exported as
[`z3rs::puremp`](src/lib.rs) for API consumers. As of `puremp` 0.1.2 it covers
Z3's **entire** numeral stack, so nothing in this layer is ported in-tree:

| Z3 `util`                    | `puremp`      |   | Z3 `util`                  | `puremp`      |
|------------------------------|---------------|---|----------------------------|---------------|
| `mpn` / `mpz`                | `Nat` / `Int` |   | `mpbq` (dyadic `n·2^-k`)   | `Dyadic`      |
| `mpq` / `rational`           | `Rational`    |   | `mpf` (software IEEE-754)  | `Float`       |
| `inf_rational` (ε-augmented) | `InfRational` |   | `mpff` / `mpfx` (fixed)    | `FixedFloat`  |

Everything above this layer (`ast`, `smt`, …) manipulates numerals through these
types, so the port never touches GMP concerns.

Other "external"-looking pieces and how we avoid deps (the reasoning core stays
`no_std + alloc`; each std-only mechanism is gated behind the `std` feature):
- Logical resource limit (`rlimit`, an operation counter) → pure `alloc`; only
  wall-clock timeouts / `scoped_timer` / ctrl-c need `std` (feature-gated).
- Threads / parallel solver / `par` tactic → `std` feature (`std::thread`, `sync`).
- File I/O → confined to the `z3rs` binary and parser entry points (readers/`&str`);
  the library never opens files.
- Memory manager / regions → global allocator + arena modules in `util`.
- Hashing / containers → `alloc`-backed maps + custom open-addressing
  maps where Z3's `hashtable.h`/`chashtable.h` semantics matter for iteration
  order (which can affect heuristic determinism).

---

## 5. Phased plan

Each phase has an **exit criterion** — a concrete, testable milestone. Phases are
strictly dependency-ordered; later phases may begin their scaffolding early but
cannot pass their exit criterion until predecessors do.

### Phase 0 — Foundation (`util`)
The **entire** numeral stack is provided by `puremp` (§4) — so Phase 0 is the
rest of `util`: core containers, `symbol` interning, `vector`/`buffer`,
`hashtable`, `params`/`gparams`, `rlimit`, `sexpr`, `region`, `memory`, `lbool`,
`statistics`.
- **Exit:** container/symbol/params semantics tested; the whole `util` layer
  builds `no_std + alloc`.

### Phase 1 — Terms & exact math (`ast`, `math`, `params`)
`ast` core (`ast`, `sort`, `func_decl`, `app`, `quantifier`, `ast_manager`,
`ast_translation`, pretty-printers) and the theory `*_decl_plugin`s (arith, bv,
array, datatype, seq, fpa, char, finite_set, dl, pb, recfun, special_relations).
`math` exact kernels (polynomial, interval, simplex, dd, hilbert, subpaving,
grobner; `lp` skeleton).
- **Exit:** can build any Z3 term programmatically, translate/pretty-print it,
  and round-trip it through `ast_smt2_pp`; polynomial & interval arithmetic
  differential-tested.

### Phase 2 — Rewriting & simplification (`rewriter`)
The `ast/rewriter` family: per-theory rewriters (arith, bv, array, bool, seq,
fpa, datatype, pb…), `th_rewriter`, `simplifier`, `euf` (E-graph / congruence
closure), `nnf`/`normal_forms`, `substitution`/unification, `macros`, `pattern`,
`bit_blaster`, `proofs`.
- **Exit:** `th_rewriter` reduces a large SMT-LIB corpus to the same normal
  forms as upstream (differential, modulo AC/ordering).

### Phase 3 — Models & tactics (`model`, `tactic`)
`model`, `model_evaluator`, model converters; the `tactic` framework, `probe`s,
`goal`s, and the preprocessing/solving tactic portfolio (`core_tactics`,
`arith_tactics`, `bv_tactics`, `fpa_tactics`, `simplifiers`, `sls`).
- **Exit:** tactic combinators (`then`/`or_else`/`par`/`repeat`) run;
  `simplify`/`ctx-solver-simplify` goals match upstream; `model_evaluator`
  agrees with Z3 on model-based evaluation.

### Phase 4 — SAT (`sat`)
CDCL core (`sat_solver`, watched literals, clause DB, GC, restarts, phase
saving), in-processing (`sat_simplifier`, `asymm_branch`, `scc`, `elim_eqs`,
vivification), `sat/smt` bridge scaffold, `drat` proof logging, DIMACS.
- **Exit:** solves the SATLIB / competition DIMACS suite with verdicts matching
  Z3's SAT engine; DRAT proofs check with an independent checker.

### Phase 5 — Core SMT engine (`smt`, `nlsat`)
`smt_context` (the CDCL(T) core), the theory solvers (`theory_arith`/`theory_lra`,
`theory_bv`, `theory_array`, `theory_datatype`, `theory_seq`, `theory_str`,
`theory_fpa`, `theory_pb`, `theory_special_relations`, `theory_recfun`),
quantifier instantiation (E-matching, MBQI), relevancy, conflict resolution.
`nlsat` + `realclosure` for nonlinear real arithmetic.
- **Exit:** `(check-sat)` over QF_* logics (QF_UF, QF_LIA, QF_LRA, QF_BV,
  QF_A/AX, QF_DT, QF_S, QF_FP, QF_NRA) matches upstream on SMT-LIB benchmarks;
  quantified fragments (UF, LIA, etc.) validated on a curated set.

### Phase 6 — Solver façade & command context (`solver`, `cmd_context`)
`solver` abstraction, `combined_solver`, incremental push/pop/assumptions,
`parallel` scaffold; `cmd_context` and the SMT-LIB2 command interpreter
(`smt2parser`) — enough to run `.smt2` scripts end-to-end via the `z3rs` binary.
- **Exit:** `z3rs file.smt2` reproduces `z3 file.smt2` output (verdict + model +
  `(get-*)` responses) across an SMT-LIB regression corpus.

### Phase 7 — QE, fixedpoint, optimization (`qe`, `muz`, `opt`)
`qe`/`qe_lite`/`mbp` (quantifier elimination, model-based projection);
`muz` (Datalog `rel`, BMC, `clp`, `tab`, `ddnf`, and **Spacer** — the Horn/PDR
engine); `opt` (MaxSAT cores: `maxres`, `wmax`, `pb`, Pareto/box optimization).
- **Exit:** Horn benchmarks (CHC-COMP subset) and MaxSMT/optimization objectives
  match upstream verdicts and optima.

### Phase 8 — Parsers (`parsers`)
Full `parsers/smt2` conformance (including `(get-proof)`, `(get-unsat-core)`,
declarations, `define-fun-rec`, datatypes), plus the Datalog frontend parser.
- **Exit:** parses the entire SMT-LIB benchmark set without error; frontends
  (`-smt2`, `-dimacs`, `-dl`, `-drat`) wired into the `z3rs` binary.

### Phase 9 — Public API (`api`)
The C ABI (`z3_api.h` surface: contexts, ASTs, solvers, models, tactics,
optimize, fixedpoint, parsers) exported as `extern "C"`, plus an idiomatic,
memory-safe native Rust API. `#[no_mangle]` symbols compatible with existing z3
FFI consumers.
- **Exit:** a drop-in `libz3rs` passes a representative slice of Z3's own C API
  test programs; the safe Rust API has doc-tested examples.

### Phase 10 — Hardening & parity
Fuzzing (SMT-LIB grammar + AST fuzzers), performance tuning to within a target
factor of upstream, `unknown`-rate parity, proof/unsat-core validation at scale,
documentation.
- **Exit:** green on the full differential corpus; published parity report.

---

## 6. Milestones (usable checkpoints)

- **M1 "It counts"** — Phase 0 done: `util` foundation over `puremp` numerals.
- **M2 "It thinks in terms"** — Phases 1–2: build, rewrite, simplify expressions.
- **M3 "It decides propositions"** — Phase 4: standalone SAT solver.
- **M4 "It solves QF"** — Phases 5–6: `z3rs file.smt2` on quantifier-free logics.
- **M5 "Full solver"** — Phase 7: quantifiers, Horn, optimization.
- **M6 "Drop-in"** — Phases 8–9: parser conformance + C ABI compatibility.
- **M7 "At parity"** — Phase 10: differential-clean, performance-competitive.

---

## 7. Methodology & testing (summary — details in [PORTING.md](PORTING.md))

- **Port, don't reinvent.** Translate upstream file-by-file, preserving structure
  and names where reasonable so diffs against Z3 stay legible. Each module header
  cites its upstream source (see `NOTICE`).
- **Differential testing is the spec.** The reference oracle is upstream Z3 4.17.0
  (built once, GMP-backed, kept in `z3/`). Every phase compares z3rs output to it:
  numerals (fuzz), rewriter normal forms, and `(check-sat)`/model/core/proof
  results over SMT-LIB.
- **Dependency-freedom enforcement:** `tests/no_external_deps.rs` allowlists
  exactly one dependency (`puremp`) and asserts the resolved lockfile contains
  nothing else; CI additionally runs `cargo tree -e normal` (must be just
  `z3rs → puremp`) and a `no_std` build for a bare target (e.g.
  `thumbv7em-none-eabi`) to prove no std leaks into the library.
- **Determinism:** container iteration order and tie-breaking are ported
  faithfully where they influence search, to keep differential noise low.

---

## 8. Progress tracker

Status legend: ⬜ not started · 🟨 in progress · ✅ done (phase exit criterion met).

| Phase | Area                         | Status | Notes |
|------:|------------------------------|:------:|-------|
| 0     | `util` foundation            | 🟨     | done: numerals (`puremp`), hash, lbool, symbol, spinlock, bit_vector, zstring · to do: containers/params/rlimit |
| 1     | `ast` / `math` / `params`    | 🟨     | ast: kinds/parameter/SortSize, node types, hash-consing manager, `basic`+`arith`+`bv` families, traversal/recognizers, s-expr pp · to do: array/datatype/seq/fpa theories, quantifiers, `math`, `params` |
| 2     | `rewriter`                   | 🟨     | `th_rewriter` driver + boolean & arithmetic constant folding, substitution, NNF · to do: theory rewriters, `euf`, `bit_blaster` |
| 3     | `model` / `tactic`           | ⬜     |       |
| 4     | `sat`                        | 🟨     | CDCL solver (2-watched literals, 1-UIP learning, backjumping, VSIDS, Luby restarts), Tseitin AST→CNF, DIMACS frontend · to do: assumptions/cores, clause-DB reduction, `sat_smt` |
| 5     | `smt` / `nlsat`              | 🟨     | lazy DPLL(T): congruence-closure e-graph (QF_UF) + Fourier–Motzkin linear arithmetic (QF_LRA) · to do: Nelson–Oppen combination, simplex, online propagation, bv/array theories, quantifiers |
| 6     | `solver` / `cmd_context`     | 🟨     | SMT-LIB2 front end: declares, assert, check-sat, let, push/pop/reset, define-fun, Bool/Int/Real, linear arith + UF; `z3rs file.smt2` decides QF_UF/QF_LRA · to do: get-model/get-value, full command set |
| 7     | `qe` / `muz` / `opt`         | ⬜     |       |
| 8     | `parsers`                    | ⬜     |       |
| 9     | `api`                        | ⬜     |       |
| 10    | hardening & parity           | ⬜     |       |

Fine-grained per-file checklists live in each module's `mod.rs` header (search
for `- [ ]`).

---

## 9. Risks & open questions

- **Scale.** ~695k LOC is a multi-person-year effort. The layering above lets work
  proceed in parallel *within* a phase once the phase's dependencies are stable.
- **Bignum performance.** GMP is highly optimized; a pure-Rust core may be slower
  on some workloads. This is now `puremp`'s concern (small-value inlining, hot
  mul/div paths), decoupled from the port. Mitigation: profile against
  GMP-backed Z3 and push optimizations into `puremp` behind its stable API.
- **Heuristic drift → differential noise.** Small ordering differences can flip
  `unknown` vs a definite answer under resource limits. Mitigation: port hash/
  container ordering faithfully; compare with generous limits first.
- **`smt` monolith (92k LOC).** The core engine is the largest single risk;
  budget extra time and land theory solvers incrementally behind the SAT core.
- **Spacer / `muz` (75k LOC).** Deep and lightly documented; may need upstream
  authors' papers as reference.

---

*z3rs is a derivative work of Z3 (© Microsoft Corporation, MIT). Not affiliated
with or endorsed by Microsoft. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).*
