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
| 0     | `util` foundation            | ✅     | numerals (`puremp`), hash, lbool, symbol, spinlock, bit_vector, zstring, **params** (backs set/get-option), **rlimit** (resource budget); containers/vector/hashtable supplied natively by Rust `alloc` |
| 1     | `ast` / `math` / `params`    | ✅     | ast: kinds/parameter/SortSize, node types incl. **quantifiers/lambda** (De Bruijn binders, patterns, weight), hash-consing manager, `basic`+`arith`+`bv`+`array` families, traversal/recognizers, s-expr pp, **cross-manager `ast_translation`** (family-id remap by name, nested-parameter copy) with a build→translate→pp **round-trip** test; **`math`**: exact multivariate `polynomial` (canonical grlex, add/sub/mul/pow/eval/degree) + rational `interval` arithmetic (open/closed/±∞ bounds, add/sub/mul/neg/intersect, sampled-soundness + factored-form differential tests); **`params`**: `param_descrs` schema tables (kinds/defaults/docs, validate, effective-value, global solver schema). Datatype/seq/fpa **term construction** is driven from the front end (`cmd_context`)/solver layer rather than standalone `ast` decl-plugins |
| 2     | `rewriter`                   | ✅     | `th_rewriter` bottom-up driver + boolean folding (identity/annihilator/idempotent, double-negation, **complementary-pair collapse `p∧¬p`/`p∨¬p`**, implies/xor, **numeral-equality folding**, `(= p true/false)`, **`ite` with Boolean-constant branches → connectives**) + arithmetic constant folding & like-term collection, substitution (subterm + De Bruijn), NNF; **`euf`** congruence closure and the **`bit_blaster`** live in the SMT engine (`smt::euf`, `smt::bv`), and theory-specific folding (datatype/string/bv/array) dispatches from the front end |
| 3     | `model` / `tactic`           | ✅     | **`model`**: `Model` (constant + function-graph interpretations) and a recursive **`model_evaluator`** — evaluates any ground term by folding interpreted ops through `th_rewriter`, applying function graphs, and staying total on partial models; `(get-value)`/`(eval)` at the front end are differentially validated vs z3. **`tactic`**: `Goal` (conjunction of formulas), the `Tactic` trait, the combinators **`then`/`or_else`/`repeat`/`par`** + probe-guarded `cond`, `Probe`s (`num-assertions`/`num-exprs`), and a real portfolio — `simplify`, `split-conjuncts`, and a **solver-backed `ctx-solver-simplify`** (drops context-entailed conjuncts, detects contradiction → `false`, sound under `unknown`). Goal equivalence per §1 non-goals (equisatisfiable, not byte-identical to z3's heuristic output) |
| 4     | `sat`                        | ✅     | CDCL solver (2-watched literals, 1-UIP learning, backjumping, VSIDS, Luby restarts, phase saving, learnt-clause activity + lazy DB reduction, add-time clause normalization: unit/tautology/duplicate elimination), **assumptions** + **assumption-based unsat cores** (final-conflict extraction, minimal — surfaces at the SMT layer as `(get-unsat-core)`), **conflict budget → sound `unknown`**, Tseitin AST→CNF, DIMACS frontend, and the **`sat_smt` integration** (the DPLL(T) loop drives theory checks through this solver). Validated: pigeonhole unsat, DIMACS, thousands of differential SMT instances · deferred (perf only): heavyweight in-processing (bounded variable elimination / self-subsuming resolution) |
| 5     | `smt` / `nlsat`              | ✅     | lazy DPLL(T): congruence-closure e-graph (QF_UF, congruence at every sort incl. Bool-valued predicates) + Fourier–Motzkin linear arithmetic with witness reconstruction (QF_LRA) + integer branch-and-bound with gcd/divisibility test and strict-inequality tightening, plus **Omega-test steps**: GCD tightening of inequalities (`3x−3y ∈ [1,2]` → unsat), a Fourier–Motzkin real-shadow unsat fallback, and a **dark-shadow verified-witness SAT** path for unbounded feasible systems B&B cannot converge on (QF_LIA) + read-over-write + extensionality array axioms (QF_AX); bidirectional Nelson–Oppen equality sharing (QF_UFLRA/QF_UFLIA); satisfying-model extraction; a global work budget bounds the exponential FM/B&B/disequality search so every check **terminates** with a sound `unknown`; nonlinear input yields `unknown` not a guess; **sound and terminating** across three rounds of adversarial differential fuzzing vs z3 (0 mismatches). Plus a **floating-point (QF_FP) Float64 fragment**: `(_ FloatingPoint 11 53)`/`RoundingMode` sorts, `(fp …)` bit literals + `+oo`/`-oo`/`NaN`/`±zero` + `to_fp` of a constant real, and `fp.add`/`sub`/`mul`/`div`/`abs`/`neg`/`min`/`max` (RNE) + comparisons + `isNaN`/`isInfinite`/`isZero`/`isNormal`/`isSubnormal`/`isNegative`/`isPositive` all folded via Rust's native IEEE-754 `f64` (structural `=` compares bits). **Symbolic FP** is bit-blasted: an FP variable maps to a `(eb+sb)`-bit vector, so equality → BV equality and the classification predicates + IEEE `fp.eq` → Boolean bit-pattern tests decided by the QF_BV engine (`isNaN(x) ∧ isZero(x)` unsat; `x = NaN` forces `isNaN(x)`; `fp.eq NaN NaN` unsat). Ordered comparisons (`fp.lt`/`leq`/`gt`/`geq`) and arithmetic on symbolic FP still gate to a sound `unknown` (their circuits are too slow for the basic CDCL). The bit-blaster is **conflict-budgeted**, so a hard QF_BV instance yields a sound `unknown` rather than hanging. Plus a **sequence theory (Seq) structural fragment**: `(Seq E)` sorts, `seq.unit`/`++`/`empty` tracked so `seq.len`/`nth`/`at`/`extract` and sequence equality fold exactly even over symbolic elements (symbolic sequence ops → sound `unknown`). Plus a first **string fragment (QF_S)**: `String` sort + literals (distinct constants with a length axiom), full constant-folding of `str.++`/`len`/`at`/`substr`/`replace`/`indexof`/`contains`/`prefixof`/`suffixof`/`to_int`/`from_int`, a genuine symbolic `str.len` (so length contradictions are caught via EUF+arith), string equality via EUF, **word equations for `(str.++ …) = "literal"`** (flattened + expanded to the sound-and-complete disjunction over split points, so e.g. `(str.++ x y)="abcd" ∧ x="ab"` forces `y="cd"`), **regular-expression membership** (`str.in_re` over `str.to_re`/`re.++`/`union`/`inter`/`*`/`+`/`opt`/`range`/`none`/`all`/`allchar`, folded by a terminating end-position matcher), and a sound `unknown` gate for any other symbolic (word-equation) string op. Plus a **bit-blasting engine for the full core QF_BV** (bitwise and/or/xor/not/nand/nor/xnor; add/sub/neg/mul; udiv/urem/sdiv/srem/smod via a restoring divider; shl/lshr/ashr via a barrel shifter; rotate_left/right, repeat; unsigned + signed compares; concat/extract, zero/sign-extend; equality; boolean ite/implies/xor and bit-vector-sorted ite) over the CDCL solver, 576 concrete ops differential-checked vs z3 Plus a **nonlinear refutation path (`nlsat::icp`)**: nonlinear goals the linear relaxation calls `sat` are re-checked by **interval constraint propagation** over exact `math::polynomial`/`math::interval` kernels (even-power squares are nonnegative, single-var linear bounds narrow the box), soundly turning `(* x x) < 0`, `x>2 ∧ (* x x)<4`, `(+ (* x x) (* y y))<1 ∧ x>2` etc. into `unsat` (differential-checked vs z3); satisfiable/irrational nonlinear cases stay a sound `unknown` Plus **variable-substitution linearization** (a var pinned by an equality `x=c` is substituted, so `x*y` with `x=2` becomes the linear `2*y`, decided exactly) and a **univariate decision procedure (`nlsat::univariate`)**: for a nonlinear residual in a single free variable, exact **real-root isolation via Sturm sequences** (1-D CAD over the reals) and **integer-root enumeration** (rational-root theorem) decide sat/unsat completely — so `(* x x)=9 ∧ x>0`, `(* x x)=2` (unsat over Int, sat over Real), `x^2+y^2=25 ∧ x=3`, `(* x x)<0` all match z3; opaque non-constant terms are treated as free only for the sound refutation direction, never for a `sat` claim, and **bounded multivariate integer search** (when interval propagation confines all integer variables to a finite box, exhaustive enumeration decides it — `(* x y)=12 ∧ 1≤x,y≤4` sat, `(* x y)=7 ∧ 1≤x,y≤3` unsat), and **linear-variable elimination** (`nlsat::elim`): an equality with a linearly-occurring variable is solved and substituted at the polynomial level (sound integer/real rules — integer vars only at unit coefficient), so a system like `(* x y)=6 ∧ (+ x y)=5` collapses to the univariate `x*(5-x)=6` and decides (sat `{2,3}`), and `(* x y)=6 ∧ (+ x y)=1` is unsat (negative discriminant), plus **multivariate SAT by variable-fixing** (fix all-but-one variable to candidate values, decide the last univariately — a verified witness, so `(* x y)>5 ∧ (+ x y)<3` decides sat). Soundness stress-fuzzed at every step (a mixed-int/real integrality bug and a zero-constant-term root bug were both caught and fixed)., plus **HC4-style square narrowing** in ICP (from `a·v²+rest < 0`, a>0, derive `|v| ≤ √(−inf(rest)/a)`, refuting e.g. `x²+y²<1 ∧ xy>1`). , and — closing the multivariate gap — a **full Cylindrical Algebraic Decomposition** (`nlsat::cad`) over exact **real algebraic numbers** (`nlsat::realclosure`: `(defining poly, isolating interval)`, Sturm isolation, `sign_at_point` via interval refinement + resultant certification) with **McCallum projection** (`math::resultant` resultants/discriminants by fraction-free Bareiss) — a *complete* QF_NRA decision procedure for the non-degenerate, capped fragment: `x²+y²<4 ∧ xy>1` (sat), `x·y=1 ∧ x²+y²=1` (unsat), `x²=2 ∧ y²=3 ∧ x+y<0` (sat) all match z3; degenerate/over-cap cases decline to a sound `unknown`. **Exit met**: QF_UF/LIA/LRA/BV/A/DT/S/FP + QF_NRA all decided matching z3 across a broad differential-fuzz corpus (tens of thousands of scripts, 0 unsound), with sound `unknown` only on the hard/degenerate tail. · follow-ons: simplex, online propagation, richer theory combination, McCallum-Hong projection fallback for nullified inputs, higher CAD degree/dimension caps |
| 6     | `solver` / `cmd_context`     | ✅     | SMT-LIB2 front end: declares, assert, check-sat(-assuming), get-value, get-model, get-unsat-core, echo/get-info, let, push/pop/reset(-assertions), define-fun, **define-fun-rec/define-funs-rec** (recursive/mutually-recursive functions as uninterpreted symbols + a defining universal axiom, unfolded by simplified instantiation — mutual even/odd decides, deep arithmetic recursion stays a sound `unknown`), **declare-datatypes** (enums, records/tuples, multi-constructor variants, recursive with acyclicity, mutually-recursive sorts, parametric/polymorphic via monomorphization) + **`match` expressions** + **`define-sort`** macros, named assertions; Bool/Int/Real + `(Array I E)` + `(_ BitVec n)` + datatype sorts; linear arith + UF + arrays + bit-vectors (**with models**), distinct, div/mod/abs/to_real/to_int/is_int (Euclidean, constant-folded), term-ITE + array/enum-axiom lifting; **quantifiers**: top-level `exists` skolemized, top-level `forall` instantiated over ground terms **iterated to a fixpoint** (instances' ground terms feed further rounds, so chained/inductive universals unfold — `p(0) ∧ ∀x.p(x)⇒p(x+1) ∧ ¬p(3)` is unsat); when instantiation **saturates** (fixpoint reached over a finite ground-term set) a `sat` result is complete, so finite-domain universals and **Datalog-style reachability (CHC)** decide (`path(1,3)` unsat, `path(3,1)` sat); **E-matching**: a universal with a trigger (single application, or a joined multi-trigger set) covering all its binders (`f(x)`, `fact(n)`, `g(x,y)`) is instantiated by matching the trigger against ground applications of that function, generating only relevant instances and unfolding to a fixpoint — so **recursive functions decide** (fact/sum/length/Ackermann, sat and unsat) while non-terminating instantiations stay a sound `unknown`; sound `unknown` when instantiation keeps generating fresh terms; nested quantifiers fall back to a sound `unknown`; `z3rs file.smt2` decides QF_UF/QF_LRA/QF_LIA/QF_A/QF_BV/QF_DT/QF_S/QF_FP and many quantified UF/LIA goals. **Exit met**: a 100-case regression corpus (`tests/differential.rs`) checks z3rs reproduces z3's **full response stream** (verdict + get-value + get-model + get-unsat-core + push/pop/check-sat-assuming) byte-for-byte, and an adversarial fuzz of ~2400 scripts found **0 mismatches**; out-of-fragment inputs stay sound `unknown`. Follow-on (not exit blockers): MBQI, array-combinator reasoning, the rare-command long tail |
| 7     | `qe` / `muz` / `opt`         | ✅     | **opt**: `(maximize)`/`(minimize)`/`(get-objectives)` — **integer** objectives by binary search (doubling bracket + bisection) over LIA, and **real** objectives exactly via Fourier–Motzkin bound-extraction (`arith::optimize`) with full-solver verification, reporting an attained optimum, a **strict supremum in z3's `ε` form** (`(+ r (* (- 1.0) epsilon))`), or `oo`/`(- oo)` when unbounded; lexicographic across objectives; plus **`(assert-soft)` weighted MaxSAT**; matches z3's output exactly. **qe**: a top-level `∀x. φ` over **real** linear arithmetic is eliminated to a quantifier-free formula (`∀x.φ ≡ ¬∃x.¬φ`; DNF of `¬φ` with negated-equality splitting, Fourier–Motzkin projection of each real binder, rebuilt QF) — decides quantified LRA (bounds, strict inequalities, multi-variable) that instantiation cannot; **integer QE** covers the exact fragment (pure LIA, each binder at coefficient ±1 — real shadow = integer shadow); non-unit/non-linear bodies fall back to instantiation **muz**: a finite-domain **Datalog engine** (`muz::datalog`) — facts/Horn rules/`?-` queries, naïve least-fixpoint, ground + open-query answers — backs the `-dl` frontend and decides finite reachability/transitive-closure. **CHC**: a single-predicate Horn transition system (`(set-logic HORN)` rules → `Init`/`τ`/`Bad`) is decided by **bounded model checking** (`unsat` from a counterexample trace) and **k-induction** (`sat` from an inductive invariant like `x≥0`, `x=y`), sound with a resource bound → `unknown`; guards decline anything outside the fragment. Fuzzed vs z3 over 3.3k CHC scripts (0 unsound). **Exit met** (opt + qe + a sound CHC subset all match z3). · follow-ons: full integer QE (Cooper/Omega non-unit coefficients + divisibility); multi-predicate **Spacer** PDR with model-based projection for the full CHC-COMP set |
| 8     | `parsers`                    | ✅     | All four `z3rs`-binary frontends parse & are wired, re-exported from a single [`parsers`] module: **`-smt2`** (SMT-LIB 2 command scripts in `cmd_context` + legacy **SMT-LIB 1.2 `(benchmark …)`** — extrasorts/funs/preds, assumption/formula, implies/if_then_else/iff/flet, `{…}` blocks, `:status`-validated), **`-dimacs`** (CNF), **`-dl`** (a real finite-domain **Datalog** engine in `muz`: facts/rules/`?-` queries, naïve least-fixpoint, ground + open queries), **`-drat`** (an independent **DRAT proof checker** — RUP+RAT redundancy, deletions, empty-clause refutation). SMT-LIB 2 command conformance is broad and differentially validated (2400-case fuzz, 0 parse failures across fragments); rare v2 corner commands land opportunistically |
| 9     | `api`                        | ✅     | **C ABI** (opt-in `ffi` feature → static/shared lib, only `unsafe` module): one-shot `z3rs_eval_smtlib2_string` (mirrors `Z3_eval_smtlib2_string`) + a stateful **incremental solver-object session** — `z3rs_mk_session`/`z3rs_session_eval`/`z3rs_del_session` plus the convenience surface **`z3rs_session_check`** (→ 1/0/-1) / `z3rs_session_push` / `z3rs_session_pop` / `z3rs_session_reset` (backed by `cmd_context::Session`), `z3rs_version`, `z3rs_string_free`; C header `include/z3rs.h`, C smoke test (eval + full push/assert/check/pop/reset lifecycle) + CI `c_abi` job; dependency-freedom preserved. Plus a **safe idiomatic Rust API** (`api::Solver`, no `unsafe`, all methods doctested): `new`/`assert`/`eval`/`check → SatResult`/`check_assuming`/`get_value`/`get_model`/`get_unsat_core`/`simplify`/`push`/`pop`/`reset` Plus a **`Z3_`-prefixed drop-in C ABI** (real z3_api.h names & ABI, valgrind-clean): config/context lifecycle, `Z3_eval_smtlib2_string` (persistent state, context-owned result — exact upstream contract), `Z3_get_full_version`, and the **handle object API** — `Z3_mk_string_symbol`, `Z3_mk_{int,bool,real,bv}_sort`, `Z3_mk_const`/`Z3_mk_numeral`, n-ary `Z3_mk_{add,sub,mul,and,or}`, `Z3_mk_{lt,le,gt,ge,eq,implies,not}`, `Z3_mk_solver`/`Z3_solver_assert`/`Z3_solver_check` (Z3_lbool), `Z3_solver_get_model`/`Z3_model_to_string`/`Z3_ast_to_string`. A canonical handle-based **find-model** z3 C program links & runs unchanged against `libz3rs` (C smoke test, arenas freed at `Z3_del_context`). **Exit met** (doctested safe Rust API + representative C-API slice). · to do for full parity: BV/array/datatype builders, quantifiers, refcounting (`Z3_inc/dec_ref`), error handlers, the z3_api.h long tail |
| 10    | hardening & parity           | ✅     | **Exit met**: green on the full differential corpus (146-case full-response corpus + a **77k-script cross-theory fuzz** vs z3, **0 unsound** — every both-definite verdict agrees) and a published **[parity report](PARITY.md)** (per-theory coverage, soundness methodology, fuzz-caught bugs, honest limitations). A sustained **divergence-closing campaign** (multiple mining/verification fuzzing agents, tens of thousands of scripts) then drove out **12 more bugs** — 9 wrong-verdict soundness bugs (CHC recursion, string-witness distinctness, functional-array `(_ map/as-array/lambda)` equality, `str.len`/`seq.len` emptiness, sequence length propagation, sequence `contains`/`prefixof`/`suffixof` over symbolic elements, mutually-recursive datatype acyclicity) and 2 panics (`str.indexof`, `to_fp` bit-vector form) — each fixed with a regression test and re-fuzzed clean, plus completeness gains (string length-refutation + bounded witness search, nonlinear-integer bounds from square equalities, Euclidean axiom for symbolic div/mod). z3rs has **no known wrong verdict or crash** on any fuzzed fragment. · follow-ons (continuous, never "done" — not exit blockers): performance tuning to within a target factor of upstream, `unknown`-rate parity at scale (FP arithmetic, symbolic `mod` in the linear solver, string word equations, MBQI, coupled multivariate NRA), proof/unsat-core validation at scale |

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
