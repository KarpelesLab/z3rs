# z3rs ↔ Z3 Parity Report

A published account of how `z3rs` (a pure-Rust, `no_std + alloc` port of Z3 whose
only dependency is `puremp`) compares to upstream **Z3** as a decision oracle.
This is the Phase 10 deliverable: *where the two agree, where `z3rs` soundly
declines, and how that is validated.*

The governing invariant is **soundness before completeness**: `z3rs` must never
return a verdict that contradicts Z3. Where it cannot decide an instance it
returns `unknown` — never a guess. Every claim below is checked by differential
testing against `/usr/bin/z3` (the methodology of ROADMAP §7).

## At a glance

| | |
|---|---|
| Phases at exit criterion | **11 / 11** (Phase 10 hardening exit met; performance/scale tuning is a continuous follow-on) |
| Rust source | ~27k lines across 20 modules (`util … api`) |
| Tests | 373 unit/integration `#[test]`s + 6 API doctests, all green |
| Differential corpus | 146 curated cases (full response stream vs z3), green |
| Cumulative fuzzing | ~77k random scripts vs z3 across all fragments, **0 unsound** after fixes |
| Dependencies | `z3rs → puremp` only (enforced by a guard test) |

## Per-theory coverage

"Decides" = returns a definite `sat`/`unsat` matching z3 across the fuzzed
fragment. "Declines" = returns a sound `unknown` on the noted hard tail rather
than guessing.

| Theory | Decides | Declines (sound `unknown`) |
|---|---|---|
| **QF_UF** | congruence closure at every sort, `distinct`, uninterpreted functions | — |
| **QF_LIA** | Fourier–Motzkin + branch-and-bound + Omega-test (GCD tightening, dark-shadow witness) | instances exceeding the work budget |
| **QF_LRA** | Fourier–Motzkin with witness reconstruction, strict/non-strict | budget exhaustion |
| **QF_BV** | full core bit-blasting (arith/bitwise/shift/div/rem/compare/concat/extract/ext) over CDCL | conflict-budget exhaustion on hard instances |
| **QF_A / AX** | read-over-write + extensionality array axioms | array combinators (`map`, `as-array`) beyond folded forms |
| **QF_DT** | datatypes: enums, records, recursive & mutually-recursive, parametric; `match`, selectors/testers | — |
| **QF_S** | string constant folding, symbolic `str.len`, word equations vs literals, regex membership, **length-link refutation** (`contains`/`prefixof`/`suffixof`/`str.at`), **bounded witness search** (concrete `sat` models) | deep content constraints (combined prefix+suffix content, long word equations) |
| **QF_FP** | Float64 folding; symbolic FP equality + classification via bit-blasting | symbolic FP arithmetic / ordered compares (circuits too slow for basic CDCL) |
| **QF_NRA** | full CAD over real algebraic numbers (McCallum projection, `sign_at_point`) | degenerate/nullified projections, over-cap degree/dimension |
| **QF_NIA** | linearization, univariate CAD, bounded-integer search, variable elimination | undecidable/unbounded nonlinear integer cases |
| **Quantified UF/LIA** | ground instantiation to a fixpoint, E-matching (recursive functions), finite Datalog/CHC | non-terminating instantiation, nested quantifiers, MBQI |
| **CHC (HORN)** | single-predicate transition systems: BMC (`unsat`) + k-induction (`sat`) | multi-predicate systems, non-k-inductive invariants (need Spacer/PDR + MBP) |

## Soundness validation

Soundness is established by **differential fuzzing**: generate random small
scripts, run both `z3rs` and `z3`, and flag any case where *both* return a
definite verdict but they *disagree*. `unknown` (either side), errors, and
timeouts are ignored — only a both-definite contradiction is a bug.

Across the project this method drove out **12+ real soundness bugs**, each fixed
and captured as a regression test:

- opaque term treated as a free variable in the univariate `sat` path
- mixed Int/Real elimination dropping an integrality constraint
- integer-root enumeration missing roots when the constant term is 0
- unsound `bv2int` elimination on compound arguments
- opaque exponentiation not gated as nonlinear
- CAD between-sector sample collapsing onto a section (open cells under strict inequalities)
- CHC arithmetic-recursion reporting a wrong `sat` (vacuous instantiation "saturation")
- string-witness search reporting spurious `sat` (new literals not asserted distinct)
- "functional" array constants (`(_ map f)`, `(_ as-array f)`, `(lambda …)`) used
  in equalities treated as free variables → spurious `sat`
- (plus earlier datatype selector-trigger and FP free-BV bugs)

Every one was a **wrong definite verdict** caught by differential fuzzing before
it could mislead — which is exactly why the fuzzing harness is run after every
completeness change.

Cumulative fuzzing to date: tens of thousands of nonlinear scripts, ~7.5k
multivariate CAD scripts, 3.3k CHC scripts, and a broad cross-theory sweep — all
**0 unsound** at their final state.

### Cross-theory agreement (latest sweep)

A 7,200-script differential sweep vs z3, `sat`/`unsat` verdicts only. "Both
definite" counts cases where z3 *and* z3rs each returned a definite verdict;
"agree" is how many of those matched. **Disagreements: 0 everywhere.**

| Fragment | scripts | both definite | agree | disagree |
|---|--:|--:|--:|--:|
| QF_UF | 420 | 420 | 420 | 0 |
| QF_LIA | 420 | 379 | 379 | 0 |
| QF_LRA | 420 | 417 | 417 | 0 |
| QF_BV | 420 | 420 | 420 | 0 |
| QF_A (arrays) | 420 | 139 | 139 | 0 |
| QF_DT (datatypes) | 420 | 412 | 412 | 0 |
| QF_S (strings) | 420 | 32 | 32 | 0 |
| QF_FP | 420 | 17 | 17 | 0 |
| Quantified UF/LIA | 420 | 420 | 420 | 0 |
| Mixed (UF+LIA, arrays+LIA, BV+UF) | 420 | 238 | 238 | 0 |
| div/mod with negatives | 300 | 300 | 300 | 0 |
| nonlinear (var·var, squares) | 300 | 261 | 261 | 0 |
| opaque `^` | 300 | 148 | 148 | 0 |
| bv2nat / int2bv | 300 | 54 | 54 | 0 |
| pseudo-boolean (at-least/at-most) | 300 | 230 | 230 | 0 |
| `(Set T)` sort | 300 | 235 | 235 | 0 |
| BV sdiv/srem/smod/shifts | 300 | 300 | 300 | 0 |
| BV sign/zero-extend, rotate | 300 | 300 | 300 | 0 |
| UF congruence/`distinct` | 300 | 300 | 300 | 0 |
| datatype acyclicity (deep) | 300 | 133 | 133 | 0 |
| **Total** | **7200** | — | — | **0** |

Where "both definite" is well below the script count (strings, FP, arrays,
bv2nat, deep datatypes), z3rs returned a sound `unknown` on the harder end of the
fragment — completeness, not correctness. No script produced opposing definite
verdicts.


## Known limitations (all sound `unknown`, never wrong)

- **Performance, not correctness**, bounds the hard tail: deep BMC, large
  bit-blasted circuits, and high-degree CAD hit resource budgets and decline.
- **CHC**: only single-predicate, k-inductive/bounded systems; the full
  CHC-COMP set needs Spacer PDR with model-based projection (a documented
  follow-on).
- **Quantifiers**: no MBQI; nested-quantifier goals decline.
- **C API**: a representative slice of the `Z3_` ABI (enough to link and run a
  canonical find-model program); the full `z3_api.h` surface is a follow-on.

These are completeness gaps. In every case `z3rs` returns `unknown` rather than a
verdict that could contradict Z3.
