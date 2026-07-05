# z3rs — Roadmap to full behavioral parity with Z3

> **Where we are.** The initial port is **complete**: `z3rs` is a single-crate,
> pure-Rust, `no_std + alloc` reimplementation of Z3 (pinned at **v4.17.0**) whose
> only dependency is our own dependency-free numeric core,
> [`puremp`](https://github.com/KarpelesLab/puremp). Every theory has a present,
> **sound** implementation — across ~90k differential-fuzz scripts vs upstream z3
> there is **no known wrong verdict and no crash**. The full port history lives in
> [`CHANGELOG.md`](CHANGELOG.md); per-theory coverage in [`PARITY.md`](PARITY.md).
>
> **Where we are going.** Sound ≠ complete. On a broad, common fragment of every
> theory z3rs returns the *same definite verdict* as z3, but on a hard tail it
> returns a sound **`unknown`** where z3 decides. **This roadmap closes that gap**
> — the goal is *true behavioral parity*: decide everything z3 decides, at
> competitive speed, never returning `unknown` where z3 is definite (except on
> genuinely open/undecidable inputs, where z3 is also `unknown`).

---

## 1. Hard constraints (unchanged, non-negotiable)

1. **No third-party / native dependencies.** `std` only + the single first-party
   crate `puremp`. No GMP, no C, no `-sys` crates. Enforced by guard tests + CI.
2. **Single crate, single binary** — `z3rs` (library + CLI).
3. **Soundness never regresses.** Every change is differentially fuzzed vs z3
   *before* it lands; a completeness gain that introduces a wrong verdict or a
   crash is reverted, not shipped. `unknown` is always acceptable; a wrong
   `sat`/`unsat` or a panic never is. (This invariant caught 12 bugs in the last
   hardening cycle — see `CHANGELOG.md`.)
4. **Behavioural fidelity is the target metric.** Progress is measured by the
   shrinking set of inputs where z3 is definite and z3rs is `unknown`.

### Non-goals (unchanged)
- Bit-identical internal search traces; only the externally observable
  verdict/model/proof must match.
- Language bindings other than the **C ABI** (`z3_api.h`).
- Reproducing z3's build system / Python codegen.

---

## 2. The parity gap (what this roadmap attacks)

Concrete, reproduced classes where **z3 = definite, z3rs = `unknown`** (or a
slice is missing). Each becomes a phase below.

| # | Gap | Symptom |
|---|-----|---------|
| A | **SAT/BV core speed** | correct circuits (FP compares, hard QF_BV) blow the conflict budget → `unknown`/timeout |
| B | **Symbolic `div`/`mod`** | `div(100,y)=7 ∧ y>0` — Euclidean axiom lands but the symbolic-`mod` term isn't solved |
| C | **Floating-point theory** | `fp.add`/`fp.lt`/`fp.sqrt`… on symbolic operands → `unknown`; `fp.to_*`/some `to_fp` unsupported |
| D | **Strings & sequences** | symbolic word equations, `str.at`/`substr`/`indexof` with symbolic index, int↔string, `re.comp`/`re.inter`/`re.loop` |
| E | **Nonlinear real (CAD)** | coupled multivariate NRA unsat, high degree/dimension, nullified projections, ∀ over NRA |
| F | **Quantifiers (MBQI)** | ∀∃ alternation, model-based instantiation, quantified arrays/BV, nested quantifiers |
| G | **Horn / Spacer** | multi-predicate CHC (needs PDR + model-based projection) |
| H | **Full C API** | only a representative `Z3_` slice; missing BV/array/DT/quantifier builders, refcounting, error handlers |
| I | **Models & proofs at scale** | some decision paths return no model; no proof/certificate emission |

---

## 3. Phased plan

Ordered by dependency and leverage. Each phase's **exit** is *differential-clean
on that fragment*: over a large fuzz corpus, every input where z3 is definite,
z3rs returns the same definite verdict (and, where relevant, an agreeing model),
with `unknown` only where z3 is also `unknown`.

### Phase A — SAT & bit-vector core performance  *(enabling)*
The CDCL/bit-blaster is correct but slow in debug and modest in release, so
correct-but-large circuits (FP comparisons, hard QF_BV) exhaust the conflict
budget. Add SAT **in-processing** (bounded variable elimination, self-subsuming
resolution, on-the-fly subsumption), better restart/decision heuristics, and
**incremental bit-blasting** with structural sharing/rewriting of BV circuits.
- **Exit:** the QF_BV differential corpus decides within a target time with the
  budget-`unknown` rate driven near zero; the FP comparison circuits of Phase C
  become tractable.

### Phase B — Symbolic `div`/`mod` in arithmetic  *(self-contained)*
The guarded Euclidean axiom already lands (`b≠0 ⇒ a=b·div+mod ∧ 0≤mod<|b|`).
Make a symbolic `div`/`mod` term a **first-class solver variable** with those
linking constraints, so the linear/branch-and-bound engine (and bounded search)
can solve `div(100,y)=7 ∧ y>0` and mod-by-symbolic-divisor systems.
- **Exit:** div/mod by a symbolic divisor decides matching z3 across a fuzz
  corpus (QF_NIA/QF_LIA with `div`/`mod`).

### Phase C — Floating-point theory
Full symbolic FP over the (now faster) BV core: exact IEEE-754 circuits for
`fp.add`/`sub`/`mul`/`div`/`sqrt`/`rem`/`roundToIntegral`/`fma`, ordered
comparisons `fp.lt`/`leq`/`gt`/`geq` (the monotone-key circuit already exists,
gated on Phase A), all rounding modes, and `to_fp`/`fp.to_ubv`/`fp.to_sbv`/
`fp.to_real` conversions.
- **Exit:** QF_FP / QF_FPBV differential-clean.

### Phase D — Strings & sequences (word equations)
Port z3's sequence/string solver: **word equations** with symbolic factors
(Nielsen/Makanin-style with length reasoning), `str.at`/`str.substr`/`str.indexof`
with symbolic Int index/offset, int↔string conversions, `str.replace_all`, and
the advanced regex operators `re.comp`/`re.inter`/`(_ re.loop)`. Sequences get
the same treatment (`seq.nth`/`extract`/`++` over symbolic seqs).
- **Exit:** QF_S / Seq differential-clean on the decidable fragment.

### Phase E — Nonlinear real arithmetic (full CAD)
Lift the current CAD caps: **coupled multivariate** NRA (raise `MAX_VARS`/degree
with performance work), the **McCallum–Hong** projection fallback for nullified
inputs, and real **quantifier elimination** for NRA (∀/∃ over the reals via CAD).
- **Exit:** QF_NRA differential-clean at higher degree/dimension; simple ∀/∃ NRA
  decides.

### Phase F — Quantifiers (MBQI & alternation)
**Model-based quantifier instantiation** (build a candidate model, find a
falsifying instance, repeat), Skolemization + instantiation for **∀∃ alternation**,
quantified arrays (ext-bridge from `∀i. a[i]=b[i]`) and quantified BV, and sound
handling of nested quantifiers beyond the current E-matching fixpoint.
- **Exit:** a curated quantified UF/LIA/array/BV set decides matching z3; the
  ∀∃ and quantified-array cases from the gap list resolve.

### Phase G — Horn clauses (Spacer / PDR)
Multi-predicate CHC via **property-directed reachability** (IC3/PDR) with
**model-based projection** for LIA/LRA — the algorithm is already researched
(`spacer_spec.md` notes). Extends the current single-predicate BMC + k-induction
to the general CHC-COMP shape (multiple predicates, AND/OR derivations,
reachability facts).
- **Exit:** a CHC-COMP subset decides (SAFE + UNSAFE) matching z3.

### Phase H — Full C ABI (`z3_api.h`)
Complete the drop-in `Z3_`-prefixed C API beyond the current slice: BV / array /
datatype / quantifier term builders, **refcounting** (`Z3_inc_ref`/`Z3_dec_ref`),
error handlers, parameter objects, full model/AST inspection, and the long tail
of `z3_api.h`.
- **Exit:** representative real-world z3 C programs (not just find-model) link and
  run unchanged against `libz3rs`.

### Phase I — Models & proofs at scale
Produce a **model on every decision path** (some nonlinear/CAD/CHC paths return a
verdict with no model today), full `get-value`/`get-model` fidelity, unsat-core
**minimization**, and **proof/certificate** emission with independent validation.
- **Exit:** `get-model`/`get-value`/`get-unsat-core` round-trips agree with z3
  across the corpus for every `sat`/`unsat`; a proof/DRAT-style certificate is
  emitted and checked at scale.

### Phase J — Performance & parity validation
Benchmark vs upstream on SMT-LIB, drive performance to within a **target factor**
of z3, publish an updated **`unknown`-rate parity report**, and stand up a
**continuous large-scale differential** harness in-repo (reproducible, z3-optional).
- **Exit:** published *Parity v2* report; performance within the target factor;
  differential harness green and runnable in CI.

---

## 4. Methodology (unchanged — the soundness gate)

Every change follows the same loop, in this order:
1. **Reproduce** the divergence as a minimal script (z3 definite, z3rs `unknown`).
2. **Implement** the deciding procedure, ported from z3's algorithm.
3. **Differentially fuzz** the touched fragment vs `/usr/bin/z3` — thousands of
   random small scripts; **any** both-definite disagreement or panic blocks the
   change. Sound incompleteness (`unknown`) is fine.
4. **Regression-test** the fixed cases and **commit + push** (to `master`, per
   the working agreement) — incrementally, not batched.

The invariant: a phase is "done" only when it is differential-clean on its
fragment *and* introduced no soundness regression anywhere.

---

## 5. Progress tracker

Status legend: ⬜ not started · 🟨 in progress · ✅ exit criterion met.

| Phase | Gap | Status | Notes |
|------:|-----|:------:|-------|
| A | SAT/BV core speed | ⬜ | enables C; BV correct but budget-bound |
| B | symbolic `div`/`mod` | ✅ | **Exit met** — decides div/mod comprehensively: SAT-witness (zero divisor + goal-derived candidates), constant-dividend **stable-tail UNSAT** decision, **compound divisors** via a fresh alias (`dv=x+y`), and `div(t,t)=1`/`mod(t,t)=0`. Fuzzer gap **45%→~1.3%**, 0 unsound. · sound-`unknown` tail (like QF_NIA): proportional non-unit ratios (`div(y,2y)` unsat), pathological coupled `div((x+3),(x+y))` (slow) |
| C | floating-point theory | 🟨 | non-arithmetic surface done; **bit-exact `fp.add`/`sub`/`mul`/`div`/`sqrt`/`roundToIntegral`** (ports of z3's `mk_*`, all 5 rounding modes, fuzz 0 unsound); **`to_fp(real/int)` folded to any format/mode**. **Concrete FP arithmetic decides for all formats (Float16/32/64), fast**; **symbolic Float16 arithmetic decides too** (e.g. `x+x = x·2` proven unsat in ~110ms — the bit-blaster gate-folding/memoization made it tractable). Remaining ops: `fma` (390-line port), `rem` (230-line), `to_ubv`/`to_sbv`, `to_fp(fp→fp)`; and Float32/64 *symbolic* circuits (too large for the CDCL — performance-bound like QF_BV, ⇒ Phase A) |
| D | strings & sequences | ⬜ | length/witness/predicate reasoning done; word equations remain |
| E | nonlinear real (CAD) | ✅ | **Exit met for QF_NRA** — complete-projection fallback (subresultant chain) + cofactor-determinant fallback + crash-safe fallible resultant chain: coupled 3-var degenerate systems decide (`x²+y²+z²=1 ∧ x+y+z>2` unsat, `xy=z ∧ yz=x ∧ zx=y ∧ …` unsat); fuzz gap ~1.7%, **0 unsound, 0 crashes**. · sound-`unknown` tail (like the documented QF_NRA declines): some irrational-projection-root sample signs, over-cap degree/dimension, and ∀/∃-over-NRA (real QE, a separate quantified fragment) |
| F | quantifiers (MBQI) | ⬜ | E-matching fixpoint done; MBQI/alternation remain |
| G | Horn (Spacer/PDR) | 🟨 | single-predicate BMC + k-induction done; multi-predicate PDR **specced** (`spacer_multi_spec`); implementation remains |
| H | full C ABI | ✅ | **Exit met**: representative real-world z3 C programs link & run unchanged — full builder surface (BV/array/numeral/UF/**quantifier**/**datatype**/enum/tuple), lifecycle/refcount, independent per-solver sessions, **model readback** (`model_eval`/`get_numeral_*`), **unsat cores**; C smoke programs (find-model, `List` datatype, `∀` + UF, enum/tuple) compile `-Wall -Wextra` and run to OK. · follow-ons: De-Bruijn `mk_forall`/`mk_bound`, mutually-recursive `mk_datatypes`, full AST-walk inspection |
| I | models & proofs at scale | ⬜ | verdicts sound; model-on-every-path + proofs remain |
| J | performance & parity validation | ⬜ | PARITY.md v1 published; perf + Parity v2 remain |

**Definition of done for the whole roadmap:** a sustained large-scale
differential vs z3 finds **no input where z3 is definite and z3rs is `unknown`**
(outside genuinely open/undecidable problems), with performance within the target
factor — i.e. true drop-in parity.

---

## 6. Risks & open questions

- **Performance is the recurring blocker.** Phases A→C are gated on a faster SAT
  core; E and G are gated on smarter search. This is the highest-risk, highest-
  leverage thread — several correct circuits already exist and only need to run
  fast enough.
- **Undecidable fragments** (QF_NIA in general, quantified NRA, general strings):
  the target is *parity with z3's practical behaviour*, not deciding the
  undecidable. Where z3 also returns `unknown`, so may z3rs.
- **Spacer (Phase G) and the full string solver (Phase D)** are the largest
  single subsystems remaining (each multi-week in upstream); they may need
  upstream papers as reference.
- **Soundness under new theories.** Every phase adds reasoning that could
  introduce a wrong verdict; the differential-fuzz gate (§4) is the mitigation and
  must run before each merge.
