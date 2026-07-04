# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.5](https://github.com/KarpelesLab/z3rs/compare/v0.0.4...v0.0.5) - 2026-07-04

### Other

- Fix unsound SAT: opaque exponentiation was not gated as nonlinear
- Phase 6: accept the (Set T) sort as (Array T Bool)
- Phase 6: pseudo-boolean cardinality (_ at-least / _ at-most
- Fix unsound bv2int elimination on compound arguments
- Reject bit-vector width mismatch in equality (robustness)
- Phase 6: decide bv2int when the bit-vector is used only via bv2int
- Phase 5: string-predicate reflexivity on identical arguments
- Phase 5: symbolic seq.len as a non-negative Int function
- Fix unsound SAT: symbolic str.len could be negative

## [0.0.4](https://github.com/KarpelesLab/z3rs/compare/v0.0.3...v0.0.4) - 2026-07-04

### Other

- Bump puremp to 0.2.0
- Accept negative numeric literals (z3 compatibility)
- Phase 5: recover implied equalities from opposing inequalities
- Phase 5: dark shadow eliminates equalities first (+ budget isolation)

## [0.0.3](https://github.com/KarpelesLab/z3rs/compare/v0.0.2...v0.0.3) - 2026-07-04

### Other

- Update ROADMAP: Omega-test progress in Phase 5
- Phase 5: Omega-test dark shadow (verified SAT witness)
- Phase 5: Fourier–Motzkin integer-unsat fallback (Omega real shadow)
- Phase 5: Omega-test GCD tightening of integer inequalities
- Phase 3: honor tactics in (apply …) — nnf + combinators
- Fix unsound SAT: datatype universal with a non-matching selector trigger
- Phase 6: get-assertions, arity-N uninterpreted sorts, version fix
- Phase 2 ✅: enrich the theory rewriter; mark rewriter phase done
- Phase 4 ✅: SAT phase functional criterion met (cores + sat_smt)
- Phase 0 ✅: complete the util foundation (params + rlimit)
- Phase 5: word-equation boundary-character mismatch
- Phase 3: minimal (apply simplify) tactic + get-value model surface
- Reject bit-vector operand-width mismatches (robustness)

## [0.0.2](https://github.com/KarpelesLab/z3rs/compare/v0.0.1...v0.0.2) - 2026-07-04

### Other

- Phase 5: regex power ((_ re.^ n))
- Phase 6: (_ as-array f) and check-sat-using
- Fix two soundness bugs in quantifier elimination (valid universals refuted)
- Phase 5: Diophantine systems via unit-variable elimination
- Phase 5: word equations for concat=concat via prefix/suffix cancellation
- Phase 5: generalize Diophantine witness to n variables
- Phase 5: verified integer witness for unbounded 2-var Diophantine (LIA)
- Phase 6: more get-info keys (:authors, :error-behavior, :reason-unknown)
- Phase 6: array map combinator ((_ map f))
- Phase 5: Euclidean div/mod linking axioms
- Phase 5: product-sign axioms (extend square-nonnegativity)
- Phase 5: square-nonnegativity axiom for nonlinear arithmetic
- Phase 4: bit-vector overflow predicates (bvuaddo/bvsaddo/bvumulo/…)
- Fix soundness bug: opaque FP ops must not bit-blast to a free BV
- Phase 7: exists-forall quantifier alternation (∃x.∀y.φ)
- Phase 6: flatten nested universal quantifiers
- Phase 5: sequence search/replace folds (indexof/contains/prefixof/replace)
- Phase 5: regex complement and difference (re.comp / re.diff)
- Phase 5: Int<->BV bridge for constant equalities (bv2int / int2bv)
- Phase 5: str.is_digit and fp.to_real (integral) folds
- Phase 5: regex bounded repetition ((_ re.loop n m))
- collect like terms in sums (arith_rewriter)
- Phase 6: declare-datatype (singular), (eval t), (simplify t)
- Update ROADMAP (lambda arrays)
- Phase 6: lambda-defined arrays (beta-reduction on select)
- Phase 6: define-const, (_ divisible n), and ^ (exponentiation)
- Update ROADMAP (parametric datatypes)
- Phase 6: parametric (polymorphic) datatypes
- Update ROADMAP (mutual datatypes + recursion over datatypes)
- Phase 6: fold datatype selectors/testers under instantiation
- Phase 6: mutually-recursive datatypes
- Update ROADMAP (multi-trigger E-matching)
- Phase 6: multi-trigger E-matching
- Update ROADMAP (E-matching / trigger-based instantiation)
- Phase 6: E-matching (trigger-based quantifier instantiation)
- Apply rustfmt to recursive-function test
- Update ROADMAP (recursive function definitions)
- Phase 6: recursive functions (define-fun-rec / define-funs-rec)
- Fix soundness bug: QE must not fire when a binder is under a UF
- Update ROADMAP (SAT: clause-DB reduction, assumptions, conflict budget)
- learnt-clause deletion (bounded clause DB) + activity
- Update ROADMAP (symbolic fp.eq + conflict-budgeted bit-blaster)
- Fix symbolic-FP test: declare y before use
- symbolic fp.eq via BV + bounded bit-blaster (sound termination)
- Update ROADMAP (symbolic FP bit-blasting)
- Phase 5: symbolic floating-point via bit-blasting (equality + classification)
- Phase 5: more string operations (str.< / replace_all / to_code / from_code)
- Update ROADMAP (word equations for concat vs literal)
- Bump puremp 0.1.4 -> 0.1.7
- Phase 5: word equations for string concatenation vs a literal
- Update ROADMAP (Phase 9: safe Rust API)
- Phase 9: safe idiomatic Rust API (api::Solver)
- Update ROADMAP (Phase 7: integer QE for unit-coefficient LIA)
- Phase 7 (qe): integer quantifier elimination (unit-coefficient LIA)
- Update ROADMAP (Phase 7: quantifier elimination for real LRA)
- Phase 7 (qe): quantifier elimination for real linear arithmetic
- Update ROADMAP (quantifier saturation: finite-domain sat + Datalog)
- complete (not just sound) sat when instantiation saturates
- Update ROADMAP (QF_FP Float64 fragment)
- Phase 5: floating-point (QF_FP) constant folding for Float64
- Update ROADMAP (Phase 7: strict-supremum epsilon reporting)
- Phase 7 (opt): strict-supremum optimization reporting (epsilon)
- Update ROADMAP (Phase 7: real-valued optimization)
- Phase 7 (opt): real-valued optimization via Fourier-Motzkin
- Update ROADMAP (sequence theory fragment)
- Phase 5: sequence theory (Seq) structural fragment
- Update ROADMAP (quantifier fixpoint instantiation)
- iterate instantiation to a fixpoint
- Phase 5: round out QF_BV — bvcomp, reductions, int/bv conversions
- Update ROADMAP (match expressions, define-sort)
- Phase 8: define-sort (sort macros / aliases)
- Phase 6: datatype match expressions (SMT-LIB 2.6 match)
- Format regex test
- Update ROADMAP (Phase 5: regex membership in string theory)
- Phase 5: regular expressions for the string theory (str.in_re)
- Update ROADMAP (Phase 9: incremental C session API)
- Phase 9: incremental solver session in the C API
- Update ROADMAP (Phase 5: string/sequence fragment)
- Phase 5: string theory — sound constant-folding + length fragment
- Update ROADMAP (Phase 9: C ABI eval entry point)
- Phase 9: C ABI — z3rs_eval_smtlib2_string
- Update ROADMAP (Phase 7: assert-soft/MaxSAT)
- Phase 7 (opt): assert-soft / weighted MaxSAT
- Update ROADMAP (Phase 7 opt: integer optimization)
- Phase 7 (opt): integer optimization — maximize/minimize/get-objectives
- Phase 5/6: recursive datatypes with acyclicity (occurs-check)
- Format test additions
- Update ROADMAP (non-recursive datatypes: records + variants)
- Phase 5/6: multi-constructor (non-recursive) datatypes
- Phase 5/6: record/tuple datatypes (single constructor with fields)
- Update ROADMAP (quantifier instantiation + skolemization)
- Quantifiers stage 2: instantiation and skolemization
- Enum models: get-value prints the constructor name
- Update ROADMAP (enum datatypes, BV models, quantifier acceptance)
- Phase 5/6: enumeration datatypes (declare-datatypes)
- Phase 6: QF_BV models — get-value/get-model for bit-vectors
- Update ROADMAP (full QF_BV operator set + quantifier acceptance)
- accept forall/exists with a sound unknown (stage 1)
- Phase 5/6: QF_BV div/rem family + bit-blaster ite/implies/xor
- Phase 5/6: QF_BV bvnand/bvnor/bvxnor, rotate_left/right, repeat, bvashr
- Fix QF_LIRA division-by-constant; gate Bool-indexed arrays (soundness)
