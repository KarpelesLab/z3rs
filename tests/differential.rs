//! Differential testing against upstream Z3 (the reference oracle, per
//! `ROADMAP.md` §7). Each script's `(check-sat)` verdicts from z3rs's
//! [`run_smt2`] are compared to those of the `z3` binary. If `z3` is not on
//! `PATH` the whole suite is skipped, so it stays green on machines without it.
//!
//! The corpus is deliberately confined to the fragment z3rs decides today
//! (QF_UF / QF_LRA / QF_LIA with the supported operators); as coverage grows,
//! extend `CORPUS`.

use std::process::Command;

use z3rs::cmd_context::run_smt2;

/// A labelled SMT-LIB2 script.
struct Case {
    name: &'static str,
    script: &'static str,
}

const CORPUS: &[Case] = &[
    Case {
        name: "qf_uf_transitivity",
        script: "(declare-sort U 0)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (= a b))(assert (= b c))(assert (not (= a c)))(check-sat)",
    },
    Case {
        name: "qf_uf_congruence",
        script: "(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)(declare-const b U)
                 (assert (= a b))(assert (not (= (f a) (f b))))(check-sat)",
    },
    Case {
        name: "qf_uf_sat",
        script: "(declare-sort U 0)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (= a b))(assert (not (= a c)))(check-sat)",
    },
    Case {
        name: "bool_contradiction",
        script: "(declare-const p Bool)(assert (and p (not p)))(check-sat)",
    },
    Case {
        name: "bool_tautology_sat",
        script: "(declare-const p Bool)(assert (or p (not p)))(check-sat)",
    },
    Case {
        name: "qf_lra_bounds_unsat",
        script: "(declare-const x Real)(declare-const y Real)
                 (assert (>= x 1))(assert (>= y 1))(assert (<= (+ x y) 1))(check-sat)",
    },
    Case {
        name: "qf_lra_bounds_sat",
        script: "(declare-const x Real)(assert (>= x 3))(assert (<= x 5))(check-sat)",
    },
    Case {
        name: "qf_lra_strict_cycle",
        script: "(declare-const x Real)(declare-const y Real)
                 (assert (< x y))(assert (< y x))(check-sat)",
    },
    Case {
        name: "qf_lia_integrality_unsat",
        script: "(declare-const x Int)(assert (< 3 x))(assert (< x 4))(check-sat)",
    },
    Case {
        name: "qf_lia_divisibility_sat",
        script: "(declare-const x Int)(assert (<= 3 (* 2 x)))(assert (<= (* 2 x) 5))(check-sat)",
    },
    Case {
        name: "qf_lia_bounds_sat",
        script: "(declare-const x Int)(assert (<= 3 x))(assert (<= x 5))(check-sat)",
    },
    Case {
        name: "uf_int_congruence_unsat",
        script: "(declare-fun f (Int) Int)(declare-const x Int)(declare-const y Int)
                 (assert (= x y))(assert (not (= (f x) (f y))))(check-sat)",
    },
    Case {
        name: "disequality_pin_unsat",
        script: "(declare-const x Int)(assert (<= x 5))(assert (>= x 5))(assert (not (= x 5)))(check-sat)",
    },
    Case {
        name: "ite_arith_sat",
        script: "(declare-const x Int)(assert (= x (ite (< x 0) 1 2)))(check-sat)",
    },
    Case {
        name: "let_nested_sat",
        script: "(declare-const p Bool)(declare-const q Bool)
                 (assert (let ((x p)) (let ((x q)) (or x (not x)))))(check-sat)",
    },
    Case {
        name: "define_fun_unsat",
        script: "(declare-const x Int)(define-fun bound () Int 10)(define-fun below ((a Int)(b Int)) Bool (< a b))
                 (assert (below x bound))(assert (>= x 10))(check-sat)",
    },
    Case {
        name: "distinct_uf_unsat",
        script: "(declare-sort U 0)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (distinct a b c))(assert (= a b))(check-sat)",
    },
    Case {
        name: "distinct_bool_pigeonhole",
        script: "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)(assert (distinct a b c))(check-sat)",
    },
    Case {
        name: "distinct_int_sat",
        script: "(declare-const a Int)(declare-const b Int)(declare-const c Int)
                 (assert (distinct a b c))(assert (<= 0 a))(assert (<= a 2))(assert (<= 0 b))(assert (<= b 2))
                 (assert (<= 0 c))(assert (<= c 2))(check-sat)",
    },
    Case {
        name: "real_division_sat",
        script: "(declare-const x Real)(assert (= x (/ 1 3)))(assert (= (* 3 x) 1))(check-sat)",
    },
    Case {
        name: "implies_modus_ponens",
        script: "(declare-const p Bool)(declare-const q Bool)(assert (=> p q))(assert p)(assert (not q))(check-sat)",
    },
    Case {
        name: "xor_unsat",
        script: "(declare-const p Bool)(declare-const q Bool)(assert (xor p q))(assert (= p q))(check-sat)",
    },
    Case {
        name: "chained_lt_unsat",
        script: "(declare-const x Int)(declare-const y Int)(declare-const z Int)
                 (assert (< x y z))(assert (< z x))(check-sat)",
    },
    Case {
        name: "int_div_mod_fold",
        script: "(assert (not (= (div 7 3) 2)))(check-sat)",
    },
    Case {
        name: "mod_negative",
        script: "(assert (not (= (mod (- 7) 3) 2)))(check-sat)",
    },
    Case {
        name: "abs_constant",
        script: "(declare-const x Int)(assert (= x (abs (- 5))))(assert (not (= x 5)))(check-sat)",
    },
    Case {
        name: "to_real_value",
        script: "(declare-const x Int)(declare-const y Real)
                 (assert (= y (to_real x)))(assert (= x 3))(assert (not (= y 3.0)))(check-sat)",
    },
    Case {
        name: "minus_nary_fold",
        script: "(declare-const x Int)(assert (= (- 10 1 2 3) x))(assert (not (= x 4)))(check-sat)",
    },
    Case {
        name: "term_ite_unsat",
        script: "(declare-const b Bool)(declare-const x Int)
                 (assert (= x (ite b 1 2)))(assert b)(assert (not (= x 1)))(check-sat)",
    },
    Case {
        name: "term_ite_selfref_sat",
        script: "(declare-const x Int)(assert (= x (ite (< x 0) 1 2)))(check-sat)",
    },
    Case {
        name: "nested_term_ite_unsat",
        script: "(declare-const x Int)(assert (> (+ (ite (> x 0) x 0) 1) 100))(assert (< x 50))(check-sat)",
    },
    Case {
        name: "parity_equation_unsat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* 2 x) (+ (* 2 y) 1)))(check-sat)",
    },
    Case {
        name: "divisibility_unsat",
        script: "(declare-const x Int)(assert (= (* 3 x) 7))(check-sat)",
    },
    Case {
        name: "nelson_oppen_lia_unsat",
        script: "(declare-sort S 0)(declare-fun f (Int) S)(declare-const a S)
                 (declare-const x Int)(declare-const y Int)
                 (assert (<= x y))(assert (<= y x))(assert (= (f x) a))(assert (not (= (f y) a)))(check-sat)",
    },
    Case {
        name: "nelson_oppen_lra_unsat",
        script: "(declare-fun f (Real) Real)(declare-const x Real)(declare-const y Real)
                 (assert (<= x y))(assert (<= y x))(assert (not (= (f x) (f y))))(check-sat)",
    },
    Case {
        name: "nelson_oppen_sat",
        script: "(declare-sort S 0)(declare-fun f (Int) S)(declare-const a S)
                 (declare-const x Int)(declare-const y Int)
                 (assert (<= x y))(assert (= (f x) a))(assert (not (= (f y) a)))(check-sat)",
    },
    Case {
        name: "nelson_oppen_euf_to_arith_unsat",
        script: "(declare-sort S 0)(declare-fun f (S) Int)(declare-const a S)(declare-const b S)
                 (declare-const x Int)(declare-const y Int)
                 (assert (= a b))(assert (= (f a) x))(assert (= (f b) y))(assert (> x y))(check-sat)",
    },
    Case {
        name: "nary_xor",
        script: "(assert (xor true true true))(check-sat)",
    },
    Case {
        name: "nary_xor_vars",
        script: "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)
                 (assert (xor a b c))(assert (= a b))(assert c)(check-sat)",
    },
    Case {
        name: "congruence_int_fn_to_arith",
        script: "(declare-sort U 0)(declare-fun f (U) Int)(declare-const a U)(declare-const b U)
                 (assert (= a b))(assert (> (f a) (f b)))(check-sat)",
    },
    Case {
        name: "arith_eq_to_uf_compound",
        script: "(declare-fun f (Int) Int)(declare-const x Int)(declare-const y Int)
                 (assert (= (+ x y) 0))(assert (= x 0))(assert (distinct (f x) (f (- y))))(check-sat)",
    },
    Case {
        name: "lia_strict_between_unsat",
        script: "(declare-const x Int)(declare-const y Int)(assert (< x y))(assert (< y (+ x 1)))(check-sat)",
    },
    Case {
        name: "predicate_congruence_unsat",
        script: "(declare-sort U 0)(declare-fun p (U) Bool)(declare-const a U)(declare-const b U)
                 (assert (= a b))(assert (p a))(assert (not (p b)))(check-sat)",
    },
    Case {
        name: "predicate_congruence_2ary_unsat",
        script: "(declare-sort U 0)(declare-fun p (U U) Bool)(declare-const a U)(declare-const b U)(declare-const c U)
                 (assert (= a b))(assert (p a c))(assert (not (p b c)))(check-sat)",
    },
    Case {
        name: "predicate_no_congruence_sat",
        script: "(declare-sort U 0)(declare-fun p (U) Bool)(declare-const a U)(declare-const b U)
                 (assert (p a))(assert (not (p b)))(check-sat)",
    },
    Case {
        name: "to_int_symbolic_unsat",
        script: "(declare-const x Real)(assert (= x 3.7))(assert (>= (to_int x) 4))(check-sat)",
    },
    Case {
        name: "to_int_floor_unsat",
        script: "(declare-const x Real)(assert (<= 2.0 x))(assert (< x 3.0))(assert (not (= (to_int x) 2)))(check-sat)",
    },
    Case {
        name: "array_row_same_unsat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const v Int)
                 (assert (not (= (select (store a i v) i) v)))(check-sat)",
    },
    Case {
        name: "array_row_other_unsat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const j Int)(declare-const v Int)
                 (assert (not (= i j)))(assert (not (= (select (store a i v) j) (select a j))))(check-sat)",
    },
    Case {
        name: "array_congruence_unsat",
        script: "(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const i Int)
                 (assert (= (select a i) 1))(assert (= (select b i) 2))(assert (= a b))(check-sat)",
    },
    Case {
        name: "array_store_sat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const v Int)
                 (assert (= (select (store a i v) i) v))(check-sat)",
    },
    Case {
        name: "array_store_commute_unsat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const j Int)
                 (assert (not (= i j)))
                 (assert (not (= (store (store a i 1) j 2) (store (store a j 2) i 1))))(check-sat)",
    },
    Case {
        name: "array_extensionality_sat",
        script: "(declare-const a (Array Int Int))(declare-const b (Array Int Int))
                 (assert (not (= a b)))(assert (= (select a 0) (select b 0)))(check-sat)",
    },
    Case {
        name: "const_array_read_unsat",
        script: "(declare-const i Int)(assert (not (= (select ((as const (Array Int Int)) 7) i) 7)))(check-sat)",
    },
    Case {
        name: "const_array_store_unsat",
        script: "(declare-const i Int)
                 (assert (not (= (select (store ((as const (Array Int Int)) 0) i 5) (+ i 1)) 0)))(check-sat)",
    },
    Case {
        name: "array_uf_arith_combo_unsat",
        script: "(declare-const a (Array Int Int))(declare-fun f (Int) Int)(declare-const i Int)
                 (assert (= (select a i) (f i)))(assert (> (select a i) 5))(assert (< (f i) 3))(check-sat)",
    },
    Case {
        name: "nested_array_unsat",
        script: "(declare-const a (Array Int (Array Int Int)))(declare-const i Int)(declare-const j Int)
                 (assert (not (= (select (select (store a i (store (select a i) j 5)) i) j) 5)))(check-sat)",
    },
    Case {
        name: "array_ite_unsat",
        script: "(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const c Bool)(declare-const i Int)
                 (assert (= (select (ite c a b) i) 9))(assert c)(assert (not (= (select a i) 9)))(check-sat)",
    },
    Case {
        name: "array_index_arith_unsat",
        script: "(declare-const a (Array Int Int))(declare-const i Int)(declare-const j Int)
                 (assert (= i (+ j 1)))(assert (= (select a i) 1))(assert (not (= (select a (+ j 1)) 1)))(check-sat)",
    },
    Case {
        name: "bv_add_wrap_unsat",
        script: "(declare-const x (_ BitVec 8))(assert (= x #xff))(assert (not (= (bvadd x #x01) #x00)))(check-sat)",
    },
    Case {
        name: "bv_ult_strict_unsat",
        script: "(declare-const x (_ BitVec 8))(assert (bvult x x))(check-sat)",
    },
    Case {
        name: "bv_solve_sat",
        script: "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))
                 (assert (= (bvadd x y) #x0a))(assert (bvult x #x05))(check-sat)",
    },
    Case {
        name: "bv_bitwise_unsat",
        script: "(declare-const x (_ BitVec 4))(assert (not (= (bvand x #b0000) #b0000)))(check-sat)",
    },
    Case {
        name: "bv_concat_extract_identity",
        script: "(declare-const x (_ BitVec 8))
                 (assert (not (= (concat ((_ extract 7 4) x) ((_ extract 3 0) x)) x)))(check-sat)",
    },
    Case {
        name: "bv_concat_literal",
        script: "(assert (not (= (concat #x0f #xf0) #x0ff0)))(check-sat)",
    },
    Case {
        name: "bv_mul_commutes",
        script: "(declare-const x (_ BitVec 4))(declare-const y (_ BitVec 4))
                 (assert (not (= (bvmul x y) (bvmul y x))))(check-sat)",
    },
    Case {
        name: "bv_mul_solve",
        script: "(declare-const x (_ BitVec 8))(assert (= (bvmul x #x03) #x0f))(assert (not (= x #x05)))(check-sat)",
    },
    Case {
        name: "bv_signed_vs_unsigned",
        // 0 <s 0xff is false (0xff = -1) but 0 <u 0xff is true.
        script: "(declare-const x (_ BitVec 8))(assert (= x #xff))(assert (bvslt #x00 x))(check-sat)",
    },
    Case {
        name: "bv_sgt_neg",
        script: "(assert (not (bvsgt #x01 #xff)))(check-sat)",
    },
    Case {
        name: "bv_zero_extend",
        script: "(declare-const x (_ BitVec 4))(assert (= x #xf))(assert (not (= ((_ zero_extend 4) x) #x0f)))(check-sat)",
    },
    Case {
        name: "bv_sign_extend_neg",
        script: "(declare-const x (_ BitVec 4))(assert (= x #xf))(assert (not (= ((_ sign_extend 4) x) #xff)))(check-sat)",
    },
    Case {
        name: "bv_shl_is_mul2",
        script: "(declare-const x (_ BitVec 8))(assert (not (= (bvshl x #x01) (bvmul x #x02))))(check-sat)",
    },
    Case {
        name: "bv_shl_variable",
        script: "(declare-const x (_ BitVec 8))(assert (= (bvshl #x01 x) #x10))(assert (not (= x #x04)))(check-sat)",
    },
    Case {
        name: "bv_lshr",
        script: "(assert (not (= (bvlshr #x80 #x03) #x10)))(check-sat)",
    },
    Case {
        name: "real_div_by_constant",
        script: "(declare-const x Real)(assert (= (/ x 2) 3))(assert (not (= x 6)))(check-sat)",
    },
    Case {
        name: "lira_div_by_one",
        script: "(declare-const x Int)(assert (>= (/ x 1) 5))(assert (< x 5))(check-sat)",
    },
    Case {
        name: "bv_nand_xnor",
        script: "(declare-const x (_ BitVec 4))(assert (not (= (bvnand x x) (bvnot x))))(check-sat)",
    },
    Case {
        name: "bv_rotate",
        script: "(assert (not (= ((_ rotate_left 1) #x80) #x01)))(check-sat)",
    },
    Case {
        name: "bv_repeat",
        script: "(assert (not (= ((_ repeat 3) #b10) #b101010)))(check-sat)",
    },
    Case {
        name: "bv_ashr_sign",
        script: "(assert (not (= (bvashr #x80 #x01) #xc0)))(check-sat)",
    },
    Case {
        name: "bv_udiv_urem",
        script: "(assert (not (and (= (bvudiv #x0f #x04) #x03) (= (bvurem #x0f #x04) #x03))))(check-sat)",
    },
    Case {
        name: "bv_udiv_by_zero",
        script: "(assert (not (= (bvudiv #x0a #x00) #xff)))(check-sat)",
    },
    Case {
        name: "bv_sdiv_negative",
        script: "(assert (not (= (bvsdiv #xf8 #x02) #xfc)))(check-sat)",
    },
    Case {
        name: "bv_smod_signs",
        script: "(assert (not (= (bvsmod #xf9 #x02) #x01)))(check-sat)",
    },
    Case {
        name: "bv_ite_and_implies",
        script: "(declare-const c Bool)(assert c)(assert (=> c (not (= (ite c #x01 #x02) #x01))))(check-sat)",
    },
    // --- datatypes (QF_DT) --------------------------------------------------
    Case {
        name: "dt_enum_exclusion_sat",
        script: "(declare-datatypes ((Color 0)) (((red)(green)(blue))))(declare-const c Color)
                 (assert (not (= c red)))(assert (not (= c green)))(check-sat)",
    },
    Case {
        name: "dt_enum_all_excluded_unsat",
        script: "(declare-datatypes ((Color 0)) (((red)(green)(blue))))(declare-const c Color)
                 (assert (not (= c red)))(assert (not (= c green)))(assert (not (= c blue)))(check-sat)",
    },
    Case {
        name: "dt_record_selector_unsat",
        script: "(declare-datatypes ((P 0)) (((mk (fst Int)(snd Int)))))(declare-const p P)
                 (assert (= p (mk 3 4)))(assert (not (= (fst p) 3)))(check-sat)",
    },
    Case {
        name: "dt_list_recursive_unsat",
        script: "(declare-datatype Lst ((nil)(cons (hd Int)(tl Lst))))(declare-const l Lst)
                 (assert (= l (cons 5 nil)))(assert (not (= (hd l) 5)))(check-sat)",
    },
    Case {
        name: "dt_tester_sat",
        script: "(declare-datatype Lst ((nil)(cons (hd Int)(tl Lst))))(declare-const l Lst)
                 (assert ((_ is cons) l))(check-sat)",
    },
    // --- quantifiers (UF / LIA) --------------------------------------------
    Case {
        name: "forall_instantiation_unsat",
        script: "(declare-fun p (Int) Bool)(assert (forall ((x Int)) (=> (p x) (p (+ x 1)))))
                 (assert (p 0))(assert (not (p 3)))(check-sat)",
    },
    Case {
        name: "forall_uf_congruence_unsat",
        script: "(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)
                 (assert (forall ((x U)) (= (f x) a)))(declare-const b U)(assert (not (= (f b) a)))(check-sat)",
    },
    Case {
        name: "exists_witness_sat",
        script: "(declare-const y Int)(assert (exists ((x Int)) (= (* 2 x) y)))(assert (= y 8))(check-sat)",
    },
    // --- floating point (QF_FP), concrete Float64 ---------------------------
    Case {
        name: "fp_add_fold_unsat",
        script: "(assert (not (= (fp.add roundNearestTiesToEven (fp #b0 #b10000000000 #x0000000000000)
                 (fp #b0 #b10000000000 #x0000000000000)) (fp #b0 #b10000000001 #x0000000000000))))(check-sat)",
    },
    Case {
        name: "fp_nan_not_equal_sat",
        script: "(declare-const x Float64)(assert (fp.isNaN x))(check-sat)",
    },
    // --- responses: get-value / get-model / get-unsat-core ------------------
    Case {
        name: "get_value_int",
        script: "(declare-const x Int)(assert (= x 7))(check-sat)(get-value (x))",
    },
    Case {
        name: "get_value_bv",
        script: "(declare-const b (_ BitVec 8))(assert (= (bvadd b #x01) #x10))(check-sat)(get-value (b))",
    },
    Case {
        name: "get_value_enum",
        script: "(declare-datatypes ((Color 0)) (((red)(green)(blue))))(declare-const c Color)
                 (assert (not (= c red)))(assert (not (= c green)))(check-sat)(get-value (c))",
    },
    Case {
        name: "get_unsat_core_named",
        script: "(set-option :produce-unsat-cores true)(declare-const x Int)
                 (assert (! (> x 0) :named a))(assert (! (< x 0) :named b))(check-sat)(get-unsat-core)",
    },
    // --- incremental push/pop (multiple verdicts) ---------------------------
    Case {
        name: "push_pop_sequence",
        script: "(declare-const p Bool)(declare-const q Bool)(assert (=> p q))
                 (check-sat)(push 1)(assert p)(assert (not q))(check-sat)(pop 1)(check-sat)",
    },
    Case {
        name: "check_sat_assuming",
        script: "(declare-const p Bool)(declare-const q Bool)(assert (=> p q))
                 (check-sat-assuming (p (not q)))(check-sat-assuming (p))",
    },
    // --- nonlinear refutation (interval constraint propagation) --------------
    // z3rs answers these via ICP (sound `unsat`); satisfiable nonlinear cases
    // stay `unknown` (sound), which the harness accepts.
    Case {
        name: "nl_square_negative_unsat",
        script: "(declare-const x Real)(assert (< (* x x) 0))(check-sat)",
    },
    Case {
        name: "nl_bound_vs_square_unsat",
        script: "(declare-const x Real)(assert (> x 2))(assert (< (* x x) 4))(check-sat)",
    },
    Case {
        name: "nl_sum_of_squares_unsat",
        script: "(declare-const x Real)(declare-const y Real)
                 (assert (< (+ (* x x) (* y y)) 1))(assert (> x 2))(check-sat)",
    },
    Case {
        name: "nl_product_bound_unsat",
        script: "(declare-const x Real)(assert (>= x 3))(assert (<= x 5))
                 (assert (> (* x x) 30))(check-sat)",
    },
    Case {
        name: "nl_satisfiable_stays_sound",
        script: "(declare-const x Real)(assert (= (* x x) 4))(assert (> x 0))(check-sat)",
    },
    // --- nonlinear now decided (linearization + univariate CAD / int roots) --
    Case {
        name: "nl_fixed_var_linearizes_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= x 2))(check-sat)",
    },
    Case {
        name: "nl_int_square_positive_sat",
        script: "(declare-const x Int)(assert (= (* x x) 9))(assert (> x 0))(check-sat)",
    },
    Case {
        name: "nl_int_square_nonsquare_unsat",
        script: "(declare-const x Int)(assert (= (* x x) 2))(check-sat)",
    },
    Case {
        name: "nl_int_bounded_square_sat",
        script: "(declare-const x Int)(assert (and (>= x 1)(<= x 5)(= (* x x) 16)))(check-sat)",
    },
    Case {
        name: "nl_real_square_irrational_sat",
        script: "(declare-const x Real)(assert (= (* x x) 2))(check-sat)",
    },
    Case {
        name: "nl_real_square_eq_positive_sat",
        script: "(declare-const x Real)(assert (= (* x x) 4))(assert (> x 0))(check-sat)",
    },
    Case {
        name: "nl_two_var_fixed_reduces_univariate_sat",
        script: "(declare-const x Int)(declare-const y Int)
                 (assert (= (+ (* x x)(* y y)) 25))(assert (= x 3))(check-sat)",
    },
    Case {
        name: "nl_real_square_lt_sat",
        script: "(declare-const x Real)(assert (< (* x x) 4))(assert (> x 1))(check-sat)",
    },
    Case {
        name: "nl_cubic_root_forced_unsat",
        script: "(declare-const x Real)(assert (= (- (* x (* x x)) x) 0))(assert (> x 0))(assert (< x 1))(check-sat)",
    },
    // Generalized substitution: a variable defined by a linear expression is
    // substituted, reducing the product to a univariate polynomial.
    Case {
        name: "nl_subst_linear_expr_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= y (+ x 1)))(check-sat)",
    },
    Case {
        name: "nl_subst_linear_expr_two_roots_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= y (+ x 5)))(check-sat)",
    },
    Case {
        name: "nl_subst_real_quadratic_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) 2))(assert (= y (- 4 x)))(check-sat)",
    },
    // Bounded multivariate integer search (exhaustive over a finite box).
    Case {
        name: "nl_bounded_int_product_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 12))
                 (assert (and (>= x 1)(<= x 4)(>= y 1)(<= y 4)))(check-sat)",
    },
    Case {
        name: "nl_bounded_int_product_prime_unsat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 7))
                 (assert (and (>= x 1)(<= x 3)(>= y 1)(<= y 3)))(check-sat)",
    },
    Case {
        name: "nl_bounded_int_pythagorean_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (+ (* x x)(* y y)) 25))
                 (assert (and (>= x 0)(<= x 5)(>= y 0)(<= y 5)))(check-sat)",
    },
    // Linear-variable elimination reduces a polynomial system to univariate.
    Case {
        name: "nl_elim_system_int_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= (+ x y) 5))(check-sat)",
    },
    Case {
        name: "nl_elim_system_int_unsat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= (+ x y) 100))(check-sat)",
    },
    Case {
        name: "nl_elim_real_disc_negative_unsat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) 6))(assert (= (+ x y) 1))(check-sat)",
    },
    Case {
        name: "nl_elim_into_inequality_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (+ (* x x) y) 5))(assert (> y 0))(check-sat)",
    },
    // Fuzzer-found soundness regressions (all now fixed).
    Case {
        name: "nl_zero_constant_root_sat",
        script: "(declare-const x Int)(declare-const y Int)(assert (= (+ x y) 7))(assert (= (* x y) 0))(assert (> y 0))(check-sat)",
    },
    Case {
        name: "nl_mixed_int_real_drops_no_integrality_unsat",
        script: "(declare-const x Real)(declare-const y Int)(assert (= y (- x 6)))(assert (= (* x y) (- 4)))(check-sat)",
    },
    Case {
        name: "nl_mixed_nonunit_coeff_unsat",
        script: "(declare-const x Real)(declare-const y Int)(assert (= y (+ (* 2 x) 4)))(assert (= (* x y) (- 1)))(check-sat)",
    },
    // Multivariate sat proved by variable-fixing + univariate.
    Case {
        name: "nl_multivar_fixing_negatives_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (> (* x y) 5))(assert (< (+ x y) 3))(check-sat)",
    },
    Case {
        name: "nl_multivar_fixing_sign_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (> (* x y) 0))(assert (> x 0))(check-sat)",
    },
    // Full multivariate real CAD (project → base → lift → decide).
    Case {
        name: "cad_circle_hyperbola_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (< (+ (* x x)(* y y)) 4))(assert (> (* x y) 1))(check-sat)",
    },
    Case {
        name: "cad_two_equalities_ineq_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x x) 2))(assert (= (* y y) 3))(assert (< (+ x y) 0))(check-sat)",
    },
    Case {
        name: "cad_ineq_only_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (> (* x x) (* y y)))(assert (> y 10))(assert (< x 1))(check-sat)",
    },
    Case {
        name: "cad_curve_intersection_unsat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) 1))(assert (= (+ (* x x)(* y y)) 1))(check-sat)",
    },
    Case {
        name: "cad_curve_intersection_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) 1))(assert (= (+ (* x x)(* y y)) 4))(check-sat)",
    },
    // CAD fuzzer regressions: open cells under strict inequalities (the
    // between-sector sample must land in the interior, not on a section).
    Case {
        name: "cad_strict_open_cell_1_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) 2))(assert (< (* x x)(* y y)))(check-sat)",
    },
    Case {
        name: "cad_strict_open_cell_2_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) (- 1)))(assert (< (- x y)(- 2)))(assert (> (+ x y) 2))(check-sat)",
    },
    Case {
        name: "cad_strict_open_cell_3_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (= (* x y) 1))(assert (> (+ x y) 8))(assert (< (- x y)(- 1)))(check-sat)",
    },
    Case {
        name: "cad_strict_open_cell_4_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (not (>= (+ (* 2 (* x x))(* 5 (* y y))) 1)))(assert (< (- (* x (* x x)) x) 0))(check-sat)",
    },
    // Constrained Horn Clauses: single-predicate transition systems decided by
    // bounded model checking (unsat/counterexample) and k-induction (sat/invariant).
    Case {
        name: "chc_safe_nonneg_invariant",
        script: "(set-logic HORN)(declare-fun inv (Int) Bool)(assert (forall ((x Int)) (=> (= x 0) (inv x))))(assert (forall ((x Int)(y Int)) (=> (and (inv x)(= y (+ x 1))) (inv y))))(assert (forall ((x Int)) (=> (and (inv x)(< x 0)) false)))(check-sat)",
    },
    Case {
        name: "chc_unsafe_reaches_target",
        script: "(set-logic HORN)(declare-fun inv (Int) Bool)(assert (forall ((x Int)) (=> (= x 0) (inv x))))(assert (forall ((x Int)(y Int)) (=> (and (inv x)(= y (+ x 1))) (inv y))))(assert (forall ((x Int)) (=> (and (inv x)(= x 5)) false)))(check-sat)",
    },
    Case {
        name: "chc_unsafe_init_hits_bad",
        script: "(set-logic HORN)(declare-fun inv (Int) Bool)(assert (forall ((x Int)) (=> (= x 3) (inv x))))(assert (forall ((x Int)) (=> (and (inv x)(= x 3)) false)))(check-sat)",
    },
    // Square-bound interval narrowing refutes bounded-disc multivariate systems.
    Case {
        name: "nl_square_narrow_unsat",
        script: "(declare-const x Real)(declare-const y Real)(assert (< (+ (* x x)(* y y)) 1))(assert (> (* x y) 1))(check-sat)",
    },
    Case {
        name: "nl_square_narrow_unsat_2",
        script: "(declare-const x Real)(declare-const y Real)(assert (<= (+ (* x x)(* y y)) 2))(assert (> (* x y) 5))(check-sat)",
    },
    Case {
        name: "nl_square_narrow_no_false_refute_sat",
        script: "(declare-const x Real)(declare-const y Real)(assert (< (+ (* x x)(* y y)) 4))(assert (> (* x y) 1))(check-sat)",
    },
];

/// Run `z3` on a script, returning its `(check-sat)` verdict lines, or `None`
/// if the binary is unavailable or errored.
fn z3_verdicts(script: &str) -> Option<Vec<String>> {
    let out = Command::new("z3")
        .args(["-in"])
        .arg("-smt2")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.take()?.write_all(script.as_bytes()).ok()?;
            child.wait_with_output().ok()
        })?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    // Capture every non-empty output line (verdicts *and* (get-value)/
    // (get-unsat-core)/model responses), so the corpus can check that z3rs
    // reproduces z3's full response stream, not just the sat/unsat verdict.
    let lines: Vec<String> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();
    Some(lines)
}

#[test]
fn matches_z3_on_corpus() {
    // Probe for z3 once; skip the whole suite if missing.
    if z3_verdicts("(check-sat)").is_none() {
        eprintln!("z3 not available — skipping differential suite");
        return;
    }

    let mut mismatches = Vec::new();
    for case in CORPUS {
        let ours = match run_smt2(case.script) {
            Ok(v) => v,
            Err(e) => {
                mismatches.push(format!("{}: z3rs error: {e}", case.name));
                continue;
            }
        };
        let Some(theirs) = z3_verdicts(case.script) else {
            mismatches.push(format!("{}: z3 failed to produce a verdict", case.name));
            continue;
        };
        // "unknown" from z3rs is always sound (an incomplete procedure declined
        // to guess), so it never counts as a mismatch against a definite z3
        // verdict — only sat-vs-unsat disagreements do.
        let disagree = ours.len() != theirs.len()
            || ours
                .iter()
                .zip(&theirs)
                .any(|(o, t)| o != "unknown" && o != t);
        if disagree {
            mismatches.push(format!("{}: z3rs={ours:?} vs z3={theirs:?}", case.name));
        }
    }
    assert!(
        mismatches.is_empty(),
        "differential mismatches:\n{}",
        mismatches.join("\n")
    );
}
