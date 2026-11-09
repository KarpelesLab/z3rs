#!/usr/bin/env python3
"""Differential fuzz of `get-model` output on seq.foldl / seq.foldli / seq.map
goals with seq.nth reads (the shape of z3test's
seq_foldl_nth_model_validation.smt2).

A sequence variable `elements` is folded or mapped by a macro into `all`
(Int or (Seq Int)), whose value is read back with seq.nth / taken as is and
equated to `final`; `initial` and `final` get fixed values and the length of
`elements` is sometimes pinned. For every z3rs `sat` model:

  DISAGREE  z3rs and z3 answer sat and unsat (a soundness bug)
  BADMODEL  the model's `define-fun`s, asserted back with the assertions,
            are not `sat` under z3 (a soundness bug)
  MATCH     the output is byte-for-byte z3's
  DIFF      a valid model that differs from z3's

With -v, a DIFF also reports why, from z3's point of view: `R<k>` is the
number of times theory_seq asked z3 to search again, `P` that z3's model
held a poly!N assumption before compression (which reorders the constants),
`U` that z3 printed seq.nth_u.

Usage: scripts/fuzz_seq_model_order.py <z3rs> <z3> <n> <outdir> [seed-offset] [-v]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

ARGS = [a for a in sys.argv[1:] if a != "-v"]
VERBOSE = "-v" in sys.argv
RS, Z3, N, OUT = ARGS[0], ARGS[1], int(ARGS[2]), ARGS[3]
OFF = int(ARGS[4]) if len(ARGS) > 4 else 0

MACROS = {
    # name: (definition, kind, acc sort)
    "all_sums": ("(define-fun all_sums ((prev (Seq Int)) (elem Int)) (Seq Int)\n"
                 "  (seq.++ (seq.unit (+ (seq.nth prev 0) elem)) prev))", "foldl", "seq"),
    "push": ("(define-fun push ((prev (Seq Int)) (elem Int)) (Seq Int)\n"
             "  (seq.++ prev (seq.unit elem)))", "foldl", "seq"),
    "add": ("(define-fun add ((a Int) (x Int)) Int (+ a x))", "foldl", "int"),
    "mx": ("(define-fun mx ((a Int) (x Int)) Int (ite (< a x) x a))", "foldl", "int"),
    "addi": ("(define-fun addi ((i Int) (a Int) (x Int)) Int (+ a (* i x)))", "foldli", "int"),
    "inc": ("(define-fun inc ((x Int)) Int (+ x 1))", "map", "seq"),
    "dbl": ("(define-fun dbl ((x Int)) Int (* 2 x))", "map", "seq"),
}


def gen(r):
    name = r.choice(list(MACROS))
    defn, kind, acc = MACROS[name]
    ini, fin = r.randint(-1, 2), r.randint(-2, 8)
    lines = ["(declare-const initial Int)"]
    asort = "(Seq Int)" if acc == "seq" else "Int"
    lines.append(f"(declare-const all {asort})")
    lines.append("(declare-const final Int)")
    lines.append("(declare-const elements (Seq Int))")
    lines.append(defn)
    if kind == "foldl":
        start = "(seq.unit initial)" if acc == "seq" else "initial"
        lines.append(f"(assert (= all (seq.foldl {name} {start} elements)))")
    elif kind == "foldli":
        lines.append(f"(assert (= all (seq.foldli {name} {r.randint(0, 1)} initial elements)))")
    else:
        lines.append(f"(assert (= all (seq.map {name} elements)))")
    if acc == "seq":
        k = 0 if r.random() < .7 else r.randint(0, 1)
        lines.append(f"(assert (= final (seq.nth all {k})))")
    else:
        lines.append("(assert (= final all))")
    lines.append(f"(assert (= initial {ini}))" if ini >= 0
                 else f"(assert (= initial (- {-ini})))")
    lines.append(f"(assert (= final {fin}))" if fin >= 0
                 else f"(assert (= final (- {-fin})))")
    if r.random() < .25:
        lines.append(f"(assert (= (seq.len elements) {r.randint(0, 2)}))")
    return "\n".join(lines) + "\n"


def run(c, p, extra=()):
    try:
        out = subprocess.run([c, *extra, p], capture_output=True, text=True, timeout=20)
        return out.stdout, out.stderr
    except subprocess.TimeoutExpired:
        return "timeout", ""


def why(p):
    _, err = run(Z3, p, ["-v:1"])
    nc, _ = run(Z3, p, ["model.compact=false"])
    zo, _ = run(Z3, p)
    tag = "R%d" % err.count("smt.seq")
    if "poly!" in nc:
        tag += "P"
    if "seq.nth_u" in zo:
        tag += "U"
    return tag


def valid(src, out, chk):
    """Is the model printed in `out` (after `sat`) a model of `src` for z3?"""
    body = out[len("sat\n"):].strip()
    if not (body.startswith("(") and body.endswith(")")):
        return False
    asserts = "".join(ln + "\n" for ln in src.splitlines() if ln.startswith("(assert"))
    # The macro (with its continuation line), then the model's definitions.
    mac = "".join(re.findall(r"\(define-fun .*\n(?:  .*\n)?", src))
    body = body[1:-1]
    if "define-fun seq.nth_u " in body:
        # z3 refuses to redefine its out-of-range read: the reads of the
        # assertions go through a copy of it instead.
        body = body.replace("define-fun seq.nth_u ", "define-fun nthu_model ")
        body += ("\n(define-fun nth_chk ((s (Seq Int)) (i Int)) Int\n"
                 "  (ite (and (<= 0 i) (< i (seq.len s))) (seq.nth s i) (nthu_model s i)))")
        mac = mac.replace("(seq.nth ", "(nth_chk ")
        asserts = asserts.replace("(seq.nth ", "(nth_chk ")
        # The macros read through nth_chk, defined after the model.
        open(chk, "w").write(body + "\n" + mac + asserts + "(check-sat)\n")
    else:
        open(chk, "w").write(mac + body + "\n" + asserts + "(check-sat)\n")
    return run(Z3, chk)[0].split("\n")[0] == "sat"


def one(i):
    src = gen(random.Random(i))
    p = f"{OUT}/smo_{i}.smt2"
    open(p, "w").write(src + "(check-sat)\n(get-model)\n")
    a, b = run(RS, p)[0], run(Z3, p)[0]
    va, vb = a.split("\n")[0], b.split("\n")[0]
    if (va, vb) == ("unsat", "sat") and not valid(src, b, f"{OUT}/smo_{i}_z3check.smt2"):
        return "unsat/sat(z3 model invalid)", p
    if {va, vb} == {"sat", "unsat"}:
        return "DISAGREE", p
    if not a.startswith("sat\n"):
        return a.split("\n")[0] + "/" + b.split("\n")[0], p
    if not valid(src, a, f"{OUT}/smo_{i}_check.smt2"):
        return "BADMODEL", p
    if a == b:
        return "MATCH", p
    return ("DIFF " + why(p) if VERBOSE else "DIFF"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("BADMODEL", "DISAGREE") or (VERBOSE and k.startswith("DIFF")):
        print(k, p)
