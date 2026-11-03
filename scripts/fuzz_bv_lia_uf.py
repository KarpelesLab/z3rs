#!/usr/bin/env python3
"""Differential fuzz of bit-vectors combined with integers and uninterpreted
functions.

Random Boolean combinations of bit-vector atoms (widths 3 and 4), integer
atoms and the links between them: `bv2nat`, `(_ int2bv w)`, functions
`f : Int -> BV`, `g : BV -> Int`, a predicate `p : BV -> Bool`, `ite`s and
equalities across the theories. Exercises the bit-blasting of bit-vectors
into the Boolean structure the DPLL(T) core decides with the other
theories. Definite verdicts are compared with z3 (DISAGREE = soundness bug),
and every z3rs `sat` model is replayed through z3 as define-funs
(BADMODEL = wrong model).

Usage: scripts/fuzz_bv_lia_uf.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
DECLS = ["(declare-const x (_ BitVec 4))", "(declare-const y (_ BitVec 4))",
         "(declare-const z (_ BitVec 3))", "(declare-const i Int)",
         "(declare-const j Int)", "(declare-const b Bool)",
         "(declare-fun f (Int) (_ BitVec 4))", "(declare-fun g ((_ BitVec 4)) Int)",
         "(declare-fun p ((_ BitVec 4)) Bool)"]


def gen(r):
    def bv(d=0):
        c = r.random()
        if d >= 2 or c < .3:
            return r.choice(["x", "y", f"#x{r.randrange(16):x}", "(f i)", "(f j)"])
        op = r.choice(["bvadd", "bvmul", "bvand", "bvor", "bvxor", "bvsub", "bvlshr",
                       "bvudiv", "bvurem", "bvnot", "ite", "int2bv", "concat", "f"])
        if op == "bvnot":
            return f"(bvnot {bv(d + 1)})"
        if op == "ite":
            return f"(ite {form(d + 1)} {bv(d + 1)} {bv(d + 1)})"
        if op == "int2bv":
            return f"((_ int2bv 4) {ar(d + 1)})"
        if op == "concat":
            return f"(concat ((_ extract 0 0) {bv(d + 1)}) z)"
        if op == "f":
            return f"(f {ar(d + 1)})"
        return f"({op} {bv(d + 1)} {bv(d + 1)})"

    def ar(d=0):
        c = r.random()
        if d >= 2 or c < .35:
            return r.choice(["i", "j", str(r.randint(-3, 20))])
        op = r.choice(["+", "-", "*c", "bv2nat", "g", "ite"])
        if op == "*c":
            return f"(* {r.randint(-2, 3)} {ar(d + 1)})"
        if op == "bv2nat":
            return f"(bv2nat {bv(d + 1)})"
        if op == "g":
            return f"(g {bv(d + 1)})"
        if op == "ite":
            return f"(ite {form(d + 1)} {ar(d + 1)} {ar(d + 1)})"
        return f"({op} {ar(d + 1)} {ar(d + 1)})"

    def form(d=0):
        c = r.random()
        if d < 2 and c < .25:
            op = r.choice(["and", "or", "=>", "not"])
            if op == "not":
                return f"(not {form(d + 1)})"
            return f"({op} {form(d + 1)} {form(d + 1)})"
        k = r.random()
        if k < .4:
            return f"({r.choice(['=', 'bvult', 'bvule', 'bvslt', 'distinct'])} {bv(d + 1)} {bv(d + 1)})"
        if k < .75:
            return f"({r.choice(['=', '<', '<=', 'distinct'])} {ar(d + 1)} {ar(d + 1)})"
        if k < .9:
            return f"(p {bv(d + 1)})"
        return r.choice(["b", f"(= b (p {bv(d + 1)}))"])

    asserts = [f"(assert {form()})" for _ in range(r.randint(1, 4))]
    return asserts


def run(c, src, p):
    open(p, "w").write(src)
    try:
        return subprocess.run([c, p], capture_output=True, text=True, timeout=20).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    asserts = gen(random.Random(i))
    src = "\n".join(DECLS + asserts) + "\n(check-sat)\n"
    p = f"{OUT}/bl_{i}.smt2"
    out = run(RS, src + "(get-model)\n", p)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/bl_{i}_z3.smt2").split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        defs = [d for d in defs if not re.match(r"\(define-fun (/0|div0|mod0) ", d)]
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in DECLS if d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/bl_{i}_replay.smt2").strip()
        if z.startswith("unsat"):
            return "BADMODEL", p
        if "error" in z:
            return "REPLAY-ERROR", p
    if a in ("sat", "unsat") and b in ("sat", "unsat"):
        return ("agree" if a == b else "DISAGREE"), p
    return f"{a}/{b}", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "REPLAY-ERROR"):
        print(k, p)
