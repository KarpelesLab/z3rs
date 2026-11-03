#!/usr/bin/env python3
"""Differential fuzz of floating-point values in arrays.

Random Boolean combinations over an `(Array Int (_ FloatingPoint 3 4))`
array, `store`s of float terms, reads at symbolic and constant indices,
float arithmetic (`fp.add`, `fp.mul`, `fp.neg`, `fp.abs`) under constant
rounding modes, comparisons, classification and `fp.to_real`, plus
integer index arithmetic. Definite verdicts are compared with z3
(DISAGREE = soundness bug), and every z3rs `sat` model is replayed through
z3 as define-funs (BADMODEL = wrong model).

Usage: scripts/fuzz_fp_array.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
F = "(_ FloatingPoint 3 4)"
DECLS = [f"(declare-const a (Array Int {F}))", f"(declare-const b (Array Int {F}))",
         f"(declare-const f {F})", f"(declare-const g {F})",
         "(declare-const i Int)", "(declare-const j Int)"]


def gen(r):
    def lit():
        return r.choice([f"((_ to_fp 3 4) RNE {r.choice(['1.0', '0.5', '2.0', '(- 1.5)', '0.0'])})",
                         "(_ +zero 3 4)", "(_ -zero 3 4)", "(_ +oo 3 4)", "(_ NaN 3 4)"])

    def idx(d=0):
        c = r.random()
        if d >= 2 or c < .6:
            return r.choice(["i", "j", str(r.randint(0, 3))])
        return f"(+ {idx(d + 1)} {r.randint(-1, 2)})"

    def arr(d=0):
        c = r.random()
        if d >= 2 or c < .5:
            return r.choice(["a", "b"])
        return f"(store {arr(d + 1)} {idx(d + 1)} {fp(d + 1)})"

    def fp(d=0):
        c = r.random()
        if d >= 2 or c < .35:
            return r.choice(["f", "g", lit()])
        if c < .6:
            return f"(select {arr(d + 1)} {idx(d + 1)})"
        op = r.choice(["fp.add", "fp.mul", "fp.neg", "fp.abs"])
        rm = r.choice(["RNE", "RTZ", "RTP"])
        if op in ("fp.neg", "fp.abs"):
            return f"({op} {fp(d + 1)})"
        return f"({op} {rm} {fp(d + 1)} {fp(d + 1)})"

    def form(d=0):
        c = r.random()
        if d < 2 and c < .2:
            op = r.choice(["and", "or", "not"])
            if op == "not":
                return f"(not {form(d + 1)})"
            return f"({op} {form(d + 1)} {form(d + 1)})"
        k = r.random()
        if k < .3:
            return f"({r.choice(['fp.eq', 'fp.lt', 'fp.leq', '='])} {fp(d + 1)} {fp(d + 1)})"
        if k < .45:
            return f"({r.choice(['fp.isNaN', 'fp.isZero', 'fp.isNormal', 'fp.isNegative'])} {fp(d + 1)})"
        if k < .6:
            return f"(= {arr(d + 1)} {arr(d + 1)})"
        if k < .75:
            return f"({r.choice(['<', '<=', '='])} (fp.to_real {fp(d + 1)}) {r.choice(['1.0', '0.0', '(- 2.0)'])})"
        return f"({r.choice(['=', '<', 'distinct'])} {idx(d + 1)} {idx(d + 1)})"

    return [f"(assert {form()})" for _ in range(r.randint(1, 4))]


def run(c, src, p):
    open(p, "w").write(src)
    try:
        return subprocess.run([c, p], capture_output=True, text=True, timeout=20).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def one(n):
    asserts = gen(random.Random(n))
    src = "\n".join(DECLS + asserts) + "\n(check-sat)\n"
    p = f"{OUT}/fa_{n}.smt2"
    out = run(RS, src + "(get-model)\n", p)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/fa_{n}_z3.smt2").split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        defs = [d for d in defs if not re.match(r"\(define-fun (/0|div0|mod0) ", d)]
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in DECLS if d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/fa_{n}_replay.smt2").strip()
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
