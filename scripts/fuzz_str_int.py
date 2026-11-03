#!/usr/bin/env python3
"""Differential fuzz of `str.to_int` / `str.from_int`.

Random Boolean combinations over string constants `s`, `t` and integers
`i`, `j`: `str.to_int` of strings built from the constants and literals
mixing digits and letters (`"07"`, `"1a"`, `"42"`, …), `str.from_int` of
linear integer terms, their lengths, concatenations, `str.at`, the
containment predicates, and comparisons with numerals. Definite verdicts
are compared with z3 (DISAGREE = soundness bug), and every z3rs `sat` model
is replayed through z3 as define-funs (BADMODEL = wrong model).

Usage: scripts/fuzz_str_int.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
DECLS = ["(declare-const s String)", "(declare-const t String)",
         "(declare-const i Int)", "(declare-const j Int)"]
LITS = ['""', '"0"', '"7"', '"07"', '"42"', '"a"', '"1a"', '"a1"', '"10"']


def gen(r):
    def st(d=0):
        c = r.random()
        if d >= 2 or c < .4:
            return r.choice(["s", "t"] + LITS)
        op = r.choice(["++", "from_int", "from_int", "at"])
        if op == "++":
            return f"(str.++ {st(d + 1)} {st(d + 1)})"
        if op == "at":
            return f"(str.at {st(d + 1)} {ar(d + 1)})"
        return f"(str.from_int {ar(d + 1)})"

    def ar(d=0):
        c = r.random()
        if d >= 2 or c < .4:
            return r.choice(["i", "j", str(r.randint(-2, 12))])
        op = r.choice(["to_int", "to_int", "len", "+"])
        if op == "to_int":
            return f"(str.to_int {st(d + 1)})"
        if op == "len":
            return f"(str.len {st(d + 1)})"
        return f"(+ {ar(d + 1)} {ar(d + 1)})"

    def form(d=0):
        c = r.random()
        if d < 2 and c < .2:
            op = r.choice(["and", "or", "not"])
            if op == "not":
                return f"(not {form(d + 1)})"
            return f"({op} {form(d + 1)} {form(d + 1)})"
        k = r.random()
        if k < .35:
            return f"(= {st(d + 1)} {st(d + 1)})"
        if k < .5:
            return f"({r.choice(['str.prefixof', 'str.contains', 'str.suffixof'])} {st(d + 1)} {st(d + 1)})"
        return f"({r.choice(['=', '<', '<=', 'distinct'])} {ar(d + 1)} {ar(d + 1)})"

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
    p = f"{OUT}/si_{n}.smt2"
    out = run(RS, src + "(get-model)\n", p)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/si_{n}_z3.smt2").split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in DECLS if d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/si_{n}_replay.smt2").strip()
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
