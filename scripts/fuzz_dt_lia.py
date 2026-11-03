#!/usr/bin/env python3
"""Differential fuzz of recursive datatypes with integer arithmetic.

Random Boolean combinations over list and tree constants (`(List Int)` with
`nil`/`cons`, a binary `Tree` with integer leaves), integer constants and
an uninterpreted `f : Int -> Int`: constructor equalities, testers,
selector reads (also of the wrong constructor, which are unspecified),
linear arithmetic over the selected integers, and `ite`. Definite verdicts
are compared with z3 (DISAGREE = soundness bug), and every z3rs `sat`
model is replayed through z3 as define-funs (BADMODEL = wrong model).

Usage: scripts/fuzz_dt_lia.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
DECLS = ["(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))",
         "(declare-datatypes ((T 0)) (((leaf (val Int)) (node (left T) (right T)))))",
         "(declare-const x L)", "(declare-const y L)", "(declare-const t T)",
         "(declare-const i Int)", "(declare-const j Int)",
         "(declare-fun f (Int) Int)"]
CONSTS = {"x", "y", "t", "i", "j"}


def gen(r):
    def lst(d=0):
        c = r.random()
        if d >= 2 or c < .45:
            return r.choice(["x", "y", "nil", "(tl x)", "(tl y)"])
        if c < .85:
            return f"(cons {ar(d + 1)} {lst(d + 1)})"
        return f"(ite {form(d + 1)} {lst(d + 1)} {lst(d + 1)})"

    def tree(d=0):
        c = r.random()
        if d >= 2 or c < .4:
            return r.choice(["t", "(left t)", "(right t)"])
        if c < .7:
            return f"(leaf {ar(d + 1)})"
        return f"(node {tree(d + 1)} {tree(d + 1)})"

    def ar(d=0):
        c = r.random()
        if d >= 2 or c < .4:
            return r.choice(["i", "j", str(r.randint(-2, 4))])
        op = r.choice(["+", "-", "hd", "val", "f", "*c"])
        if op == "hd":
            return f"(hd {lst(d + 1)})"
        if op == "val":
            return f"(val {tree(d + 1)})"
        if op == "f":
            return f"(f {ar(d + 1)})"
        if op == "*c":
            return f"(* {r.randint(-2, 3)} {ar(d + 1)})"
        return f"({op} {ar(d + 1)} {ar(d + 1)})"

    def form(d=0):
        c = r.random()
        if d < 2 and c < .2:
            op = r.choice(["and", "or", "=>", "not"])
            if op == "not":
                return f"(not {form(d + 1)})"
            return f"({op} {form(d + 1)} {form(d + 1)})"
        k = r.random()
        if k < .3:
            return f"(= {lst(d + 1)} {lst(d + 1)})"
        if k < .45:
            return f"((_ is {r.choice(['nil', 'cons'])}) {lst(d + 1)})"
        if k < .55:
            return f"((_ is {r.choice(['leaf', 'node'])}) {tree(d + 1)})"
        if k < .65:
            return f"(= {tree(d + 1)} {tree(d + 1)})"
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
    p = f"{OUT}/dl_{n}.smt2"
    out = run(RS, src + "(get-model)\n", p)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/dl_{n}_z3.smt2").split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in DECLS if not (d.startswith("(declare-const") or
                                       d.startswith("(declare-fun")) or d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/dl_{n}_replay.smt2").strip()
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
