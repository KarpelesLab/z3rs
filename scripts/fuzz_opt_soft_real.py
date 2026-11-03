#!/usr/bin/env python3
"""Differential fuzz of real objectives among soft constraints and disjunctions.

Random problems over two boxed Real constants and up to three Booleans:
disjunctive hard constraints, 1-5 `assert-soft`s (some grouped by `:id`)
and one `maximize`/`minimize` of a linear term, in random lex order. The
output must be identical to z3's (DIFF otherwise). z3rs answers `unknown`
(rs-unknown) when an open real optimum precedes other objectives, where z3
reports an interval that depends on its models.

Usage: scripts/fuzz_opt_soft_real.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random, subprocess, sys, concurrent.futures
from collections import Counter
RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0
def num(k): return f"{k}.0" if k >= 0 else f"(- {-k}.0)"
def gen(r):
    vs = ["x", "y"]
    bs = ["p", "q", "r"][:r.randint(1, 3)]
    def lin():
        return "(+ " + " ".join(f"(* {num(r.randint(-2, 2))} {v})" for v in vs) + ")"
    def atom():
        if r.random() < .4:
            return r.choice(bs)
        return f"({r.choice(['<=', '<', '>='])} {lin()} {num(r.randint(-4, 4))})"
    def lit():
        a = atom()
        return f"(not {a})" if r.random() < .3 else a
    a = [f"(declare-const {v} Real)" for v in vs] + [f"(declare-const {b} Bool)" for b in bs]
    a += [f"(assert (<= (- 5.0) {v} 5.0))" for v in vs]
    for _ in range(r.randint(1, 3)):
        a.append(f"(assert (or {lit()} {lit()}))")
    objs = []
    for _ in range(r.randint(1, 5)):
        objs.append(f"(assert-soft {lit()} :weight {r.randint(1, 4)}{r.choice(['', ' :id g'])})")
    objs.append(f"({r.choice(['maximize', 'minimize'])} {lin()})")
    r.shuffle(objs)
    a += objs
    a.append("(check-sat)(get-objectives)")
    return "\n".join(a) + "\n"
def run(c, p):
    try: return subprocess.run([c, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired: return "TIMEOUT"
def one(i):
    p = f"{OUT}/sr_{i}.smt2"; open(p, "w").write(gen(random.Random(i)))
    a, b = run(RS, p), run(Z3, p)
    if a == b: return "same", p
    if "unknown" in a: return "rs-unknown", p
    return "DIFF", p
res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k != "same": print(k, p)
