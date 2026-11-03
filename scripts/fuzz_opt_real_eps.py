#!/usr/bin/env python3
"""Differential fuzz of linear real optimization with equalities and strict bounds.

Random problems over 2-3 Real constants: 1-2 linear equalities, 1-3
(strict or not) inequalities, one objective. The output must be identical
to z3's: in particular an open optimum `r -/+ k*epsilon`, whose k follows
the bounds z3's solve-eqs leaves (DIFF-eps), and the verdicts (DIFF).

Usage: scripts/fuzz_opt_real_eps.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random, subprocess, sys, concurrent.futures
from collections import Counter
RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0
def num(k): return f"{k}.0" if k >= 0 else f"(- {-k}.0)"
def gen(r):
    vs = ["x", "y", "z"][:r.randint(2, 3)]
    def lin():
        ts = [f"(* {num(r.randint(-3, 3))} {v})" for v in vs if r.random() < .7] or [vs[0]]
        r.shuffle(ts)
        return "(+ " + " ".join(ts) + ")" if len(ts) > 1 else ts[0]
    a = [f"(declare-const {v} Real)" for v in vs]
    for _ in range(r.randint(1, 2)):
        a.append(f"(assert (= {lin()} {num(r.randint(-5, 5))}))")
    for _ in range(r.randint(1, 3)):
        a.append(f"(assert ({r.choice(['<', '>', '<=', '>='])} {lin()} {num(r.randint(-5, 5))}))")
    a.append(f"({r.choice(['maximize', 'minimize'])} {lin()})")
    a.append("(check-sat)(get-objectives)")
    return "\n".join(a) + "\n"
def run(c, p):
    try: return subprocess.run([c, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired: return "TIMEOUT"
def one(i):
    p = f"{OUT}/le_{i}.smt2"; open(p, "w").write(gen(random.Random(i)))
    a, b = run(RS, p), run(Z3, p)
    if a == b: return ("same-eps" if "epsilon" in a else "same"), p
    return ("DIFF-eps" if "epsilon" in a + b else "DIFF"), p
res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k.startswith("DIFF"): print(k, p)
