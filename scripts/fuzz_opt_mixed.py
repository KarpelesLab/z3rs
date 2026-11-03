#!/usr/bin/env python3
"""Differential fuzz of mixed optimization problems against z3.

Random problems over 1-3 Int/Real constants: optional boxes, linear atoms
with term-level `ite`s, disjunctions, 1-3 objectives (also with `ite`s)
under lex or box priority. A sat/unsat mismatch is VERDICT, a differing
value DIFF (both bugs). Differences in an `epsilon` coefficient
(diff-eps) or in an interval (diff-interval: after an unbounded objective
or an open optimum, z3's endpoints come from its models) are reported
apart.

Usage: scripts/fuzz_opt_mixed.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random, subprocess, sys, concurrent.futures
from collections import Counter
RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0
def gen(r):
    srts = {v: r.choice(["Int", "Real"]) for v in ["x", "y", "z"][:r.randint(1, 3)]}
    vs = list(srts)
    def num(k, s): return (f"{k}.0" if k >= 0 else f"(- {-k}.0)") if s == "Real" else (str(k) if k >= 0 else f"(- {-k})")
    def term(s=None):
        same = [v for v in vs if s is None or srts[v] == s]
        if not same:
            return num(r.randint(-3, 3), s)
        ts = []
        for v in same:
            if r.random() < .7:
                ts.append(f"(* {num(r.randint(-3, 3), srts[v])} {v})")
        if r.random() < .2 and len(same) >= 1:
            c = f"({r.choice(['<', '>='])} {same[0]} {num(r.randint(-2, 2), srts[same[0]])})"
            ts.append(f"(ite {c} {num(r.randint(-3, 3), srts[same[0]])} {num(r.randint(-3, 3), srts[same[0]])})")
        if not ts:
            ts = [same[0]]
        return "(+ " + " ".join(ts) + ")" if len(ts) > 1 else ts[0]
    def atom():
        s = r.choice(list(set(srts.values())))
        return f"({r.choice(['<=', '<', '>=', '>', '='])} {term(s)} {num(r.randint(-6, 6), s)})"
    a = []
    if r.random() < .3:
        a.append("(set-option :opt.priority box)")
    a += [f"(declare-const {v} {s})" for v, s in srts.items()]
    for v, s in srts.items():
        if r.random() < .6:
            a.append(f"(assert (<= {num(-r.randint(0, 6), s)} {v} {num(r.randint(0, 6), s)}))")
    for _ in range(r.randint(1, 3)):
        if r.random() < .4:
            a.append(f"(assert (or {atom()} {atom()}))")
        else:
            a.append(f"(assert {atom()})")
    for _ in range(r.randint(1, 3)):
        s = r.choice(list(set(srts.values())))
        a.append(f"({r.choice(['maximize', 'minimize'])} {term(s)})")
    a.append("(check-sat)(get-objectives)")
    return "\n".join(a) + "\n"
def run(c, p):
    try: return subprocess.run([c, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired: return "TIMEOUT"
def one(i):
    p = f"{OUT}/mx_{i}.smt2"; open(p, "w").write(gen(random.Random(i)))
    a, b = run(RS, p), run(Z3, p)
    if a == b: return "same", p
    if a.split("\n")[0] != b.split("\n")[0]:
        va, vb = a.split("\n")[0], b.split("\n")[0]
        if {va, vb} == {"sat", "unsat"}: return "VERDICT", p
        return f"verd-{va}/{vb}", p
    if "unknown" in a and "unknown" not in b: return "rs-unknown", p
    if "epsilon" in a + b: return "diff-eps", p
    if "interval" in a + b: return "diff-interval", p
    return "DIFF", p
res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k != "same": print(k, p)
