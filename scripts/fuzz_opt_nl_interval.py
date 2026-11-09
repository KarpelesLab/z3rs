#!/usr/bin/env python3
"""Differential fuzz of the interval z3 reports for a nonlinear real objective
it cannot close: one Real x under a polynomial bound (x^k scaled, <= or <),
maximize or minimize x, with opt.optsmt_nlsat false (bisection) or
opt.optsmt_nlsat_supremum_rlimit 0 (an uncertified nlsat limit). Some cases
add side constraints over uninterpreted functions (which keep nlsat's cells
out, so the default options bisect too). Compares the whole output byte for
byte.

Usage: scripts/fuzz_opt_nl_interval.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import os, random, subprocess, sys, concurrent.futures
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0
os.makedirs(OUT, exist_ok=True)


def gen(r):
    k = r.choice([2, 2, 2, 3])
    c = r.choice([1, 1, 1, 2, 3, 4])
    d = r.randint(1, 30)
    mono = " ".join(["x"] * k)
    lhs = f"(* {mono})" if c == 1 else f"(* {c}.0 {mono})"
    op = r.choice(["<=", "<"])
    goal = r.choice(["maximize", "maximize", "minimize"])
    if goal == "minimize" and k % 2 == 1:
        goal = "maximize"
    a = []
    mode = r.random()
    rounds = r.choice([8, 8, 4, 6, 10])
    side = r.choice([None, None, None, "fx", "fy", "gx", "ngx", "fx2"])
    if side is None or r.random() < 0.5:
        if mode < 0.5:
            a.append("(set-option :opt.optsmt_nlsat false)")
        else:
            a.append("(set-option :opt.optsmt_nlsat_supremum_rlimit 0)")
    a.append(f"(set-option :opt.optsmt_bisect_rounds {rounds})")
    a.append("(declare-const x Real)")
    sides = {
        "fx": ["(declare-fun f (Real) Real)", f"(assert (<= (f x) {r.randint(-3, 9)}.0))"],
        "fy": ["(declare-const y Real)", "(declare-fun f (Real) Real)",
               f"(assert (>= (f y) {r.randint(-3, 9)}.0))"],
        "gx": ["(declare-fun g (Real) Bool)", "(assert (g x))"],
        "ngx": ["(declare-fun g (Real) Bool)", "(assert (not (g (* 2.0 x))))"],
        "fx2": ["(declare-fun f (Real) Real)", "(declare-fun g (Real) Bool)",
                f"(assert (<= (* 2.0 (f x)) {r.randint(-3, 9)}.0))", "(assert (g x))"],
    }
    side_lines = sides[side] if side else []
    a += [l for l in side_lines if l.startswith("(declare")]
    asserts = [f"(assert ({op} {lhs} {d}.0))"] + [l for l in side_lines if l.startswith("(assert")]
    if r.random() < 0.5:
        asserts.reverse()
    a += asserts
    a.append(f"({goal} x)")
    a.append("(check-sat)\n(get-objectives)")
    return "\n".join(a) + "\n"


def run(cmd, p):
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def one(i):
    r = random.Random(i)
    src = gen(r)
    p = f"{OUT}/nli_{i}.smt2"
    open(p, "w").write(src)
    a, b = run(RS, p), run(Z3, p)
    if a == b:
        return "same", p
    va, vb = a.split("\n")[0], b.split("\n")[0]
    if {va, vb} == {"sat", "unsat"}:
        return "VERDICT", p
    return "DIFF", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k != "same":
        print(k, p)
