#!/usr/bin/env python3
"""Differential fuzz of `get-model` on pure linear real conjunctions.

Random conjunctions of `<`/`<=`/`>`/`>=`/`=` (occasionally negated) over
Real constants `x y z w v`, then `(check-sat) (get-model)`. These are the
goals whose model z3rs replays through z3's `lar_solver` (see
`src/cmd_context/smt2/lra_conj.rs`). For every `sat` model z3rs prints:

  DISAGREE    z3rs and z3 differ on sat/unsat (a soundness bug)
  BADMODEL    the model's `define-fun`s, asserted back with the assertions,
              are unsatisfiable under z3 (a soundness bug)
  MATCH       the output is byte-for-byte z3's
  DIFF        a valid model that differs from z3's

Usage: scripts/fuzz_lra_conj_model.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0


def gen(r):
    vs = ["x", "y", "z", "w", "v"][: r.randint(2, 5)]

    def num():
        k = r.choice([0, 1, 2, 3, 5, 7, -1, -3, -6, "1.5", "0.25", "(/ 1 3)", "(/ 5 2)"])
        if isinstance(k, int):
            return str(k) if k >= 0 else f"(- {-k})"
        return k

    def coef():
        return r.choice(["1", "1", "(- 1)", "2", "(- 2)", "3", "(- 4)", "0.5", "(/ 2 3)"])

    def lin():
        ts = []
        for v in r.sample(vs, r.randint(1, min(3, len(vs)))):
            c = coef()
            ts.append(v if c == "1" else f"(* {c} {v})")
        if r.random() < .3:
            ts.append(num())
        return ts[0] if len(ts) == 1 else "(+ " + " ".join(ts) + ")"

    def atom():
        op = r.choice(["<", "<=", ">", ">=", "<=", ">=", "="])
        a, b = lin(), (num() if r.random() < .8 else lin())
        at = f"({op} {a} {b})"
        if op != "=" and r.random() < .15:
            at = f"(not {at})"
        return at

    decls = "".join(f"(declare-const {v} Real)\n" for v in vs)
    asserts = "".join(f"(assert {atom()})\n" for _ in range(r.randint(1, 6)))
    return decls, asserts


def run(c, p):
    try:
        out = subprocess.run([c, p], capture_output=True, text=True, timeout=20)
        return out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    decls, asserts = gen(random.Random(i))
    p = f"{OUT}/lc_{i}.smt2"
    open(p, "w").write(decls + asserts + "(check-sat)\n(get-model)\n")
    a, b = run(RS, p), run(Z3, p)
    va, vb = a.split("\n")[0], b.split("\n")[0]
    if {va, vb} == {"sat", "unsat"}:
        return "DISAGREE", p
    if va != "sat":
        return va, p
    body = a[len("sat\n"):].strip()
    defined = set(re.findall(r"\(define-fun (\S+) ", body))
    keep = "".join(ln + "\n" for ln in decls.splitlines()
                   if re.search(r"declare-\w+ (\S+)", ln).group(1) not in defined)
    chk = f"{OUT}/lc_{i}_check.smt2"
    open(chk, "w").write(keep + body[1:-1] + "\n" + asserts + "(check-sat)\n")
    if run(Z3, chk).split("\n")[0] != "sat":
        return "BADMODEL", p
    return ("MATCH" if a == b else "DIFF"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("BADMODEL", "DISAGREE"):
        print(k, p)
