#!/usr/bin/env python3
"""Differential fuzz of nonlinear integer arithmetic (the incremental
linearization of `smt::nla` with its nlsat checks).

Random Boolean combinations of low-degree polynomial constraints over 2-5
mostly *unbounded* Int variables (some Real, for mixed problems), with
products of sums, squares and equalities, so that the refinement lemmas
(signs, monotonicity, order, tangent planes) and branch and bound do the
work. A DISAGREE (sat vs unsat against z3) is a soundness bug; a `sat` model
is replayed into z3 (constants as definitions): BADMODEL if z3 then finds
the assertions unsat. Also reports the gap (z3 decides, z3rs does not).

Usage: scripts/fuzz_nia.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0
TIMEOUT = 10.0


def gen(r):
    nv = r.randint(2, 5)
    vs = [f"x{i}" for i in range(nv)]
    sorts = {v: ("Real" if r.random() < 0.15 else "Int") for v in vs}
    if all(s == "Real" for s in sorts.values()):
        sorts[vs[0]] = "Int"
    ints = all(s == "Int" for s in sorts.values())

    def num(lo=-9, hi=9):
        k = r.randint(lo, hi)
        s = f"{abs(k)}" if ints else f"{abs(k)}.0"
        return s if k >= 0 else f"(- {s})"

    def var():
        return r.choice(vs)

    def lin():
        ts = [f"(* {num(-4, 4)} {var()})" for _ in range(r.randint(1, 2))] + [num()]
        return f"(+ {' '.join(ts)})"

    def term():
        c = r.random()
        if c < 0.3:
            return f"(* {var()} {var()})"
        if c < 0.45:
            return f"(* {var()} {var()} {var()})"
        if c < 0.6:
            return f"(* {lin()} {lin()})"
        if c < 0.7:
            a = lin()
            return f"(* {a} {a})"
        return lin()

    def poly():
        ts = [term() for _ in range(r.randint(1, 3))]
        if r.random() < 0.5:
            ts.append(num())
        return ts[0] if len(ts) == 1 else f"(+ {' '.join(ts)})"

    def atom():
        op = r.choice(["<", "<=", ">", ">=", "=", "=", "distinct"])
        return f"({op} {poly()} {num() if r.random() < 0.7 else poly()})"

    decls = [f"(declare-fun {v} () {sorts[v]})" for v in vs]
    asserts = []
    for _ in range(r.randint(2, 5)):
        c = r.random()
        if c < 0.55:
            asserts.append(f"(assert {atom()})")
        elif c < 0.85:
            lits = [atom() for _ in range(r.randint(2, 3))]
            asserts.append(f"(assert (or {' '.join(lits)}))")
        else:
            asserts.append(f"(assert (=> {atom()} {atom()}))")
    return decls, asserts


def run(cmd, src, p, t):
    open(p, "w").write(src)
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=t).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    decls, asserts = gen(random.Random(i))
    src = "\n".join(decls) + "\n" + "\n".join(asserts) + "\n(check-sat)\n"
    p = f"{OUT}/nia_{i}.smt2"
    out = run(RS, src + "(get-model)\n", p, TIMEOUT)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/nia_{i}_z3.smt2", TIMEOUT).split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in decls if d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/nia_{i}_replay.smt2", 60).strip()
        if z.startswith("unsat"):
            return "BADMODEL", p
        if "error" in z:
            return "REPLAY-ERROR", p
    if a in ("sat", "unsat") and b in ("sat", "unsat"):
        return ("agree" if a == b else "DISAGREE"), p
    if b in ("sat", "unsat"):
        return f"GAP-{b}", p
    return f"{a}/{b}", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "REPLAY-ERROR"):
        print(k, p)
