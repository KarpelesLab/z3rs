#!/usr/bin/env python3
"""Differential fuzz of the nlsat solver on harder nonlinear problems.

Random Boolean combinations of polynomial constraints over 3-8 variables, of
total degree up to 6, with equalities mixed in (so samples sit on sections and
leading coefficients vanish) and factored atoms (products of small
polynomials, squares). `--int` makes some or all variables Int (QF_NIA, the
branch-and-bound path). A DISAGREE (sat vs unsat against z3) is a soundness
bug; a `sat` model is replayed into z3 (constants as definitions, root-obj
values included): BADMODEL if z3 then finds the assertions unsat.

Also reports the completeness gap: cases z3 decides within the timeout but
z3rs leaves unknown / times out (GAP).

Usage: scripts/fuzz_nlsat_hard.py <z3rs> <z3> <n> <outdir> [--int] [--timeout S] [--seed K]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
INT = "--int" in sys.argv
TIMEOUT = float(sys.argv[sys.argv.index("--timeout") + 1]) if "--timeout" in sys.argv else 10.0
SEED = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 0


def gen(r):
    nv = r.randint(3, 8)
    vs = [f"x{i}" for i in range(nv)]
    sorts = {v: ("Int" if INT and (r.random() < 0.7) else "Real") for v in vs}
    if INT and all(s == "Real" for s in sorts.values()):
        sorts[vs[0]] = "Int"
    # A few variables are "hot": most terms use them, so polynomials interact.
    hot = r.sample(vs, min(len(vs), r.randint(2, 4)))
    maxdeg = r.randint(2, 6)

    def var():
        return r.choice(hot) if r.random() < 0.7 else r.choice(vs)

    def num(small=False):
        k = r.choice([1, 2, 3, 5, 7] if small else [0, 1, 2, 3, 4, 5, 7, 10])
        if sorts_all_int():
            s = f"{k}"
        else:
            s = f"{float(k)}" if r.random() < 0.85 else f"(/ {k}.0 {r.choice([2, 3, 4])}.0)"
        return s if r.random() < 0.65 else f"(- {s})"

    def sorts_all_int():
        return all(s == "Int" for s in sorts.values())

    def mono():
        d = r.randint(1, maxdeg)
        fs = [var() for _ in range(d)]
        t = fs[0] if len(fs) == 1 else f"(* {' '.join(fs)})"
        return t if r.random() < 0.6 else f"(* {num(True)} {t})"

    def poly(terms=None):
        ts = [mono() for _ in range(terms or r.randint(1, 4))]
        if r.random() < 0.6:
            ts.append(num())
        return ts[0] if len(ts) == 1 else f"(+ {' '.join(ts)})"

    def lin():
        ts = [f"(* {num(True)} {var()})" for _ in range(r.randint(1, 3))] + [num()]
        return f"(+ {' '.join(ts)})"

    def factored():
        c = r.random()
        if c < 0.4:
            return f"(* {lin()} {lin()})"
        if c < 0.7:
            a = poly(2)
            return f"(* {a} {a})"
        return f"(* {lin()} {poly(2)})"

    def zero():
        return "0" if sorts_all_int() else "0.0"

    def atom():
        c = r.random()
        lhs = factored() if c < 0.25 else poly()
        op = r.choice(["<", "<=", ">", ">=", "=", "=", "distinct"])
        rhs = zero() if r.random() < 0.5 else (num() if r.random() < 0.6 else poly())
        return f"({op} {lhs} {rhs})"

    def formula(d):
        c = r.random()
        if d >= 2 or c < 0.5:
            a = atom()
            return a if r.random() < 0.8 else f"(not {a})"
        if c < 0.75:
            return f"(or {formula(d + 1)} {formula(d + 1)})"
        if c < 0.9:
            return f"(and {formula(d + 1)} {formula(d + 1)})"
        return f"(=> {formula(d + 1)} {formula(d + 1)})"

    decls = [f"(declare-fun {v} () {sorts[v]})" for v in vs]
    asserts = []
    # Bounds on some variables keep many problems sat and bounded.
    for v in vs:
        if r.random() < 0.3:
            b = r.randint(1, 10)
            z = f"{b}" if sorts[v] == "Int" else f"{b}.0"
            asserts.append(f"(assert (<= (- {z}) {v} {z}))")
    for _ in range(r.randint(2, 7)):
        c = r.random()
        if c < 0.45:
            asserts.append(f"(assert {atom()})")
        elif c < 0.75:
            lits = [atom() for _ in range(r.randint(2, 3))]
            asserts.append(f"(assert (or {' '.join(lits)}))")
        else:
            asserts.append(f"(assert {formula(0)})")
    return decls, asserts


def run(cmd, src, p, t):
    open(p, "w").write(src)
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=t).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    decls, asserts = gen(random.Random(SEED * 1000003 + i))
    src = "\n".join(decls) + "\n" + "\n".join(asserts) + "\n(check-sat)\n"
    p = f"{OUT}/nlh_{i}.smt2"
    out = run(RS, src + "(get-model)\n", p, TIMEOUT)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/nlh_{i}_z3.smt2", TIMEOUT).split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        defs = [d for d in defs if d.split()[1] not in ("/0", "div0", "mod0")]
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in decls if d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/nlh_{i}_replay.smt2", 60).strip()
        if z.startswith("unsat"):
            return "BADMODEL", p
        if "error" in z:
            return "REPLAY-ERROR", p
    if a in ("sat", "unsat") and b in ("sat", "unsat"):
        return ("agree" if a == b else "DISAGREE"), p
    if b in ("sat", "unsat"):
        return f"GAP-{b}", p
    return f"{a}/{b}", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "REPLAY-ERROR"):
        print(k, p)
with open(f"{OUT}/gap.txt", "w") as f:
    for k, p in res:
        if k.startswith("GAP"):
            f.write(f"{k} {p}\n")
