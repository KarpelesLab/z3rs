#!/usr/bin/env python3
"""Differential soundness fuzz of the nlsat solver (src/nlsat/solver.rs).

Random Boolean combinations (CNF with disjunctions, plus nested and/or/=>) of
polynomial constraints of degree <= 3 over 2-6 reals, some with divisions --
the shape that reaches the conflict-driven nlsat search when the conjunctive
procedures decline. A DISAGREE (sat vs unsat against z3) is a soundness bug; a
`sat` model is replayed into z3 (its constants as definitions, root-obj
values included): BADMODEL if z3 then finds the assertions unsat.

Usage: scripts/fuzz_nlsat.py <z3rs> <z3> <n> <outdir>
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]


def gen(r):
    vs = [f"x{i}" for i in range(r.randint(2, 6))]

    def num():
        k = r.choice([0, 1, 2, 3, 5, 0.5, 7])
        s = f"{float(k)}"
        return s if r.random() < 0.7 else f"(- {s})"

    def mono():
        c = r.random()
        if c < 0.35:
            return r.choice(vs)
        if c < 0.6:
            return f"(* {r.choice(vs)} {r.choice(vs)})"
        if c < 0.7:
            return f"(* {r.choice(vs)} {r.choice(vs)} {r.choice(vs)})"
        if c < 0.8:
            return f"(/ {r.choice(vs)} {r.choice(vs)})"
        return num()

    def poly():
        ts = [mono() for _ in range(r.randint(1, 3))]
        ts = [t if r.random() < 0.7 else f"(* {num()} {t})" for t in ts]
        return ts[0] if len(ts) == 1 else f"(+ {' '.join(ts)})"

    def atom():
        op = r.choice(["<", "<=", ">", ">=", "=", "distinct"])
        return f"({op} {poly()} {num() if r.random() < 0.6 else poly()})"

    def formula(d):
        c = r.random()
        if d >= 2 or c < 0.5:
            a = atom()
            return a if r.random() < 0.8 else f"(not {a})"
        if c < 0.7:
            return f"(or {formula(d + 1)} {formula(d + 1)})"
        if c < 0.85:
            return f"(and {formula(d + 1)} {formula(d + 1)})"
        return f"(=> {formula(d + 1)} {formula(d + 1)})"

    decls = [f"(declare-fun {v} () Real)" for v in vs]
    asserts = []
    for _ in range(r.randint(2, 6)):
        if r.random() < 0.5:
            lits = [atom() for _ in range(r.randint(1, 3))]
            asserts.append(f"(assert (or {' '.join(lits)}))" if len(lits) > 1 else f"(assert {lits[0]})")
        else:
            asserts.append(f"(assert {formula(0)})")
    return decls, asserts


def run(cmd, src, p):
    open(p, "w").write(src)
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    decls, asserts = gen(random.Random(i))
    src = "\n".join(decls) + "\n" + "\n".join(asserts) + "\n(check-sat)\n"
    p = f"{OUT}/nl_{i}.smt2"
    out = run(RS, src + "(get-model)\n", p)
    a = out.split("\n")[0]
    b = run(Z3, src, f"{OUT}/nl_{i}_z3.smt2").split("\n")[0]
    if a == "sat":
        body = out[out.find("(", 4):]
        defs = re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)", body, re.S)
        defs = [d for d in defs if d.split()[1] not in ("/0", "div0", "mod0")]
        names = set(re.findall(r"\(define-fun (\S+)", body))
        ds = [d for d in decls if d.split()[1] not in names]
        rep = "\n".join(ds + [d.strip() for d in defs] + asserts) + "\n(check-sat)\n"
        z = run(Z3, rep, f"{OUT}/nl_{i}_replay.smt2").strip()
        if z.startswith("unsat"):
            return "BADMODEL", p
        if "error" in z:
            return "REPLAY-ERROR", p
    if a in ("sat", "unsat") and b in ("sat", "unsat"):
        return ("agree" if a == b else "DISAGREE"), p
    return f"{a}/{b}", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "REPLAY-ERROR"):
        print(k, p)
