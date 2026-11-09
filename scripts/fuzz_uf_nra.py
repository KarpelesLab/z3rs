#!/usr/bin/env python3
"""Differential fuzz of nonlinear real arithmetic mixed with uninterpreted functions.

Random goals over 1-3 reals with a unary `f` and a binary `g` (Real -> Real),
polynomial constraints over variables and applications (nested ones too), and
argument equalities that make congruence matter (`x = y ∧ f(x) > f(y)`).
z3rs and z3 must agree on every decided verdict (DISAGREE otherwise). A z3rs
`sat` model without irrational values is replayed into z3 as `define-fun`s
(constants and function graphs) and must satisfy the assertions (BADMODEL
otherwise). GAP counts goals z3 decides and z3rs leaves `unknown`.

Usage: scripts/fuzz_uf_nra.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import os
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0
os.makedirs(OUT, exist_ok=True)


def gen(r):
    vs = [f"x{i}" for i in range(r.randint(1, 3))]

    def num():
        k = r.randint(-4, 4)
        return f"{k}.0" if k >= 0 else f"(- {-k}.0)"

    def arg(d):
        c = r.random()
        if d > 0 and c < 0.2:
            return app(d - 1)
        if c < 0.35:
            return f"(+ {r.choice(vs)} {num()})"
        return r.choice(vs)

    def app(d=1):
        if r.random() < 0.65:
            return f"(f {arg(d)})"
        return f"(g {arg(d)} {arg(d)})"

    def leaf():
        return app() if r.random() < 0.45 else r.choice(vs)

    def mono():
        fs = [leaf() for _ in range(r.randint(0, 2))]
        return f"(* {num()} {' '.join(fs)})" if fs else num()

    def poly():
        return f"(+ {' '.join(mono() for _ in range(r.randint(1, 3)))})"

    def atom():
        c = r.random()
        if c < 0.12:
            a, b = r.sample(vs, 2) if len(vs) > 1 else (vs[0], vs[0])
            return f"(= {a} {b})"
        if c < 0.2:
            return f"(distinct {app()} {app()})"
        op = r.choice(["<", "<=", "=", ">", ">=", "<=", "distinct"])
        return f"({op} {poly()} {num()})"

    def form():
        if r.random() < 0.15:
            return f"(or {atom()} {atom()})"
        return atom()

    asserts = [f"(assert {form()})" for _ in range(r.randint(2, 5))]
    if not any("(f " in a or "(g " in a for a in asserts):
        asserts.append(f"(assert (<= (f {r.choice(vs)}) {num()}))")
    return vs, asserts


def run(c, src, p, t=20):
    open(p, "w").write(src)
    try:
        return subprocess.run([c, p], capture_output=True, text=True, timeout=t).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def model_defs(out):
    """The `define-fun` blocks of a `(get-model)` answer (balanced parens)."""
    defs, i = [], out.find("(define-fun")
    while i >= 0:
        d, j = 0, i
        while j < len(out):
            d += out[j] == "("
            d -= out[j] == ")"
            j += 1
            if d == 0:
                break
        defs.append(out[i:j])
        i = out.find("(define-fun", j)
    return defs


HEAD = "(declare-fun f (Real) Real)\n(declare-fun g (Real Real) Real)\n"


def one(i):
    r = random.Random(i)
    vs, asserts = gen(r)
    decls = HEAD + "".join(f"(declare-const {v} Real)\n" for v in vs)
    body = decls + "\n".join(asserts) + "\n(check-sat)\n"
    p = f"{OUT}/u_{i}.smt2"
    z = run(Z3, body, p).strip()
    out = run(RS, body + "(get-model)\n", f"{OUT}/u_{i}_m.smt2")
    o = out.split("\n", 1)[0].strip()
    if o in ("sat", "unsat") and z in ("sat", "unsat") and o != z:
        return "DISAGREE", p
    if o != "sat":
        if o == "unsat":
            return "unsat", p
        return ("GAP" if z in ("sat", "unsat") else "both-unknown"), p
    defs = model_defs(out)
    if any("root-obj" in d for d in defs):
        return "sat-alg", p
    names = set(re.findall(r"\(define-fun (\S+)", " ".join(defs)))
    src = [d for d in defs]
    if "f" not in names:
        src.append("(declare-fun f (Real) Real)")
    if "g" not in names:
        src.append("(declare-fun g (Real Real) Real)")
    src += [f"(declare-const {v} Real)" for v in vs if v not in names]
    q = f"{OUT}/u_{i}_replay.smt2"
    zr = run(Z3, "\n".join(src) + "\n" + "\n".join(asserts) + "\n(check-sat)\n", q).strip()
    if zr == "unsat":
        return "BADMODEL", q
    return ("sat" if zr == "sat" else "replay:" + zr[:20]), q


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "GAP") or k.startswith("replay"):
        print(k, p)
