#!/usr/bin/env python3
"""Differential fuzz of `get-model` on small ground UF + linear integer problems.

Random assertions over Int constants `a b c`, functions `f : Int -> Int`,
`g : Int Int -> Int`, predicates `p : Int -> Bool`, `q : Int Int -> Bool` and
an unused function `u`, then `(check-sat) (get-model)`. For every `sat` model
z3rs prints:

  BADMODEL    the model's `define-fun`s, asserted back with the assertions,
              are unsatisfiable under z3 (a soundness bug)
              — or a declared symbol z3's model interprets is missing from
              it (z3 prints every declared symbol it interprets)
  INCOMPLETE  a declared symbol has no interpretation in the model
  MATCH       the output is byte-for-byte z3's
  DIFF        a complete, valid model that differs from z3's

Usage: scripts/fuzz_get_model.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
NAMES = ["a", "b", "c", "f", "g", "p", "q", "u"]


def gen(r):
    vs = ["a", "b", "c"]

    def num():
        k = r.randint(-2, 4)
        return str(k) if k >= 0 else f"(- {-k})"

    def term(d):
        k = r.random()
        if d >= 2 or k < .4:
            return r.choice(vs) if r.random() < .75 else num()
        if k < .65:
            return f"(f {term(d + 1)})"
        if k < .8:
            return f"(g {term(d + 1)} {term(d + 1)})"
        if k < .92:
            return f"(+ {term(d + 1)} {term(d + 1)})"
        return f"(- {term(d + 1)} {num()})"

    def atom():
        k = r.random()
        if k < .15:
            return f"(p {term(1)})"
        if k < .25:
            return f"(q {term(1)} {term(1)})"
        op = r.choice(["=", "=", "distinct", "<", "<=", ">="])
        return f"({op} {term(0)} {term(0)})"

    def lit():
        a = atom()
        return a if r.random() < .75 else f"(not {a})"

    decls = "".join(f"(declare-const {v} Int)\n" for v in vs)
    decls += ("(declare-fun f (Int) Int)\n(declare-fun g (Int Int) Int)\n"
              "(declare-fun p (Int) Bool)\n(declare-fun q (Int Int) Bool)\n"
              "(declare-fun u (Int) Int)\n")
    asserts = ""
    for _ in range(r.randint(2, 5)):
        asserts += (f"(assert {lit()})\n" if r.random() < .75
                    else f"(assert (or {lit()} {lit()}))\n")
    return decls, asserts


def run(c, p):
    try:
        out = subprocess.run([c, p], capture_output=True, text=True, timeout=20)
        return out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    decls, asserts = gen(random.Random(i))
    p = f"{OUT}/gm_{i}.smt2"
    open(p, "w").write(decls + asserts + "(check-sat)\n(get-model)\n")
    a, b = run(RS, p), run(Z3, p)
    if not a.startswith("sat\n"):
        return a.split("\n")[0] + "/" + b.split("\n")[0], p
    model = a[len("sat\n"):]
    defined = set(re.findall(r"\(define-fun (\S+) ", model))
    missing = [n for n in NAMES if n not in defined]
    # Validate: the model's definitions replace the declarations.
    body = model.strip()
    assert body.startswith("(") and body.endswith(")")
    keep = "".join(ln + "\n" for ln in decls.splitlines()
                   if re.search(r"declare-\w+ (\S+)", ln).group(1) in missing)
    chk = f"{OUT}/gm_{i}_check.smt2"
    open(chk, "w").write(keep + body[1:-1] + "\n" + asserts + "(check-sat)\n")
    v = run(Z3, chk).split("\n")[0]
    if v != "sat":
        return "BADMODEL", p
    if b.startswith("sat\n"):
        z3_defined = set(re.findall(r"\(define-fun (\S+) ", b))
        if z3_defined - defined:
            return "BADMODEL", p
    if missing:
        return "INCOMPLETE", p
    return ("MATCH" if a == b else "DIFF"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("BADMODEL", "INCOMPLETE"):
        print(k, p)
