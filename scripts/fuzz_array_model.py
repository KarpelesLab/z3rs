#!/usr/bin/env python3
"""Differential fuzz of `get-model` / `get-value` on ground array problems.

Random assertions over array constants `A B C : (Array Int Int)`, a Boolean-
valued `P : (Array Int Bool)`, index constants `i j k : Int` and a function
`f : Int -> Int`, built from `select`, `store`, constant arrays, array
equalities and linear arithmetic, then `(check-sat) (get-model)` and a
`get-value` of a few array reads and arrays. For every `sat` z3rs prints:

  DISAGREE    z3 says unsat (a soundness bug)
  BADMODEL    the model's `define-fun`s, asserted back with the assertions,
              are unsatisfiable under z3 (a soundness bug), or a `get-value`
              answer contradicts the model (also checked by z3)
  INCOMPLETE  a declared array or constant z3 interprets has no
              interpretation in z3rs's model
  MATCH       the output is byte-for-byte z3's
  DIFF        a complete, valid model that differs from z3's

Usage: scripts/fuzz_array_model.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset


def gen(r):
    arrs = ["A", "B", "C"]
    ints = ["i", "j", "k"]

    def num():
        return str(r.randint(0, 4))

    def idx(d=0):
        k = r.random()
        if k < .55:
            return r.choice(ints)
        if k < .85 or d > 1:
            return num()
        if k < .93:
            return f"(+ {r.choice(ints)} {num()})"
        return f"(f {idx(d + 1)})"

    def arr(d):
        k = r.random()
        if d >= 2 or k < .55:
            return r.choice(arrs)
        if k < .85:
            return f"(store {arr(d + 1)} {idx()} {val(d + 1)})"
        return f"((as const (Array Int Int)) {num()})"

    def val(d):
        k = r.random()
        if d >= 2 or k < .4:
            return num() if r.random() < .5 else r.choice(ints)
        if k < .85:
            return f"(select {arr(d + 1)} {idx()})"
        return f"(+ {val(d + 1)} {val(d + 1)})"

    def atom():
        k = r.random()
        if k < .3:
            return f"(= {arr(0)} {arr(0)})"
        if k < .4:
            return f"(select P {idx()})"
        if k < .45:
            return f"(= P (store P {idx()} {r.choice(['true', 'false'])}))"
        op = r.choice(["=", "=", "distinct", "<", "<=", ">="])
        return f"({op} {val(0)} {val(0)})"

    def lit():
        a = atom()
        return a if r.random() < .7 else f"(not {a})"

    decls = "".join(f"(declare-const {v} (Array Int Int))\n" for v in arrs)
    decls += "(declare-const P (Array Int Bool))\n"
    decls += "".join(f"(declare-const {v} Int)\n" for v in ints)
    decls += "(declare-fun f (Int) Int)\n"
    asserts = ""
    for _ in range(r.randint(2, 5)):
        asserts += (f"(assert {lit()})\n" if r.random() < .75
                    else f"(assert (or {lit()} {lit()}))\n")
    queries = [f"(select A {idx()})", f"(select B {idx()})", "A",
               f"(store C {idx()} {num()})"]
    return decls, asserts, queries


def run(c, p):
    try:
        out = subprocess.run([c, p], capture_output=True, text=True, timeout=20)
        return out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        return "timeout"


def split_value_pairs(s):
    """`((t1 v1)\\n (t2 v2))` -> [(t1, v1), ...] by paren matching."""
    s = s.strip()
    assert s.startswith("(") and s.endswith(")")
    s = s[1:-1]
    out, depth, start = [], 0, None
    for n, ch in enumerate(s):
        if ch == "(":
            if depth == 0:
                start = n
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                out.append(s[start + 1:n])
    pairs = []
    for item in out:
        # term then value: the term is the first balanced expression
        item = item.strip()
        if item.startswith("("):
            d = 0
            for n, ch in enumerate(item):
                d += ch == "("
                d -= ch == ")"
                if d == 0:
                    break
            pairs.append((item[:n + 1], item[n + 1:].strip()))
        else:
            t, v = item.split(None, 1)
            pairs.append((t, v.strip()))
    return pairs


def one(i):
    decls, asserts, queries = gen(random.Random(i))
    p = f"{OUT}/am_{i}.smt2"
    open(p, "w").write(decls + asserts + "(check-sat)\n(get-model)\n"
                       f"(get-value ({' '.join(queries)}))\n")
    a, b = run(RS, p), run(Z3, p)
    if not a.startswith("sat\n"):
        return a.split("\n")[0] + "/" + b.split("\n")[0], p
    if b.startswith("unsat"):
        return "DISAGREE", p
    m = re.match(r"sat\n(\(\n(?:.*\n)*?\))\n(\((?:.*\n)*.*\))\s*$", a)
    if not m:
        return "BADOUTPUT", p
    model, values = m.group(1), m.group(2)
    names = [re.search(r"declare-\w+ (\S+)", ln).group(1) for ln in decls.splitlines()]
    defined = set(re.findall(r"\(define-fun (\S+) ", model))
    missing = [n for n in names if n not in defined]
    body = model.strip()
    keep = "".join(ln + "\n" for ln in decls.splitlines()
                   if re.search(r"declare-\w+ (\S+)", ln).group(1) in missing)
    # The model's own auxiliary functions (`k!0`, …) are defined in it too.
    vals = "".join(f"(assert (= {t} {v}))\n" for t, v in split_value_pairs(values))
    chk = f"{OUT}/am_{i}_check.smt2"
    open(chk, "w").write(keep + body[1:-1] + "\n" + asserts + "(check-sat)\n")
    if run(Z3, chk).split("\n")[0] != "sat":
        return "BADMODEL", p
    chk2 = f"{OUT}/am_{i}_check2.smt2"
    open(chk2, "w").write(keep + body[1:-1] + "\n" + asserts + vals + "(check-sat)\n")
    if run(Z3, chk2).split("\n")[0] != "sat":
        return "BADVALUE", p
    if b.startswith("sat\n"):
        z3_defined = set(re.findall(r"\(define-fun (\S+) ", b))
        if any(n in z3_defined and n not in defined for n in names):
            return "INCOMPLETE", p
    return ("MATCH" if a == b else "DIFF"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "BADVALUE", "BADOUTPUT", "INCOMPLETE"):
        print(k, p)
