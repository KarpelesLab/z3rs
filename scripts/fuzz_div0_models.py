#!/usr/bin/env python3
"""Differential fuzz of division by possibly-zero terms: verdicts, models, eval.

Random small LIA / LRA problems over `div`, `mod` and `/` whose divisors are
variables, linear terms or the literal 0 (often forced to zero), followed by
`(get-model)` and an `(eval t)` of every division term (plus a few ground ones
such as `(div 5 0)`). In SMT-LIB (and z3) division by zero is an unspecified
but *functional* value: z3's `div0`/`mod0`/`/0`, functions of the dividend.

  DISAGREE  sat vs unsat against z3 (a soundness bug);
  BADMODEL  z3rs's model is not a model: z3 finds no `div0`/`mod0`/`/0`
            interpretation under which the constants of z3rs's model satisfy
            every assertion while each evaluated division takes the value
            z3rs's `eval` printed (so `get-model`/`eval` are inconsistent, or
            two zero divisions of equal dividends got different values);
  MATCH / DIFF  the whole output equals z3's byte for byte, or not (models
            are not unique, so DIFF is informational).

Usage: scripts/fuzz_div0_models.py <z3rs> <z3> <n> <outdir>
"""
import concurrent.futures
import random
import re
import subprocess
import sys
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]


def gen(r):
    real = r.random() < 0.4
    srt = "Real" if real else "Int"
    vs = [f"v{i}" for i in range(r.randint(2, 4))]

    def num(lo=-3, hi=5):
        k = r.randint(lo, hi)
        s = f"{k}.0" if real else str(k)
        s = s.lstrip("-")
        return f"(- {s})" if k < 0 else s

    def lin(d=0):
        c = r.random()
        if d >= 2 or c < 0.45:
            return r.choice(vs) if r.random() < 0.8 else num()
        if c < 0.7:
            return f"(+ {lin(d + 1)} {lin(d + 1)})"
        if c < 0.85:
            return f"(- {lin(d + 1)} {lin(d + 1)})"
        return f"(* {num(1, 3)} {lin(d + 1)})"

    def divisor():
        c = r.random()
        if c < 0.25:
            return "0.0" if real else "0"
        if c < 0.75:
            return r.choice(vs)
        return lin(1)

    divs = []

    def dterm():
        op = "/" if real else r.choice(["div", "mod", "div"])
        t = f"({op} {lin(1)} {divisor()})"
        divs.append(t)
        return t

    def term():
        c = r.random()
        if c < 0.55:
            return dterm()
        if c < 0.75:
            return f"(+ {dterm()} {lin(1)})"
        return lin()

    def atom():
        op = r.choice(["=", "=", "<", "<=", ">", ">=", "distinct"])
        return f"({op} {term()} {term()})"

    out = [f"(declare-fun {v} () {srt})" for v in vs]
    # Often force a divisor variable to zero.
    for v in vs:
        if r.random() < 0.35:
            out.append(f"(assert (= {v} {num(0, 0)}))")
    for _ in range(r.randint(1, 4)):
        out.append(f"(assert {atom()})")
    out.append("(check-sat)")
    out.append("(get-model)")
    extra = (
        ["(/ 5.0 0.0)", "(/ 0.0 0.0)"] if real else ["(div 5 0)", "(mod 5 0)", "(div 0 0)"]
    )
    evals = list(dict.fromkeys(divs)) + extra
    for t in evals:
        out.append(f"(eval {t})")
    return "\n".join(out) + "\n", vs, srt, evals


def run(cmd, p):
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=20).stdout
    except subprocess.TimeoutExpired:
        return "timeout"


def model_consts(text, vs):
    """The constant interpretations `(define-fun v () S val)` in a model."""
    vals = {}
    for v in vs:
        m = re.search(r"\(define-fun " + re.escape(v) + r" \(\) \w+\s+(.*?)\)\n", text, re.S)
        if m:
            vals[v] = m.group(1).strip()
    return vals


def one(i):
    p = f"{OUT}/dz_{i}.smt2"
    src, vs, srt, evals = gen(random.Random(i))
    open(p, "w").write(src)
    a, b = run(RS, p), run(Z3, p)
    va = a.split("\n")[0] if a else ""
    vb = b.split("\n")[0] if b else ""
    if va not in ("sat", "unsat") or vb not in ("sat", "unsat"):
        return f"{va}/{vb}", p
    if va != vb:
        return "DISAGREE", p
    if va == "unsat":
        return "agree", p
    # The eval lines are the last len(evals) output lines.
    lines = a.rstrip("\n").split("\n")
    if len(lines) < len(evals) + 2 or any(l.startswith("(error") for l in lines):
        return "BADMODEL", p
    evvals = lines[-len(evals):]
    consts = model_consts(a, vs)
    chk = [f"(declare-fun {v} () {srt})" for v in vs]
    chk += [l for l in src.split("\n") if l.startswith("(assert")]
    for v, x in consts.items():
        chk.append(f"(assert (= {v} {x}))")
    for t, x in zip(evals, evvals):
        chk.append(f"(assert (= {t} {x}))")
    chk.append("(check-sat)")
    q = f"{OUT}/dz_{i}.check.smt2"
    open(q, "w").write("\n".join(chk) + "\n")
    r = run(Z3, q).strip()
    if r != "sat":
        return "BADMODEL", p
    return ("MATCH" if a == b else "DIFF"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL"):
        print(k, p)
