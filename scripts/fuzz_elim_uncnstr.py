#!/usr/bin/env python3
"""Differential fuzz of z3's `elim-uncnstr` tactic.

Random small goals over bit-vector, integer, real and Boolean constants
(several occurring once, so the tactic has something to eliminate), using
the operators the tactic handles (n-ary `bvadd`/`bvmul`/`bvor`, `bvnot`,
`concat`, `extract`, `bvudiv`/`bvsdiv`, `bvule`/`bvsle`, `+`, `*`, `<=`,
`>=`, `ite`, `not`, `and`, `or`, `=`) and some it does not, with an
occasional quantifier. Each goal runs

    (apply elim-uncnstr)
    (check-sat-using (then elim-uncnstr smt))
    (get-model)

and is classified as:

  DISAGREE    z3rs and z3 give different sat/unsat verdicts (soundness)
  BADMODEL    z3rs's model, asserted back with the goal, is unsat under z3
  MATCH       the whole output is byte-for-byte z3's
  APPLY-DIFF  the `(apply …)` goal differs from z3's
  MODEL-DIFF  only the (valid) model differs
  OTHER       anything else (timeouts, unknown, errors)

Usage: scripts/fuzz_elim_uncnstr.py <z3rs> <z3> <n> <outdir> [seed-offset]
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
    w = r.choice([4, 8])
    bvs = ["x", "y", "z", "u"]
    ints = ["i", "j"]
    reals = ["a", "b"]
    bools = ["p", "q"]

    def bvlit(width=None):
        width = width or w
        v = r.randrange(1 << width)
        if width % 4 == 0 and r.random() < .8:
            return "#x" + format(v, "0%dx" % (width // 4))
        return f"(_ bv{v} {width})"

    def bv(d):
        k = r.random()
        if d >= 3 or k < .35:
            return r.choice(bvs) if r.random() < .8 else bvlit()
        op = r.choice(["bvadd", "bvadd", "bvmul", "bvmul", "bvor", "bvand",
                       "bvnot", "bvneg", "bvsub", "bvudiv", "bvsdiv", "bvxor",
                       "bvshl", "concat", "extract", "ite", "bvurem"])
        if op in ("bvadd", "bvmul", "bvor", "bvand", "bvxor"):
            n = r.choice([2, 2, 3])
            return f"({op} {' '.join(bv(d + 1) for _ in range(n))})"
        if op in ("bvnot", "bvneg"):
            return f"({op} {bv(d + 1)})"
        if op == "concat":
            h = w // 2
            return (f"(concat ((_ extract {h - 1} 0) {bv(d + 1)}) "
                    f"((_ extract {w - 1} {h}) {bv(d + 1)}))")
        if op == "extract":
            return f"((_ zero_extend {w // 2}) ((_ extract {w // 2 - 1} 0) {bv(d + 1)}))"
        if op == "ite":
            return f"(ite {boolean(d + 1)} {bv(d + 1)} {bv(d + 1)})"
        return f"({op} {bv(d + 1)} {bv(d + 1)})"

    def arith(d, srt):
        vs = ints if srt == "Int" else reals
        k = r.random()
        if d >= 3 or k < .4:
            if r.random() < .8:
                return r.choice(vs)
            n = r.randint(0, 5)
            if srt == "Real" and r.random() < .5:
                return f"{n}.0" if r.random() < .5 else f"(/ {n + 1}.0 2.0)"
            return str(n)
        op = r.choice(["+", "+", "*", "*", "-", "ite"])
        if op == "ite":
            return f"(ite {boolean(d + 1)} {arith(d + 1, srt)} {arith(d + 1, srt)})"
        if op == "*" and r.random() < .5:
            c = r.choice(["2", "3", "(- 1)"]) if srt == "Int" else r.choice(["2.0", "0.5", "3.0"])
            return f"(* {c} {arith(d + 1, srt)})"
        n = r.choice([2, 2, 3])
        return f"({op} {' '.join(arith(d + 1, srt) for _ in range(n))})"

    def boolean(d):
        k = r.random()
        if d >= 3 or k < .15:
            return r.choice(bools)
        if k < .45:
            op = r.choice(["=", "=", "bvule", "bvsle", "bvult", "distinct"])
            return f"({op} {bv(d + 1)} {bv(d + 1)})"
        if k < .7:
            srt = r.choice(["Int", "Real"])
            op = r.choice(["=", "<=", ">=", "<"])
            return f"({op} {arith(d + 1, srt)} {arith(d + 1, srt)})"
        op = r.choice(["not", "and", "or", "=", "ite", "=>"])
        if op == "not":
            return f"(not {boolean(d + 1)})"
        if op == "ite":
            return f"(ite {boolean(d + 1)} {boolean(d + 1)} {boolean(d + 1)})"
        n = 2 if op in ("=", "=>") else r.choice([2, 3])
        return f"({op} {' '.join(boolean(d + 1) for _ in range(n))})"

    def quant():
        v = r.choice(["e", "f"])
        q = r.choice(["forall", "exists"])
        body = f"(= ({r.choice(['bvadd', 'bvor', 'bvashr'])} {r.choice(bvs)} {v}) {bv(2)})"
        return f"({q} (({v} (_ BitVec {w}))) {body})"

    decls = "".join(f"(declare-const {v} (_ BitVec {w}))\n" for v in bvs)
    decls += "".join(f"(declare-const {v} Int)\n" for v in ints)
    decls += "".join(f"(declare-const {v} Real)\n" for v in reals)
    decls += "".join(f"(declare-const {v} Bool)\n" for v in bools)
    asserts = []
    for _ in range(r.randint(1, 4)):
        asserts.append(quant() if r.random() < .08 else boolean(0))
    return decls, "".join(f"(assert {a})\n" for a in asserts)


def run(c, p):
    try:
        out = subprocess.run([c, p], capture_output=True, text=True, timeout=20)
        return out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        return "timeout"


def split(out):
    """The `(apply …)` goals, the verdict, and the model text."""
    m = re.match(r"(\(goals\n.*?\n\)\n)(\w+)\n(.*)", out, re.S)
    return (m.group(1), m.group(2), m.group(3)) if m else (None, None, None)


def one(i):
    decls, asserts = gen(random.Random(i))
    p = f"{OUT}/eu_{i}.smt2"
    open(p, "w").write(decls + asserts + "(apply elim-uncnstr)\n"
                       "(check-sat-using (then elim-uncnstr smt))\n(get-model)\n")
    a, b = run(RS, p), run(Z3, p)
    ga, va, ma = split(a)
    gb, vb, mb = split(b)
    if ga is None or gb is None:
        return "OTHER", p
    if va in ("sat", "unsat") and vb in ("sat", "unsat") and va != vb:
        return "DISAGREE", p
    if va == "sat" and ma.startswith("("):
        body = ma.strip()
        chk = f"{OUT}/eu_{i}_check.smt2"
        defined = set(re.findall(r"\(define-fun (\S+) ", body))
        keep = "".join(ln + "\n" for ln in decls.splitlines()
                       if ln.split()[1] not in defined)
        open(chk, "w").write(keep + body[1:-1] + "\n" + asserts + "(check-sat)\n")
        if run(Z3, chk).split("\n")[0] != "sat":
            return "BADMODEL", p
    if a == b:
        return "MATCH", p
    if ga != gb:
        return "APPLY-DIFF", p
    return ("MODEL-DIFF" if va == vb else "OTHER"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k in ("DISAGREE", "BADMODEL", "APPLY-DIFF", "OTHER"):
        print(k, p)
