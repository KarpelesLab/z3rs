#!/usr/bin/env python3
"""Differential fuzz of `(simplify …)` on arithmetic, Boolean and bit-vector terms.

Random terms over Int/Real/Bool/(_ BitVec 8) constants are simplified by z3rs
and z3 and the printed results compared byte for byte. A simplification of a
Boolean term to opposite truth values is a soundness bug (WRONG); any other
textual difference is reported as DIFF, bucketed by the head symbol of the
input term so the most common categories stand out. One simplify per script.

Usage: scripts/fuzz_simplify.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random, subprocess, sys, concurrent.futures
from collections import Counter

RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
# Odd seed offsets also draw signed division, rotations, extracts,
# extensions, concatenations and bit-vector ite.
WIDE = OFF % 2 == 1
HDR = (
    "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n"
    "(declare-const a Real)\n(declare-const b Real)\n"
    "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n"
    "(declare-const u (_ BitVec 8))\n(declare-const v (_ BitVec 8))\n"
    "(declare-fun f (Int) Int)\n"
)


def gen(r):
    def num():
        return r.choice(["0", "1", "2", "3", "5", "(- 1)", "(- 2)"])

    def rnum():
        return r.choice(["0.0", "1.0", "2.0", "0.5", "(/ 1.0 3.0)", "(- 1.0)"])

    def it(d):
        c = r.random()
        if d > 2 or c < 0.3:
            return r.choice(["x", "y", "z", num(), "x", "y"])
        if c < 0.45:
            return f"(+ {' '.join(it(d+1) for _ in range(r.randint(2, 3)))})"
        if c < 0.55:
            return f"(* {it(d+1)} {it(d+1)})"
        if c < 0.63:
            return f"(- {it(d+1)} {it(d+1)})"
        if c < 0.67:
            return f"(- {it(d+1)})"
        if c < 0.73:
            return f"(ite {bt(d+1)} {it(d+1)} {it(d+1)})"
        if c < 0.78:
            return f"(div {it(d+1)} {r.choice(['1', '2', '3', 'y'])})"
        if c < 0.83:
            return f"(mod {it(d+1)} {r.choice(['1', '2', '3', 'y'])})"
        if c < 0.88:
            return f"(f {it(d+1)})"
        if c < 0.92:
            return f"(abs {it(d+1)})"
        return f"(* {num()} {it(d+1)})"

    def rt(d):
        c = r.random()
        if d > 2 or c < 0.35:
            return r.choice(["a", "b", rnum(), "a"])
        if c < 0.55:
            return f"(+ {rt(d+1)} {rt(d+1)})"
        if c < 0.7:
            return f"(* {rt(d+1)} {rt(d+1)})"
        if c < 0.8:
            return f"(- {rt(d+1)} {rt(d+1)})"
        if c < 0.88:
            return f"(/ {rt(d+1)} {r.choice(['2.0', '3.0', 'b'])})"
        return f"(to_real {it(d+1)})"

    def bv(d):
        c = r.random()
        if d > 2 or c < 0.35:
            return r.choice(["u", "v", "#x00", "#x01", "#xff", "#x0f", "u"])
        ops = ["bvadd", "bvmul", "bvand", "bvor", "bvxor", "bvsub", "bvshl", "bvlshr", "bvudiv", "bvurem"]
        if WIDE:
            ops += ["bvashr", "bvsdiv", "bvsrem", "bvsmod", "bvnand", "bvnor", "bvxnor"]
        if c < 0.75:
            return f"({r.choice(ops)} {bv(d+1)} {bv(d+1)})"
        if WIDE and c < 0.8:
            k = r.randint(0, 7)
            return f"((_ {r.choice(['rotate_left', 'rotate_right'])} {k}) {bv(d+1)})"
        if WIDE and c < 0.85:
            lo = r.randint(0, 7)
            hi = r.randint(lo, 7)
            n = 8 - (hi - lo + 1)
            ext = r.choice(["zero_extend", "sign_extend"])
            inner = f"((_ extract {hi} {lo}) {bv(d+1)})"
            if n == 0:
                return inner
            if r.random() < 0.5:
                return f"((_ {ext} {n}) {inner})"
            return f"(concat {bvk(n, d)} {inner})"
        if WIDE and c < 0.88:
            return f"(ite {bt(d+1)} {bv(d+1)} {bv(d+1)})"
        if c < 0.92:
            return f"(bvnot {bv(d+1)})"
        return f"(bvneg {bv(d+1)})"

    def bvk(n, d):
        """A bit-vector term of width n (1..7)."""
        c = r.random()
        if c < 0.4:
            return "#b" + "".join(r.choice("01") for _ in range(n))
        lo = r.randint(0, 8 - n)
        return f"((_ extract {lo + n - 1} {lo}) {bv(d+1)})"

    def bt(d):
        c = r.random()
        if d > 2 or c < 0.2:
            return r.choice(["p", "q", "r", "true", "false", "p"])
        if c < 0.3:
            return f"(and {' '.join(bt(d+1) for _ in range(r.randint(2, 3)))})"
        if c < 0.4:
            return f"(or {' '.join(bt(d+1) for _ in range(r.randint(2, 3)))})"
        if c < 0.45:
            return f"(not {bt(d+1)})"
        if c < 0.5:
            return f"(=> {bt(d+1)} {bt(d+1)})"
        if c < 0.53:
            return f"(xor {bt(d+1)} {bt(d+1)})"
        if c < 0.56:
            return f"(ite {bt(d+1)} {bt(d+1)} {bt(d+1)})"
        if c < 0.66:
            op = r.choice(["<=", "<", ">=", ">", "="])
            return f"({op} {it(d+1)} {it(d+1)})"
        if c < 0.72:
            op = r.choice(["<=", "<", ">=", ">", "="])
            return f"({op} {rt(d+1)} {rt(d+1)})"
        if c < 0.8:
            op = r.choice(["bvule", "bvult", "bvsle", "bvslt", "="])
            return f"({op} {bv(d+1)} {bv(d+1)})"
        if c < 0.84:
            return f"(distinct {it(d+1)} {it(d+1)})"
        return f"(= {bt(d+1)} {bt(d+1)})"

    k = r.random()
    if k < 0.35:
        return it(0)
    if k < 0.5:
        return rt(0)
    if k < 0.65:
        return bv(0)
    return bt(0)


def run(c, p):
    try:
        return subprocess.run([c, p], capture_output=True, text=True, timeout=20).stdout.strip()
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    r = random.Random(i)
    t = gen(r)
    p = f"{OUT}/simp_{i}.smt2"
    open(p, "w").write(HDR + f"(simplify {t})\n")
    a, b = run(RS, p), run(Z3, p)
    head = t.split()[0].lstrip("(") if t.startswith("(") else "atom"
    if a == b:
        return "same", p, head
    if {a, b} == {"true", "false"}:
        return "WRONG", p, head
    return "DIFF", p, head


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _, _ in res))
print("DIFF by head:", Counter(h for k, _, h in res if k == "DIFF").most_common())
for k, p, _ in res:
    if k != "same":
        print(k, p)
