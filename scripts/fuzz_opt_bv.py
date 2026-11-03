#!/usr/bin/env python3
"""Differential fuzz of bit-vector objectives against z3.

Random problems over two or three small bit-vector constants (widths 3-5):
hard constraints built from unsigned/signed comparisons over `bvadd`,
`bvsub`, `bvmul`, `bvand`, `bvor`, `bvxor`, `bvlshr`, 1-3 `minimize` /
`maximize` objectives over such terms (optimized as unsigned numbers), under
`opt.priority` lex or box, sometimes with an `assert-soft`. The values are
checked against brute force over every assignment (BAD-VALUE), the lex model
of `get-value` against the hard constraints and the reported values
(BAD-MODEL), and the verdict (BAD-VERDICT). Output that differs from z3's
only in the model is model-diff; anything else is DIFF.

Usage: scripts/fuzz_opt_bv.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random, re, subprocess, sys, itertools, concurrent.futures
from collections import Counter
RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset


def gen(r):
    w = r.randint(3, 5)
    M = 1 << w
    vs = ["a", "b", "c"][: r.randint(2, 3 if w <= 4 else 2)]
    lit = lambda k: f"(_ bv{k % M} {w})"
    sgn = lambda v: v - M if v >= M // 2 else v

    def term(d=0):
        if d > 1 or r.random() < .35:
            if r.random() < .75:
                v = r.choice(vs)
                return (lambda e, v=v: e[v]), v
            k = r.randrange(M)
            return (lambda e, k=k: k), lit(k)
        op = r.choice(["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvlshr"])
        (fa, sa), (fb, sb) = term(d + 1), term(d + 1)
        f = {"bvadd": lambda x, y: (x + y) % M, "bvsub": lambda x, y: (x - y) % M,
             "bvmul": lambda x, y: (x * y) % M, "bvand": lambda x, y: x & y,
             "bvor": lambda x, y: x | y, "bvxor": lambda x, y: x ^ y,
             "bvlshr": lambda x, y: x >> y if y < w else 0}[op]
        return (lambda e, f=f, fa=fa, fb=fb: f(fa(e), fb(e))), f"({op} {sa} {sb})"

    def atom():
        op = r.choice(["bvule", "bvult", "bvsle", "bvslt", "="])
        (fa, sa), (fb, sb) = term(), term()
        f = {"bvule": lambda x, y: x <= y, "bvult": lambda x, y: x < y,
             "bvsle": lambda x, y: sgn(x) <= sgn(y), "bvslt": lambda x, y: sgn(x) < sgn(y),
             "=": lambda x, y: x == y}[op]
        g = lambda e, f=f, fa=fa, fb=fb: f(fa(e), fb(e))
        if r.random() < .25:
            return (lambda e, g=g: not g(e)), f"(not ({op} {sa} {sb}))"
        return g, f"({op} {sa} {sb})"

    pri = r.choice(["lex", "lex", "box"])
    src = [f"(set-option :opt.priority {pri})"] + [f"(declare-const {v} (_ BitVec {w}))" for v in vs]
    hard = [atom() for _ in range(r.randint(1, 3))]
    src += [f"(assert {s})" for _, s in hard]
    objs = []
    for _ in range(r.randint(1, 3)):
        if r.random() < .2:
            f, s = atom()
            wt = r.randint(1, 3)
            src.append(f"(assert-soft {s} :weight {wt} :id s{len(objs)})")
            objs.append(("soft", f, wt))
            continue
        f, s = term(1)
        mx = r.random() < .5
        objs.append(("term", f, mx))
        src.append(f"({'maximize' if mx else 'minimize'} {s})")
    src.append("(check-sat)(get-objectives)")
    src.append(f"(get-value ({' '.join(vs)}))")
    pts = [dict(zip(vs, x)) for x in itertools.product(range(M), repeat=len(vs))]
    pts = [e for e in pts if all(f(e) for f, _ in hard)]

    def val(o, e):  # smaller is better
        if o[0] == "soft":
            return 0 if o[1](e) else o[2]
        return -o[1](e) if o[2] else o[1](e)

    shown = lambda o, v: -v if o[0] == "term" and o[2] else v
    exp = None
    if pts:
        if pri == "lex":
            cur, exp = pts, []
            for o in objs:
                best = min(val(o, e) for e in cur)
                cur = [e for e in cur if val(o, e) == best]
                exp.append(shown(o, best))
        else:
            exp = [shown(o, min(val(o, e) for e in pts)) for o in objs]
    return "\n".join(src) + "\n", exp, objs, hard, vs, pri, val, shown


def run(cmd, p):
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def bvval(s):
    s = s.strip()
    if s.startswith("#x"):
        return int(s[2:], 16)
    if s.startswith("#b"):
        return int(s[2:], 2)
    try:
        return int(s)
    except ValueError:
        return None


def one(i):
    r = random.Random(i)
    src, exp, objs, hard, vs, pri, val, shown = gen(r)
    p = f"{OUT}/bv_{i}.smt2"
    open(p, "w").write(src)
    a, b = run(RS, p), run(Z3, p)
    lines = a.split("\n")
    verdict = lines[0]
    if verdict in ("sat", "unsat") and (verdict == "sat") != (exp is not None):
        return "BAD-VERDICT", p
    if verdict == "sat":
        got = [bvval(ln.strip()[1:-1].split()[-1]) for ln in lines[2:2 + len(objs)]]
        if got != exp:
            return "BAD-VALUE", p
        if pri == "lex":
            model = {}
            for v in vs:
                m = re.search(rf"\({v} (#[xb][0-9a-f]+)\)", a)
                if not m:
                    return "BAD-MODEL", p
                model[v] = bvval(m.group(1))
            if not all(f(model) for f, _ in hard) or [shown(o, val(o, model)) for o in objs] != exp:
                return "BAD-MODEL", p
    if a == b:
        return "same", p
    if not b.strip():
        return "z3-crash", p
    if verdict not in ("sat", "unsat"):
        return "rs-" + verdict, p
    head = lambda o: o.split("\n")[:3 + len(objs)]
    return ("model-diff" if head(a) == head(b) else "DIFF"), p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k not in ("same", "model-diff"):
        print(k, p)
