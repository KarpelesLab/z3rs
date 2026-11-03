#!/usr/bin/env python3
"""Differential fuzz of MaxSMT (`assert-soft`) and mixed objectives against z3.

Random small problems over bounded Int and Bool constants: hard linear
constraints, 2-6 `assert-soft`s with integer or decimal weights grouped by
optional `:id`s, sometimes a `minimize`/`maximize`, under `opt.priority`
lex or box and a random `opt.maxsat_engine`. Every objective is checked
against brute force over the whole box (BAD-VALUE), and for lex the model of
`get-value` must satisfy the hard constraints and attain the reported values
(BAD-MODEL); a verdict differing from the brute-force one is BAD-VERDICT.
Output that differs from z3's only in the model is model-diff; z3 optimum
that brute force refutes (seen with some MaxSAT engines) is z3-wrong;
anything else is DIFF.

Usage: scripts/fuzz_opt_soft.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random, re, subprocess, sys, itertools, concurrent.futures
from fractions import Fraction as F
from collections import Counter
RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
c = lambda k: str(k) if k >= 0 else f"(- {-k})"
ENGINES = ["maxres", "wmax", "pd-maxres", "rc2", "maxres-bin", "maxresw"]


def gen(r):
    ivs = ["x", "y"][: r.randint(1, 2)]
    bvs = ["p", "q"][: r.randint(0, 2)]
    box = {v: (lo := r.randint(-3, 1), lo + r.randint(1, 4)) for v in ivs}

    def lin():
        cs = [(r.randint(-2, 2), v) for v in ivs]
        return cs, "(+ " + " ".join(f"(* {c(k)} {v})" for k, v in cs) + ")"

    def atom():
        if bvs and r.random() < .35:
            b = r.choice(bvs)
            return (lambda e, b=b: e[b]), b
        cs, t = lin()
        op = r.choice(["<=", ">=", "=", "<"])
        k = r.randint(-4, 4)
        f = {"<=": lambda a, b: a <= b, ">=": lambda a, b: a >= b,
             "=": lambda a, b: a == b, "<": lambda a, b: a < b}[op]
        return (lambda e, cs=cs, f=f, k=k: f(sum(a * e[v] for a, v in cs), k)), f"({op} {t} {c(k)})"

    def lit():
        f, s = atom()
        if r.random() < .3:
            return (lambda e, f=f: not f(e)), f"(not {s})"
        return f, s

    def clause():
        ls = [lit() for _ in range(r.randint(1, 2))]
        if len(ls) == 1:
            return ls[0]
        return (lambda e, ls=ls: any(f(e) for f, _ in ls)), "(or " + " ".join(s for _, s in ls) + ")"

    pri = r.choice(["lex", "lex", "box"])
    eng = r.choice(ENGINES)
    src = [f"(set-option :opt.priority {pri})", f"(set-option :opt.maxsat_engine {eng})"]
    src += [f"(declare-const {v} Int)" for v in ivs] + [f"(declare-const {b} Bool)" for b in bvs]
    src += [f"(assert (<= {c(lo)} {v} {c(hi)}))" for v, (lo, hi) in box.items()]
    hard = [clause() for _ in range(r.randint(0, 2))]
    src += [f"(assert {s})" for _, s in hard]
    # objectives in creation order: ("soft", id) groups and ("term", ...)
    objs, groups = [], {}
    nsoft = r.randint(2, 6)
    term_at = r.randint(0, nsoft) if r.random() < .4 else -1
    for i in range(nsoft + 1):
        if i == term_at:
            cs, t = lin()
            mx = r.random() < .5
            objs.append(("term", cs, mx))
            src.append(f"({'maximize' if mx else 'minimize'} {t})")
        if i == nsoft:
            break
        f, s = clause()
        w = r.choice([1, 1, 2, 3, 5, F(3, 2), F(1, 4)])
        gid = r.choice(["", "", "a", "b"])
        ws = "" if w == 1 and r.random() < .5 else f" :weight {float(w) if w.denominator != 1 else int(w)}"
        ids = f" :id {gid}" if gid else ""
        if gid not in groups:
            groups[gid] = []
            objs.append(("soft", gid))
        groups[gid].append((f, F(w)))
        src.append(f"(assert-soft {s}{ws}{ids})")
    src.append("(check-sat)(get-objectives)")
    vs = ivs + bvs
    src.append(f"(get-value ({' '.join(vs)}))")
    pts = []
    for vals in itertools.product(*[range(box[v][0], box[v][1] + 1) for v in ivs],
                                  *[[False, True] for _ in bvs]):
        e = dict(zip(vs, vals))
        if all(f(e) for f, _ in hard):
            pts.append(e)

    def val(o, e):  # smaller is better
        if o[0] == "soft":
            return sum(w for f, w in groups[o[1]] if not f(e))
        _, cs, mx = o
        v = sum(a * e[x] for a, x in cs)
        return -v if mx else v

    def shown(o, v):
        return -v if o[0] == "term" and o[2] else v

    exp = None
    if pts:
        if pri == "lex":
            cur = pts
            exp = []
            for o in objs:
                best = min(val(o, e) for e in cur)
                cur = [e for e in cur if val(o, e) == best]
                exp.append(shown(o, best))
        else:
            exp = [shown(o, min(val(o, e) for e in pts)) for o in objs]
    return "\n".join(src) + "\n", exp, objs, groups, hard, vs, pri, val, shown


def run(cmd, p):
    try:
        return subprocess.run([cmd, p], capture_output=True, text=True, timeout=30).stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def num(s):
    s = s.strip()
    m = re.fullmatch(r"\(- (.*)\)", s)
    if m:
        v = num(m.group(1))
        return None if v is None else -v
    m = re.fullmatch(r"\(/ (\S+) (\S+)\)", s)
    if m:
        return F(m.group(1)) / F(m.group(2))
    try:
        return F(s)
    except ValueError:
        return None


def last_sexpr(s):
    """The last top-level s-expression of `s` (the value after a name)."""
    s = s.rstrip()
    if not s.endswith(")"):
        return s.split()[-1] if s.split() else ""
    depth = 0
    for k in range(len(s) - 1, -1, -1):
        depth += {")": 1, "(": -1}.get(s[k], 0)
        if depth == 0:
            return s[k:]
    return s


def one(i):
    r = random.Random(i)
    src, exp, objs, groups, hard, vs, pri, val, shown = gen(r)
    p = f"{OUT}/soft_{i}.smt2"
    open(p, "w").write(src)
    a, b = run(RS, p), run(Z3, p)
    lines = a.split("\n")
    verdict = lines[0]
    if verdict == "sat" or verdict == "unsat":
        if (verdict == "sat") != (exp is not None):
            return "BAD-VERDICT", p
    if verdict == "sat":
        got = []
        for ln in lines[2:2 + len(objs)]:
            got.append(num(last_sexpr(ln.strip()[1:-1])))
        if got != exp:
            return "BAD-VALUE", p
        if pri == "lex":
            model = {}
            for v in vs:
                m = re.search(rf"\({v} ([^()]+|\(- \d+\))\)", a)
                if not m:
                    return "BAD-MODEL", p
                t = m.group(1)
                model[v] = t == "true" if t in ("true", "false") else int(num(t))
            if not all(f(model) for f, _ in hard):
                return "BAD-MODEL", p
            if [shown(o, val(o, model)) for o in objs] != exp:
                return "BAD-MODEL", p
    if a == b:
        return "same", p
    if not b.strip():
        return "z3-crash", p
    if verdict not in ("sat", "unsat"):
        return "rs-" + verdict, p
    head = lambda o: o.split("\n")[:3 + len(objs)]
    if head(a) == head(b):
        return "model-diff", p  # both models were checked when lex
    zl = b.split("\n")
    if verdict == "sat" and zl[0] == "sat":
        zgot = [num(last_sexpr(ln.strip()[1:-1])) for ln in zl[2:2 + len(objs)]]
        if zgot != exp:
            return "z3-wrong", p  # z3's optimum differs from brute force
    return "DIFF", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(OFF, OFF + N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k != "same":
        print(k, p)
