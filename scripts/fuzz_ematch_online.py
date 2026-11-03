#!/usr/bin/env python3
"""Differential soundness fuzz of E-matching inside the persistent DPLL(T) search.

Boogie-style quantified UF/LIA goals without MBQI (z3's `smt.mbqi false`, as in
crash.smt2), so z3rs refutes them by relevancy-guided E-matching inside one
search: universals over an uninterpreted sort `U` and `Int` with `:pattern`s,
mixing arithmetic (`f x > 0`, `f (g k) = k + 1`), functions with a Boolean
argument (`h b`, preprocessed into finite tables), term-level `ite`s (lifted),
predicates and equalities, plus ground facts. Each file is decided by z3 both as
written and with MBQI on (its default), so a z3rs `unsat` against a z3 `sat` in
either mode shows up as DISAGREE (a soundness bug); `unsat` where z3 is
`unknown` both ways is reported as `unsat/unknown` (unconfirmed, not a bug).

Usage: scripts/fuzz_ematch_online.py <z3rs> <z3> <n> <outdir>
"""
import random, subprocess, sys, concurrent.futures
from collections import Counter
RS, Z3, N, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]


def gen(r):
    us = ["a", "b", "c"]
    ks = ["i", "j", "n"]

    def uterm(vs, d=0):
        c = r.random()
        if d < 2 and c < .25:
            return f"(g {iterm([v for v in vs if v in ('k', 'm')], d + 1)})"
        if d < 2 and c < .35:
            return f"(h {bterm(vs, d + 1)})"
        if d < 2 and c < .45:
            return f"(sel {uterm(vs, d + 1)} {uterm(vs, d + 1)})"
        if d < 2 and c < .5:
            return f"(ite {batom(vs, d + 1)} {uterm(vs, d + 1)} {uterm(vs, d + 1)})"
        pool = [v for v in vs if v in ("x", "y")] + us
        return r.choice(pool)

    def iterm(vs, d=0):
        c = r.random()
        if d < 2 and c < .3:
            return f"(f {uterm(vs, d + 1)})"
        if d < 2 and c < .45:
            return f"(+ {iterm(vs, d + 1)} {r.randint(-2, 2)})"
        if d < 2 and c < .5:
            return f"(ite {batom(vs, d + 1)} {iterm(vs, d + 1)} {iterm(vs, d + 1)})"
        if d < 2 and c < .55:
            return f"(* {r.randint(-2, 3)} {iterm(vs, d + 1)})"
        pool = [v for v in vs if v in ("k", "m")] + ks
        return r.choice(pool) if r.random() < .8 else str(r.randint(-2, 3))

    def bterm(vs, d):
        return r.choice(["true", "false", batom(vs, d + 1)])

    def batom(vs, d=0):
        c = r.random()
        if c < .2:
            return f"(p {uterm(vs, d + 1)})"
        if c < .45:
            return f"({r.choice(['<', '<=', '>', '>='])} {iterm(vs, d + 1)} {iterm(vs, d + 1)})"
        if c < .65:
            return f"(= {iterm(vs, d + 1)} {iterm(vs, d + 1)})"
        if c < .8:
            return f"(= {uterm(vs, d + 1)} {uterm(vs, d + 1)})"
        return f"(q {bterm(vs, d + 1)} {uterm(vs, d + 1)})"

    def form(vs, d):
        c = r.random()
        if d >= 2 or c < .35:
            return batom(vs) if r.random() < .7 else f"(not {batom(vs)})"
        if c < .6:
            return f"(or {form(vs, d + 1)} {form(vs, d + 1)})"
        if c < .8:
            return f"(and {form(vs, d + 1)} {form(vs, d + 1)})"
        return f"(=> {form(vs, d + 1)} {form(vs, d + 1)})"

    out = ["(set-option :auto-config false)", "(set-option :smt.mbqi false)",
           "(declare-sort U 0)", "(declare-fun f (U) Int)", "(declare-fun g (Int) U)",
           "(declare-fun h (Bool) U)", "(declare-fun sel (U U) U)",
           "(declare-fun p (U) Bool)", "(declare-fun q (Bool U) Bool)"]
    out += [f"(declare-const {c} U)" for c in us]
    out += [f"(declare-const {c} Int)" for c in ks]
    # Universals: binders and a pattern covering them.
    shapes = [(["x"], "(f x)"), (["x"], "(p x)"), (["k"], "(g k)"),
              (["x", "y"], "(sel x y)"), (["x", "k"], "(f (sel x (g k)))"),
              (["x"], "(h (p x))")]
    for _ in range(r.randint(1, 4)):
        vs, pat = r.choice(shapes)
        binders = " ".join(f"({v} {'U' if v in ('x', 'y') else 'Int'})" for v in vs)
        body = form(vs, 0)
        if r.random() < .8:
            body = f"(! {body} :pattern ({pat}))"
        out.append(f"(assert (forall ({binders}) {body}))")
    for _ in range(r.randint(1, 5)):
        out.append(f"(assert {form([], 1)})")
    return "\n".join(out) + "\n(check-sat)\n"


def run(cmd, p):
    try:
        o = subprocess.run(cmd + [p], capture_output=True, text=True, timeout=20).stdout
        return (o.strip().split("\n") or ["?"])[0]
    except subprocess.TimeoutExpired:
        return "timeout"


def one(i):
    p = f"{OUT}/emo_{i}.smt2"
    src = gen(random.Random(i))
    open(p, "w").write(src)
    a = run([RS], p)
    b = run([Z3], p)
    pm = f"{OUT}/emo_{i}_mbqi.smt2"
    open(pm, "w").write(src.replace("(set-option :auto-config false)\n(set-option :smt.mbqi false)\n", ""))
    c = run([Z3], pm)
    zs = {b, c} & {"sat", "unsat"}
    if a in ("sat", "unsat") and zs:
        return ("agree" if zs == {a} else "DISAGREE"), p
    return f"{a}/{b}", p


res = list(concurrent.futures.ThreadPoolExecutor(8).map(one, range(N)))
print(Counter(k for k, _ in res))
for k, p in res:
    if k == "DISAGREE":
        print(k, p)
