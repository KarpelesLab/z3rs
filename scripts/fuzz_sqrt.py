#!/usr/bin/env python3
"""Differential soundness fuzz of square roots `(^ t 0.5)` over the reals.

Random conjunctions over reals x, y with bounds (often making the roots'
bases provably nonnegative) and polynomial atoms mixing `(^ b 0.5)` terms of
variables, numerals and small sums. Only definite answers are compared: a
DISAGREE is a soundness bug.

Usage: scripts/fuzz_sqrt.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    vs=["x","y"]
    def num(): return r.choice(["0.0","1.0","2.0","3.0","4.0","0.5","(- 1.0)","9.0"])
    def base():
        k=r.random()
        if k<.4: return r.choice(vs)
        if k<.6: return num()
        if k<.8: return f"(* {r.choice(['2.0','3.0','0.5'])} {r.choice(vs)})"
        return f"(+ {r.choice(vs)} {r.choice(vs)})"
    def term(d=0):
        k=r.random()
        if k<.35: return f"(^ {base()} 0.5)"
        if k<.55 or d>1: return r.choice(vs) if r.random()<.6 else num()
        if k<.75: return f"(* {term(d+1)} {term(d+1)})"
        return f"(+ {term(d+1)} {term(d+1)})"
    def atom():
        op=r.choice(["=","=","distinct","<",">=","<="])
        return f"({op} {term()} {term()})"
    src="(declare-const x Real)\n(declare-const y Real)\n"
    for v in vs:
        if r.random()<.7: src+=f"(assert (>= {v} {r.choice(['0.0','1.0','(- 1.0)'])}))\n"
    src+="".join(f"(assert {atom()})\n" for _ in range(r.randint(1,3)))
    return src+"(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/sq_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
