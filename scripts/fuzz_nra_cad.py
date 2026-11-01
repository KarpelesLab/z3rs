#!/usr/bin/env python3
"""Differential soundness fuzz of polynomial real arithmetic (CAD/nlsat).

Random conjunctions of 1-3 polynomial atoms (<, <=, =, distinct, ...) over
2-3 reals, with products of up to three factors so leading coefficients can
vanish. Only definite answers are compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_nra_cad.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    vs=[f"x{i}" for i in range(r.randint(2,3))]
    def num(): k=r.randint(-3,3); return f"{k}.0" if k>=0 else f"(- {-k}.0)"
    def mono():
        fs=[r.choice(vs) for _ in range(r.randint(0,3))]
        return f"(* {num()} {' '.join(fs)})" if fs else num()
    def poly(): return f"(+ {' '.join(mono() for _ in range(r.randint(1,3)))})"
    def atom():
        op=r.choice(["<","<=","=","distinct",">",">=","="])
        return f"({op} {poly()} 0.0)"
    a=[f"(declare-const {v} Real)" for v in vs]
    a+= [f"(assert {atom()})" for _ in range(r.randint(1,3))]
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/cad_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
