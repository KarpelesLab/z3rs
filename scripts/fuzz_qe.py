#!/usr/bin/env python3
"""Differential fuzz of nested linear quantifiers (Real/Int) against z3.

Random formulas with alternating forall/exists over two free constants; only
definite sat/unsat answers are compared. Any DISAGREE is a soundness bug.

Usage: scripts/fuzz_qe.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    srt=r.choice(["Real","Real","Int"])
    free=["a","b"]
    def num(): k=r.randint(-3,3); return (f"{k}.0" if k>=0 else f"(- {-k}.0)") if srt=="Real" else (str(k) if k>=0 else f"(- {-k})")
    def lin(vs):
        ts=[f"(* {num()} {v})" for v in vs if r.random()<.6] or [r.choice(vs)]
        return f"(+ {' '.join(ts)} {num()})"
    def atom(vs): return f"({r.choice(['<','<=','=','>','>='])} {lin(vs)} {num()})"
    def fm(vs,d):
        c=r.random()
        if d>=3 or c<.3: return atom(vs)
        if c<.5: return f"(or {fm(vs,d+1)} {fm(vs,d+1)})"
        if c<.65: return f"(and {fm(vs,d+1)} {fm(vs,d+1)})"
        if c<.72: return f"(not {fm(vs,d+1)})"
        v=f"q{d}{r.randint(0,99)}"
        return f"({r.choice(['forall','exists'])} (({v} {srt})) {fm(vs+[v],d+1)})"
    a=[f"(declare-const {v} {srt})" for v in free]
    for _ in range(r.randint(1,2)): a.append(f"(assert {fm(free,0)})")
    a.append("(check-sat)")
    return "\n".join(a)+"\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    r=random.Random(i); src=gen(r); p=f"{OUT}/qe_{i}.smt2"; open(p,"w").write(src)
    if "forall" not in src and "exists" not in src: return "noq",p
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
