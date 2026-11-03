#!/usr/bin/env python3
"""Differential fuzz of quantified UF/LIA (MBQI) against z3.

Random universals over Int and an uninterpreted sort U, with functions f, g, h
and predicates p, q, plus ground assertions. Flags definite sat/unsat
disagreements (DISAGREE).

Usage: scripts/fuzz_mbqi.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    a=["(declare-sort U 0)","(declare-fun f (Int) Int)","(declare-fun g (U) U)","(declare-fun p (Int) Bool)","(declare-fun q (U) Bool)","(declare-fun h (U) Int)"]
    a+=["(declare-const c Int)","(declare-const d Int)","(declare-const u U)","(declare-const v U)"]
    def it(vs,d=0):
        ch=r.random()
        if d>1 or ch<.35: return r.choice(vs+["c","d",str(r.randint(-2,3))])
        if ch<.55: return f"(f {it(vs,d+1)})"
        if ch<.7: return f"(h {ut([],d+1)})"
        return f"(+ {it(vs,d+1)} {it(vs,d+1)})"
    def ut(uvs,d=0):
        if d>1 or r.random()<.5: return r.choice(uvs+["u","v"])
        return f"(g {ut(uvs,d+1)})"
    def at(vs,uvs):
        ch=r.random()
        if ch<.25: return f"(p {it(vs)})"
        if ch<.4: return f"(q {ut(uvs)})"
        if ch<.55: return f"(= {ut(uvs)} {ut(uvs)})"
        if ch<.75: return f"({r.choice(['<=','<','='])} {it(vs)} {it(vs)})"
        return f"(= (h {ut(uvs)}) {it(vs)})"
    def fm(vs,uvs,d=0):
        ch=r.random()
        if d>1 or ch<.5: return at(vs,uvs)
        if ch<.7: return f"(or {fm(vs,uvs,d+1)} {fm(vs,uvs,d+1)})"
        if ch<.85: return f"(not {fm(vs,uvs,d+1)})"
        return f"(and {fm(vs,uvs,d+1)} {fm(vs,uvs,d+1)})"
    for _ in range(r.randint(1,2)):
        if r.random()<.5: a.append(f"(assert (forall ((x Int)) {fm(['x'],[])}))")
        else: a.append(f"(assert (forall ((y U)) {fm([],['y'])}))")
    for _ in range(r.randint(1,3)): a.append(f"(assert {fm([],[])})")
    a.append("(check-sat)")
    return "\n".join(a)+"\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    r=random.Random(i+100000); src=gen(r); p=f"{OUT}/q_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
