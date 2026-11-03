#!/usr/bin/env python3
"""Differential soundness fuzz of range-restricted integer universals.

Random problems with universals `forall k. lo <= k < hi => phi(k)` (also
written as negated conjunctions and disjunctions) whose bounds are ground
terms (integer constants, sequence lengths), over arrays, functions and
sequences read at `k`, plus ground constraints on the bounds. Definite
verdicts are compared with z3: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_range_quant.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    def bound(): return r.choice(["0","1","n","m","(seq.len s)","(+ n 1)","(- m 1)"])
    def val(k): return r.choice([f"(select a {k})",f"(f {k})",f"(seq.nth s {k})","n",k,f"(+ {k} 1)"])
    def c(): return str(r.randint(-1,3))
    def atom(k): return f"({r.choice(['<','<=','=','>','distinct'])} {val(k)} {r.choice([c(),val(k)])})"
    def body(k):
        x=r.random()
        if x<.3: return atom(k)
        if x<.5: return f"(and {atom(k)} {atom(k)})"
        return f"(or {atom(k)} {atom(k)})"
    def quant():
        lo,hi=bound(),bound()
        g=f"(and (<= {lo} k) (< k {hi}))"
        x=r.random()
        if x<.5: q=f"(forall ((k Int)) (=> {g} {body('k')}))"
        elif x<.75: q=f"(forall ((k Int)) (or (< k {lo}) (>= k {hi}) {body('k')}))"
        else: q=f"(not (exists ((k Int)) (and {g} (not {body('k')}))))"
        return q
    def ground():
        return f"({r.choice(['<','<=','=','>'])} {r.choice(['n','m','(seq.len s)',val(r.choice(['0','1','n']))])} {r.choice([c(),'n','m'])})"
    a=["(declare-const a (Array Int Int))","(declare-fun f (Int) Int)","(declare-const s (Seq Int))",
       "(declare-const n Int)","(declare-const m Int)","(assert (<= 0 n 4))","(assert (<= 0 m 4))"]
    a+=[f"(assert {quant()})" for _ in range(r.randint(1,2))]
    a+=[f"(assert {ground()})" for _ in range(r.randint(0,3))]
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/rq_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
