#!/usr/bin/env python3
"""Differential soundness fuzz of the EUF + linear arithmetic combination.

Random conjunctions/disjunctions over Int (or Real) constants, uninterpreted
functions `f : S -> S`, `g : S S -> S`, a predicate `p : S -> Bool` and an
`ite`, so congruence must exchange equalities with arithmetic (Nelson-Oppen
interface terms). Only definite answers are compared: a DISAGREE is a
soundness bug.

Usage: scripts/fuzz_uflia.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    S=r.choice(["Int","Int","Real"])
    vs=["a","b","c"]
    def num():
        k=r.randint(-2,3)
        s=f"{k}" if S=="Int" else f"{k}.0"
        return s if k>=0 else (f"(- {-k})" if S=="Int" else f"(- {-k}.0)")
    def term(d):
        k=r.random()
        if d>=3 or k<.35: return r.choice(vs) if r.random()<.8 else num()
        if k<.55: return f"(f {term(d+1)})"
        if k<.65: return f"(g {term(d+1)} {term(d+1)})"
        if k<.8: return f"(+ {term(d+1)} {term(d+1)})"
        if k<.88: return f"(- {term(d+1)} {num()})"
        if k<.94: return f"(* 2{'' if S=='Int' else '.0'} {term(d+1)})"
        return f"(ite {atom(d+1)} {term(d+1)} {term(d+1)})"
    def atom(d=0):
        k=r.random()
        if k<.1 and d<2: return f"(p {term(d+1)})"
        op=r.choice(["=","=","distinct","<","<=",">="])
        return f"({op} {term(d)} {term(d)})"
    def lit():
        a=atom()
        return a if r.random()<.75 else f"(not {a})"
    src="".join(f"(declare-const {v} {S})\n" for v in vs)
    src+=f"(declare-fun f ({S}) {S})\n(declare-fun g ({S} {S}) {S})\n(declare-fun p ({S}) Bool)\n"
    for _ in range(r.randint(2,5)):
        src+= f"(assert {lit()})\n" if r.random()<.7 else f"(assert (or {lit()} {lit()}))\n"
    return src+"(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/uf_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
