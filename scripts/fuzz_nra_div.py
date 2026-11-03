#!/usr/bin/env python3
"""Differential soundness fuzz of nonlinear real arithmetic with division.

Random conjunctions over 2-5 reals mixing products, division by variables or
products (unspecified at zero, as in SMT-LIB), comparisons and disequalities.
Only definite sat/unsat answers are compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_nra_div.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    vs=[f"r{i}" for i in range(r.randint(2,5))]
    def num():
        k=r.choice([0,1,2,3,7,0.5,0.9,13]); s=f"{float(k)}"
        return s if r.random()<.7 else f"(- {s})"
    def term(d):
        c=r.random()
        if d>=3 or c<.3: return r.choice(vs) if r.random()<.75 else num()
        if c<.5: return f"(* {term(d+1)} {term(d+1)})"
        if c<.7: return f"(/ {term(d+1)} {term(d+1)})"
        if c<.85: return f"(+ {term(d+1)} {term(d+1)})"
        return f"(- {term(d+1)} {term(d+1)})"
    def atom():
        op=r.choice(["<","<=",">",">=","=","distinct"])
        return f"({op} {term(0)} {term(1)})"
    a=[f"(declare-const {v} Real)" for v in vs]
    for _ in range(r.randint(1,3)): a.append(f"(assert {atom()})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/nd_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
