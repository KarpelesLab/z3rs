#!/usr/bin/env python3
"""Differential soundness fuzz of bit-vector arrays.

Random conjunctions over free and constant arrays (Array (_ BitVec w) (_ BitVec 3)),
store chains, selects, and array/element (dis)equalities. Index widths 1-3 hit
the finite-domain extensionality expansion, width 5 the general path. Only
definite answers are compared: a DISAGREE is a soundness bug (a z3 `sat`
whose model z3's own model_validate rejects is reported separately).

Usage: scripts/fuzz_bv_array.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    w=r.choice([1,2,3,5])
    I=f"(_ BitVec {w})"; E="(_ BitVec 3)"; A=f"(Array {I} {E})"
    def idx(): return r.choice(["i","j",f"(_ bv{r.randrange(1<<w)} {w})"])
    def el(d=0):
        if d<2 and r.random()<.4: return f"(select {arr(d+1)} {idx()})"
        return r.choice(["x","y",f"(_ bv{r.randrange(8)} 3)"])
    def arr(d=0):
        c=r.random()
        if d<2 and c<.45: return f"(store {arr(d+1)} {idx()} {el(d+1)})"
        if c<.65: return f"((as const {A}) {el(2)})"
        return r.choice(["a","b"])
    def atom():
        c=r.random()
        if c<.4: return f"(= {arr()} {arr()})"
        if c<.55: return f"(not (= {arr()} {arr()}))"
        if c<.85: return f"(= {el()} {el()})"
        return f"(distinct {el()} {el()})"
    a=[f"(declare-const {v} {A})" for v in "ab"]
    a+=[f"(declare-const {v} {I})" for v in "ij"]
    a+=[f"(declare-const {v} {E})" for v in "xy"]
    a+=[f"(assert {atom()})" for _ in range(r.randint(1,4))]
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/ba_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"):
        if a==b: return "agree",p
        # z3 occasionally returns a model it cannot validate itself.
        if b=="sat" and "invalid model" in subprocess.run([Z3,"model_validate=true",p],capture_output=True,text=True,timeout=20).stdout:
            return "z3-invalid-model",p
        return "DISAGREE",p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
