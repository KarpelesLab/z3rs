#!/usr/bin/env python3
"""Differential soundness fuzz of arrays indexed by Bool.

Arrays `(Array Bool Int)` / `(Array Bool Bool)` (and one nested
`(Array Bool (Array Int Int))`) read and updated at symbolic Bool indices —
constants and formulas such as `(< x 2)` — compared by `=`/`distinct`, with
integer side constraints. A DISAGREE is a soundness bug.

Usage: scripts/fuzz_bool_array.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    def bidx():
        c=r.random()
        if c<.5: return r.choice(["p","q","s"])
        if c<.7: return r.choice(["true","false"])
        return f"(< {r.choice(['x','y'])} {r.randint(-1,3)})"
    def iarr(d=0):
        c=r.random()
        if d<2 and c<.35: return f"(store {iarr(d+1)} {bidx()} {ival(d+1)})"
        if d<2 and c<.45: return f"(ite {bidx()} {iarr(d+1)} {iarr(d+1)})"
        if c<.55: return f"((as const (Array Bool Int)) {r.randint(0,3)})"
        return r.choice(["A","B"])
    def ival(d=0):
        c=r.random()
        if d<3 and c<.5: return f"(select {iarr(d+1)} {bidx()})"
        if d<3 and c<.6: return f"(select (select N {bidx()}) {r.randint(0,2)})"
        if c<.8: return str(r.randint(0,3))
        return r.choice(["x","y"])
    def barr(d=0):
        if d<2 and r.random()<.3: return f"(store {barr(d+1)} {bidx()} {bidx()})"
        return r.choice(["P","Q"])
    def atom():
        c=r.random()
        if c<.35: return f"(= {ival()} {ival()})"
        if c<.55: return f"(= {iarr()} {iarr()})"
        if c<.65: return f"(distinct {iarr()} {iarr()} {iarr()})"
        if c<.8: return f"(select {barr()} {bidx()})"
        if c<.9: return f"(= {barr()} {barr()})"
        return f"(<= {ival()} {ival()})"
    def form(d=0):
        c=r.random()
        if d>=2 or c<.4: return atom() if r.random()<.7 else f"(not {atom()})"
        return f"({r.choice(['and','or','=>'])} {form(d+1)} {form(d+1)})"
    a=["(declare-const p Bool)","(declare-const q Bool)","(declare-const s Bool)",
       "(declare-const x Int)","(declare-const y Int)",
       "(declare-const A (Array Bool Int))","(declare-const B (Array Bool Int))",
       "(declare-const P (Array Bool Bool))","(declare-const Q (Array Bool Bool))",
       "(declare-const N (Array Bool (Array Int Int)))"]
    for _ in range(r.randint(1,4)):
        a.append(f"(assert {form()})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/ba_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
