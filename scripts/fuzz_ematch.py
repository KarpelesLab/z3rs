#!/usr/bin/env python3
"""Differential soundness fuzz of E-matching saturation over an uninterpreted sort.

Universals over U with one or two binders whose bodies mix uninterpreted
applications covering only some binders (`p(x)` beside `r(x, y)`), binders in
interpreted positions (`x = c`, `x ≠ f(y)`), optional user `:pattern`s, and
ground facts with equalities, sometimes without MBQI. A `sat` claimed from an E-matching fixpoint that
missed a needed instance shows up as a DISAGREE (a soundness bug).

Usage: scripts/fuzz_ematch.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    consts=["a","b","c","d"]
    def term(vs,d=0):
        c=r.random()
        if d<2 and c<.3: return f"(f {term(vs,d+1)})"
        if d<2 and c<.4: return f"(g {term(vs,d+1)} {term(vs,d+1)})"
        return r.choice(vs+consts) if vs and r.random()<.7 else r.choice(consts)
    def atom(vs):
        c=r.random()
        if c<.3: return f"(p {term(vs)})"
        if c<.45: return f"(q {term(vs)})"
        if c<.65: return f"(r {term(vs)} {term(vs)})"
        return f"(= {term(vs)} {term(vs)})"
    def form(vs,d):
        c=r.random()
        if d>=2 or c<.35: return atom(vs) if r.random()<.7 else f"(not {atom(vs)})"
        if c<.6: return f"(or {form(vs,d+1)} {form(vs,d+1)})"
        if c<.85: return f"(and {form(vs,d+1)} {form(vs,d+1)})"
        return f"(=> {form(vs,d+1)} {form(vs,d+1)})"
    a=["(set-option :auto-config false)","(set-option :smt.mbqi false)"] if r.random()<.3 else []
    a+=["(declare-sort U 0)","(declare-fun f (U) U)","(declare-fun g (U U) U)",
       "(declare-fun p (U) Bool)","(declare-fun q (U) Bool)","(declare-fun r (U U) Bool)"]
    a+=[f"(declare-const {k} U)" for k in consts]
    for _ in range(r.randint(1,3)):
        vs=["x"] if r.random()<.5 else ["x","y"]
        body=form(vs,0)
        binders=" ".join(f"({v} U)" for v in vs)
        if r.random()<.3:
            pat=f"(r x {vs[-1]})" if len(vs)==2 or r.random()<.5 else "(f x)"
            if len(vs)==2 and r.random()<.5: pat=f"(g x y)"
            body=f"(! {body} :pattern ({pat}))"
        a.append(f"(assert (forall ({binders}) {body}))")
    for _ in range(r.randint(1,4)):
        a.append(f"(assert {form([],1)})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/em_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE" or k.startswith("sat/"): print(k,p)
