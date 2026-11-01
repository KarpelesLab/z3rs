#!/usr/bin/env python3
"""Differential soundness fuzz of nested quantifiers over an uninterpreted sort.

Random assertions over a sort U with a function f, predicates p and r and
constants a, b: universals whose bodies nest further universals and
existentials in both polarities (under not, =>, or, ite), plus ground facts.
Exercises prenexing, skolemization, sentinels and finite model finding.
Only definite answers are compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_nested_quant.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    cnt=[0]
    def fresh():
        cnt[0]+=1; return f"v{cnt[0]}"
    def term(vs):
        c=r.random()
        if c<.25: return f"(f {term(vs)})" if r.random()<.5 else f"(f {r.choice(vs+['a','b'])})"
        return r.choice(vs+["a","b"])
    def atom(vs):
        c=r.random()
        if c<.35: return f"(p {term(vs)})"
        if c<.6: return f"(r {term(vs)} {term(vs)})"
        return f"(= {term(vs)} {term(vs)})"
    def form(vs,d):
        c=r.random()
        if d>=3 or c<.3: return atom(vs)
        if c<.45:
            v=fresh(); q=r.choice(["forall","exists"])
            return f"({q} (({v} U)) {form(vs+[v],d+1)})"
        if c<.6: return f"(not {form(vs,d+1)})"
        if c<.75: return f"(=> {form(vs,d+1)} {form(vs,d+1)})"
        if c<.88: return f"(or {form(vs,d+1)} {form(vs,d+1)})"
        return f"(ite {atom(vs)} {form(vs,d+1)} {form(vs,d+1)})"
    a=["(declare-sort U 0)","(declare-fun f (U) U)","(declare-fun p (U) Bool)",
       "(declare-fun r (U U) Bool)","(declare-const a U)","(declare-const b U)"]
    for _ in range(r.randint(1,4)):
        if r.random()<.6:
            v=fresh(); a.append(f"(assert (forall (({v} U)) {form([v],1)}))")
        else:
            a.append(f"(assert {form([],1)})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/nq_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
