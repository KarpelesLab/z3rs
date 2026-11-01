#!/usr/bin/env python3
"""Differential soundness fuzz of quantified arithmetic.

Random assertions over free constants c, d (all Int or all Real per file):
universals whose bodies may nest an existential, existentials, and ground
facts; terms are linear with an occasional product. Exercises the
counterexample-guided instantiation over arithmetic binders. Only definite
answers are compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_arith_quant.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    S=r.choice(["Int","Real"]); cnt=[0]
    def num():
        k=r.randint(-4,6)
        s=f"{abs(k)}" if S=="Int" else f"{abs(k)}.0"
        return s if k>=0 else f"(- {s})"
    def fresh():
        cnt[0]+=1; return f"q{cnt[0]}"
    def term(vs,d=0):
        c=r.random()
        if d<2 and c<.3: return f"(+ {term(vs,d+1)} {term(vs,d+1)})"
        if d<2 and c<.4: return f"(* {num()} {term(vs,d+1)})"
        if d<1 and c<.45: return f"(* {r.choice(vs+['c','d'])} {r.choice(vs+['c','d'])})"
        if c<.6: return num()
        return r.choice(vs+["c","d"])
    def atom(vs):
        return f"({r.choice(['<','<=','=','>=','>','distinct'])} {term(vs)} {term(vs)})"
    def form(vs,d):
        c=r.random()
        if d>=3 or c<.35: return atom(vs)
        if c<.5:
            v=fresh(); q=r.choice(["forall","exists"])
            return f"({q} (({v} {S})) {form(vs+[v],d+1)})"
        if c<.62: return f"(not {form(vs,d+1)})"
        if c<.77: return f"(=> {form(vs,d+1)} {form(vs,d+1)})"
        return f"({r.choice(['and','or'])} {form(vs,d+1)} {form(vs,d+1)})"
    a=[f"(declare-const c {S})",f"(declare-const d {S})"]
    for _ in range(r.randint(1,3)):
        if r.random()<.6:
            v=fresh(); a.append(f"(assert (forall (({v} {S})) {form([v],1)}))")
        else:
            a.append(f"(assert {form([],1)})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/aq_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
