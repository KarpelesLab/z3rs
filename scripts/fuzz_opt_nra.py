#!/usr/bin/env python3
"""Differential fuzz of nonlinear real optimization against z3.

Random 1-2 variable polynomial problems (optionally with a Boolean disjunction)
with one objective. Flags sat/unsat disagreements (VERDICT) and objective values
that differ where both solvers give one (VALUE-DIFF). z3 sometimes prints an
interval where z3rs gives the exact value; those are counted separately.

Usage: scripts/fuzz_opt_nra.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    vs=["x","y"][:r.randint(1,2)]
    num=lambda: (lambda k: f"{k}.0" if k>=0 else f"(- {-k}.0)")(r.randint(-4,4))
    def term(d=0):
        c=r.random()
        if d>1 or c<.3: return r.choice(vs+[num()])
        if c<.6: return f"(* {term(d+1)} {term(d+1)})"
        if c<.85: return f"(+ {term(d+1)} {term(d+1)})"
        return f"(- {term(d+1)} {term(d+1)})"
    a=[f"(declare-const {v} Real)" for v in vs]
    if r.random()<.3: a.append("(declare-const b Bool)")
    for _ in range(r.randint(1,3)):
        at=f"({r.choice(['<=','<','>=','>','='])} {term()} {num()})"
        if "b" in a[-1] or any("Bool" in x for x in a):
            if r.random()<.4: at=f"(or (and b {at}) (and (not b) ({r.choice(['<=','>='])} {term()} {num()})))"
        a.append(f"(assert {at})")
    a.append(f"({r.choice(['maximize','minimize'])} {term(1)})")
    a.append("(check-sat)(get-objectives)")
    return "\n".join(a)+"\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=30).stdout
    except subprocess.TimeoutExpired: return "TIMEOUT"
def one(i):
    r=random.Random(i); src=gen(r); p=f"{OUT}/nra_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    if a==b: return "same",p
    va,vb=a.split("\n")[0],b.split("\n")[0]
    if {va,vb}=={"sat","unsat"}: return "VERDICT",p
    if va!="sat" or vb!="sat": return f"{va}/{vb}",p
    la=a.split("\n")[2]; lb=b.split("\n")[2]
    if "unknown" in la: return "rs-unknown-val",p
    if "interval" in lb or "unknown" in lb: return "z3-interval",p
    return "VALUE-DIFF",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in ("VERDICT","VALUE-DIFF"): print(k,p)
