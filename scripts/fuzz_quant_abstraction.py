#!/usr/bin/env python3
"""Differential soundness fuzz of nested quantifiers abstracted by predicates.

Universals whose bodies mention nested quantifiers in positions prenexing
cannot reach (under `=`/`xor`, both polarities), drawn from a small pool of
shapes reused with renamed bound variables across assertions (so
alpha-equivalent occurrences share one abstraction predicate), plus nested
universals in negative position (skolemized) and ground facts. A refutation
with the abstractions free must be a real one: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_quant_abstraction.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    cnt=[0]
    def fresh():
        cnt[0]+=1; return f"v{cnt[0]}"
    consts=["a","b","c"]
    def term(vs):
        c=r.random()
        if c<.3: return f"(f {r.choice(vs+consts)})"
        if c<.4: return f"(g {r.choice(vs+consts)} {r.choice(vs+consts)})"
        return r.choice(vs+consts)
    def atom(vs):
        c=r.random()
        if c<.35: return f"(p {term(vs)})"
        if c<.6: return f"(q {term(vs)} {term(vs)})"
        if c<.75: return f"(s {term(vs)})"
        return f"(= {term(vs)} {term(vs)})"
    # Nested-quantifier shapes over one free variable `X`, reused renamed.
    def shape():
        y=fresh(); q=r.choice(["forall","exists"])
        body=r.choice([f"(=> (q {y} X) (p {y}))",f"(or (s {y}) (q X {y}))",
                       f"(and (p {y}) (not (q {y} X)))",f"(=> (p (f {y})) (q X {y}))"])
        return q,y,body
    shapes=[shape() for _ in range(r.randint(1,3))]
    def nested(x):
        q,y,body=r.choice(shapes)
        y2=fresh()
        return f"({q} (({y2} U)) {body.replace(y,y2).replace('X',x)})"
    def form(vs,d):
        c=r.random()
        if d>=3 or c<.3: return atom(vs)
        if c<.5 and vs: return nested(r.choice(vs))
        if c<.6: return f"(not {form(vs,d+1)})"
        if c<.7: return f"(=> {form(vs,d+1)} {form(vs,d+1)})"
        if c<.8: return f"(= {form(vs,d+1)} {form(vs,d+1)})"
        if c<.9: return f"(and {form(vs,d+1)} {form(vs,d+1)})"
        return f"(or {form(vs,d+1)} {form(vs,d+1)})"
    a=["(declare-sort U 0)","(declare-fun f (U) U)","(declare-fun g (U U) U)",
       "(declare-fun p (U) Bool)","(declare-fun q (U U) Bool)","(declare-fun s (U) Bool)",
       "(declare-const a U)","(declare-const b U)","(declare-const c U)"]
    for _ in range(r.randint(2,5)):
        k=r.random()
        if k<.4:
            # A definition-like universal: an atom equivalent to a nested shape.
            v=fresh()
            a.append(f"(assert (forall (({v} U)) (= {atom([v])} {nested(v)})))")
        elif k<.7:
            v=fresh(); a.append(f"(assert (forall (({v} U)) {form([v],1)}))")
        else:
            a.append(f"(assert {form([],1)})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/qa_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
