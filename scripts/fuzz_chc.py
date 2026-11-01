#!/usr/bin/env python3
"""Differential soundness fuzz of multi-predicate linear CHC systems.

Random Horn systems over 2-3 unary/binary integer predicates: facts with
constant initial states, linear transitions (`P(x,y) ∧ g ⇒ Q(x+a, y+b)`),
recursion, and queries `P(x,y) ∧ g ⇒ false`. Only definite answers are
compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_chc.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    ar=r.choice([1,2])
    ps=["P","Q","R"][:r.randint(2,3)]
    vs=["x","y"][:ar]; ws=["u","w"][:ar]
    def guard(v):
        x=r.choice(v); k=r.randint(-3,5)
        return r.choice([f"(>= {x} {k})",f"(<= {x} {k})",f"(< {x} {k})",f"(= {x} {k})",
                         f"(not (= {x} {k}))" if r.random()<.3 else f"(>= {x} {k})"] +
                        ([f"(<= {v[0]} {v[1]})",f"(< {v[1]} {v[0]})"] if ar==2 else []))
    def upd(x):
        c=r.random()
        if c<.5: return f"(+ {x} {r.randint(-2,2)})"
        if c<.7: return str(r.randint(-2,4))
        if c<.85 and ar==2: return f"(+ {r.choice(vs)} {r.choice(vs)})"
        return x
    decl=" ".join(["Int"]*ar)
    lines=["(set-logic HORN)"]+[f"(declare-fun {p} ({decl}) Bool)" for p in ps]
    bind=" ".join(f"({v} Int)" for v in vs)
    bind2=" ".join(f"({v} Int)" for v in vs+ws)
    rules=[]
    for _ in range(r.randint(1,2)):
        p=r.choice(ps); init=" ".join(str(r.randint(-2,3)) for _ in vs)
        rules.append(f"(assert (forall ({bind}) (=> (and {' '.join(f'(= {v} {i})' for v,i in zip(vs,init.split()))}) ({p} {' '.join(vs)}))))")
    for _ in range(r.randint(2,5)):
        a,b=r.choice(ps),r.choice(ps)
        g=" ".join(guard(vs) for _ in range(r.randint(0,2)))
        eqs=" ".join(f"(= {w} {upd(v)})" for v,w in zip(vs,ws))
        rules.append(f"(assert (forall ({bind2}) (=> (and ({a} {' '.join(vs)}) {g} {eqs}) ({b} {' '.join(ws)}))))")
    for _ in range(r.randint(1,2)):
        p=r.choice(ps); g=" ".join(guard(vs) for _ in range(r.randint(1,2)))
        rules.append(f"(assert (forall ({bind}) (=> (and ({p} {' '.join(vs)}) {g}) false)))")
    return "\n".join(lines+rules)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/chc_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
