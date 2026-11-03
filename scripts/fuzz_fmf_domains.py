#!/usr/bin/env python3
"""Differential fuzz of finite model finding over enumerated sorts.

Each uninterpreted sort is bounded the way verification encodings do it: an
injective map into a small integer range (`∀u v. f u = f v ⇒ u = v`,
`∀u. 1 ≤ f u ≤ n`) and named constants pinned to distinct values (or a
`distinct`), so the sort has a known finite size. On top: random universals
over predicates and functions of those sorts, nested quantifiers under `=`
(both polarities), and ground facts. Verdicts are compared with z3
(DISAGREE = soundness bug).

Usage: scripts/fuzz_fmf_domains.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    out=[]
    sorts=["A","B"][:r.randint(1,2)]
    consts={}
    for s in sorts:
        n=r.randint(2,6)
        out.append(f"(declare-sort {s} 0)")
        out.append(f"(declare-fun {s}2int ({s}) Int)")
        cs=[f"{s.lower()}{i}" for i in range(n)]
        consts[s]=cs
        for c in cs: out.append(f"(declare-const {c} {s})")
        out.append(f"(assert (forall ((u {s}) (v {s})) (=> (= ({s}2int u) ({s}2int v)) (= u v))))")
        hi=n+r.choice([0,0,1])
        out.append(f"(assert (forall ((u {s})) (and (<= 1 ({s}2int u)) (<= ({s}2int u) {hi}))))")
        if r.random()<.7:
            for i,c in enumerate(cs): out.append(f"(assert (= ({s}2int {c}) {i+1}))")
        else:
            out.append(f"(assert (distinct {' '.join(cs)}))")
    preds=[]
    for i in range(r.randint(1,3)):
        dom=[r.choice(sorts) for _ in range(r.randint(1,2))]
        out.append(f"(declare-fun p{i} ({' '.join(dom)}) Bool)"); preds.append((f"p{i}",dom))
    funs=[]
    for i in range(r.randint(0,2)):
        d=r.choice(sorts); rg=r.choice(sorts+["Int"])
        out.append(f"(declare-fun f{i} ({d}) {rg})"); funs.append((f"f{i}",d,rg))
    out.append("(declare-const k Int)")
    cnt=[0]
    def term(s,vs):
        opts=[v for v,vs_ in vs if vs_==s]+consts[s]
        fs=[f for f in funs if f[2]==s]
        if fs and r.random()<.3:
            f=r.choice(fs); return f"({f[0]} {term(f[1],vs)})"
        return r.choice(opts)
    def atom(vs):
        c=r.random()
        if c<.5:
            p,dom=r.choice(preds); return f"({p} {' '.join(term(s,vs) for s in dom)})"
        if c<.7:
            s=r.choice(sorts); return f"(= {term(s,vs)} {term(s,vs)})"
        ints=[f for f in funs if f[2]=="Int"]
        if ints and c<.85:
            f=r.choice(ints); return f"({r.choice(['<','<=','='])} ({f[0]} {term(f[1],vs)}) {r.choice(['k',str(r.randint(0,3))])})"
        s=r.choice(sorts); return f"(< ({s}2int {term(s,vs)}) {r.randint(1,4)})"
    def form(vs,d):
        c=r.random()
        if d>=3 or c<.35: return atom(vs)
        if c<.45:
            cnt[0]+=1; v=f"x{cnt[0]}"; s=r.choice(sorts)
            return f"({r.choice(['forall','exists'])} (({v} {s})) {form(vs+[(v,s)],d+1)})"
        if c<.55: return f"(not {form(vs,d+1)})"
        if c<.65: return f"(= {form(vs,d+1)} {form(vs,d+1)})"
        if c<.75: return f"(=> {form(vs,d+1)} {form(vs,d+1)})"
        if c<.88: return f"(and {form(vs,d+1)} {form(vs,d+1)})"
        return f"(or {form(vs,d+1)} {form(vs,d+1)})"
    for _ in range(r.randint(1,4)):
        if r.random()<.6:
            cnt[0]+=1; v=f"y{cnt[0]}"; s=r.choice(sorts)
            out.append(f"(assert (forall (({v} {s})) {form([(v,s)],1)}))")
        else:
            out.append(f"(assert {form([],1)})")
    return "\n".join(out)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/fmf_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
