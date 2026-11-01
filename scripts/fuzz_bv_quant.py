#!/usr/bin/env python3
"""Differential soundness fuzz of quantified bit-vector formulas.

Random assertions over 4-bit bit-vectors and Booleans: universals whose
bodies may nest an existential (forall/exists alternation), existentials,
and ground facts over free constants c, d. Exercises the counterexample-
guided bit-vector instantiation. Only definite answers are compared: a
DISAGREE is a soundness bug.

Usage: scripts/fuzz_bv_quant.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    cnt=[0]
    def fresh():
        cnt[0]+=1; return f"q{cnt[0]}"
    def bv(vs,d=0):
        c=r.random()
        if d<2 and c<.35:
            op=r.choice(["bvadd","bvmul","bvand","bvor","bvxor","bvsub","bvlshr","bvshl"])
            return f"({op} {bv(vs,d+1)} {bv(vs,d+1)})"
        if c<.5: return f"#x{r.randrange(16):x}"
        return r.choice(vs+["c","d"])
    def atom(vs,bs):
        c=r.random()
        if c<.6: return f"({r.choice(['=','bvult','bvule','bvslt','bvsge','distinct'])} {bv(vs)} {bv(vs)})"
        return r.choice(bs+["p"])
    def form(vs,bs,d):
        c=r.random()
        if d>=3 or c<.35: return atom(vs,bs)
        if c<.5:
            v=fresh(); q=r.choice(["forall","exists"])
            if r.random()<.25: return f"({q} (({v} Bool)) {form(vs,bs+[v],d+1)})"
            return f"({q} (({v} (_ BitVec 4))) {form(vs+[v],bs,d+1)})"
        if c<.65: return f"(not {form(vs,bs,d+1)})"
        if c<.8: return f"(=> {form(vs,bs,d+1)} {form(vs,bs,d+1)})"
        return f"({r.choice(['and','or'])} {form(vs,bs,d+1)} {form(vs,bs,d+1)})"
    a=["(declare-const c (_ BitVec 4))","(declare-const d (_ BitVec 4))","(declare-const p Bool)"]
    for _ in range(r.randint(1,3)):
        if r.random()<.6:
            v=fresh(); a.append(f"(assert (forall (({v} (_ BitVec 4))) {form([v],[],1)}))")
        else:
            a.append(f"(assert {form([],[],1)})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/bq_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
