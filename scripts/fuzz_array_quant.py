#!/usr/bin/env python3
"""Differential soundness fuzz of universals over read-only arrays.

Arrays Int -> Int that are only ever read (`select` of a declared constant)
under universals with range guards over Int binders, plus ground facts on
array cells, lengths and an uninterpreted sort variant. Exercises the
arrays-as-functions reduction with E-matching and MBQI. With `--models`
(default on) the z3rs `get-value` of the read cells is checked against the
assertions by z3. A DISAGREE or BADMODEL is a soundness bug.

Usage: scripts/fuzz_array_quant.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures,re
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    arrs=["a","b","c"]
    ints=["n","m","k"]
    def idx(vs):
        c=r.random()
        if vs and c<.5: v=r.choice(vs); return v if r.random()<.6 else f"(+ {v} {r.randint(-2,2)})"
        if c<.75: return str(r.randint(-1,4))
        return r.choice(ints)
    def val(vs):
        c=r.random()
        if c<.6: return f"(select {r.choice(arrs)} {idx(vs)})"
        if c<.8: return str(r.randint(-3,5))
        return r.choice(ints+vs) if vs else r.choice(ints)
    def atom(vs):
        op=r.choice(["=","<=","<",">="])
        return f"({op} {val(vs)} {val(vs)})"
    def form(vs,d):
        c=r.random()
        if d>=2 or c<.4: return atom(vs) if r.random()<.75 else f"(not {atom(vs)})"
        if c<.65: return f"(and {form(vs,d+1)} {form(vs,d+1)})"
        if c<.9: return f"(or {form(vs,d+1)} {form(vs,d+1)})"
        return f"(=> {form(vs,d+1)} {form(vs,d+1)})"
    a=["(set-option :produce-models true)"]
    a+=[f"(declare-const {x} (Array Int Int))" for x in arrs]
    a+=[f"(declare-const {x} Int)" for x in ints]
    for _ in range(r.randint(1,3)):
        lo,hi=r.choice(["0","1",r.choice(ints)]),r.choice(ints+["3"])
        guard=f"(and (<= {lo} x) (< x {hi}))"
        a.append(f"(assert (forall ((x Int)) (=> {guard} {form(['x'],1)})))")
    for _ in range(r.randint(1,4)):
        a.append(f"(assert {form([],1)})")
    cells=" ".join(f"(select {x} {i})" for x in arrs for i in range(0,3))
    return "\n".join(a)+f"\n(check-sat)\n(get-value (n m k {cells}))\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip()
    except subprocess.TimeoutExpired: return "timeout"
def check_model(src,vals,p):
    # Pin the reported values and ask z3 whether the assertions still hold.
    pins=re.findall(r"\(((?:\(select \w+ \d+\))|\w+) (\(- \d+\)|-?\d+)\)",vals)
    if not pins: return True
    body=src.split("(check-sat)")[0]
    extra="".join(f"(assert (= {t} {v}))\n" for t,v in pins)
    q=p+".check.smt2"; open(q,"w").write(body+extra+"(check-sat)\n")
    return run(Z3,q).split("\n")[0]!="unsat"
def one(i):
    src=gen(random.Random(i)); p=f"{OUT}/aq_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    a0,b0=a.split("\n")[0],b.split("\n")[0]
    if a0 in("sat","unsat") and b0 in("sat","unsat"):
        if a0!=b0: return "DISAGREE",p
        if a0=="sat" and not check_model(src,a,p): return "BADMODEL",p
        return "agree",p
    return f"{a0}/{b0}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
