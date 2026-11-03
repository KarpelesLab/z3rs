#!/usr/bin/env python3
"""Differential soundness fuzz of records (single-constructor datatypes).

Two record variables with Bool / bit-vector / Int fields, constrained through
their selectors (fields as Boolean atoms, bit-vector and integer comparisons,
`ite` over fields), record equalities and constructor terms. The z3rs
`get-value` of every field is checked against the assertions by z3. A
DISAGREE or BADMODEL is a soundness bug.

Usage: scripts/fuzz_records.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures,re
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
FIELDS=[("b","Bool"),("v","(_ BitVec 4)"),("n","Int"),("w","(_ BitVec 1)")]
def gen(r):
    recs=["r","s"]
    def bv(x): return f"(v {x})" if r.random()<.7 else f"#x{r.randint(0,15):x}"
    def form(d=0):
        x=r.choice(recs); c=r.random()
        if d<2 and c<.25: return f"({r.choice(['and','or','=>'])} {form(d+1)} {form(d+1)})"
        if c<.3: return f"(not {form(d+1)})"
        if c<.45: return f"(b {x})"
        if c<.6: return f"({r.choice(['bvule','bvult','='])} {bv(x)} {bv(r.choice(recs))})"
        if c<.7: return f"(= (n {x}) {r.randint(-2,3)})"
        if c<.78: return f"(< (n {x}) (n {r.choice(recs)}))"
        if c<.85: return f"(= ((_ extract 0 0) (w {x})) (ite (b {x}) #b1 #b0))"
        if c<.92: return f"(= r s)"
        return f"(= {x} (mk {'true' if r.random()<.5 else 'false'} #x{r.randint(0,15):x} {r.randint(-1,2)} #b{r.randint(0,1)}))"
    a=["(set-option :produce-models true)",
       "(declare-datatype R ((mk "+" ".join(f"({f} {s})" for f,s in FIELDS)+")))",
       "(declare-const r R)","(declare-const s R)"]
    for _ in range(r.randint(1,4)):
        a.append(f"(assert {form()})")
    cells=" ".join(f"({f} {x})" for x in recs for f,_ in FIELDS)
    return "\n".join(a)+f"\n(check-sat)\n(get-value ({cells}))\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip()
    except subprocess.TimeoutExpired: return "timeout"
def check_model(src,vals,p):
    pins=re.findall(r"\((\(\w \w\)) (true|false|#x[0-9a-f]+|#b[01]+|\(- \d+\)|-?\d+)\)",vals)
    if not pins: return True
    body=src.split("(check-sat)")[0]
    q=p+".check.smt2"
    open(q,"w").write(body+"".join(f"(assert (= {t} {v}))\n" for t,v in pins)+"(check-sat)\n")
    return run(Z3,q).split("\n")[0]!="unsat"
def one(i):
    src=gen(random.Random(i)); p=f"{OUT}/rc_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    a0,b0=a.split("\n")[0],b.split("\n")[0]
    if a0 in("sat","unsat") and b0 in("sat","unsat"):
        if a0!=b0: return "DISAGREE",p
        if a0=="sat" and not check_model(src,a,p): return "BADMODEL",p
        return "agree",p
    return f"{a0}/{b0}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
