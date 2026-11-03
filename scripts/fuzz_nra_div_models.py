#!/usr/bin/env python3
"""Model-validation fuzz of nonlinear real arithmetic with division.

Same generator as fuzz_nra_div.py. Whenever z3rs answers `sat`, its model is
substituted for the declarations (`define-fun`) and z3 re-checks the
assertions: anything but `sat` is a wrong model (BADMODEL). Division by zero
is unspecified, so the replay keeps a model's literal `(/ t 0)` values free;
z3 picks them, and a genuine model always replays `sat`.

Usage: scripts/fuzz_nra_div_models.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    vs=[f"r{i}" for i in range(r.randint(2,5))]
    def num():
        k=r.choice([0,1,2,3,7,0.5,0.9,13]); s=f"{float(k)}"
        return s if r.random()<.7 else f"(- {s})"
    def term(d):
        c=r.random()
        if d>=3 or c<.3: return r.choice(vs) if r.random()<.75 else num()
        if c<.5: return f"(* {term(d+1)} {term(d+1)})"
        if c<.7: return f"(/ {term(d+1)} {term(d+1)})"
        if c<.85: return f"(+ {term(d+1)} {term(d+1)})"
        return f"(- {term(d+1)} {term(d+1)})"
    def atom():
        op=r.choice(["<","<=",">",">=","=","distinct"])
        return f"({op} {term(0)} {term(1)})"
    asserts=[f"(assert {atom()})" for _ in range(r.randint(1,3))]
    return vs,asserts
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    r=random.Random(i); vs,asserts=gen(r)
    decls="\n".join(f"(declare-const {v} Real)" for v in vs)
    p=f"{OUT}/m_{i}.smt2"
    out=run(RS,decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n(get-model)\n",p)
    if not out.startswith("sat"): return "skip",p
    defs=re.findall(r"\(define-fun (\S+) \(\) Real\s+(.*?)\)\n",out[4:],re.S)
    if not defs: return "nomodel",p
    q=f"{OUT}/m_{i}_replay.smt2"
    src="\n".join(f"(define-fun {n} () Real {v.strip()})" for n,v in defs)
    src+="\n"+"\n".join(f"(declare-const {v} Real)" for v in vs if v not in dict(defs))
    src+="\n"+"\n".join(asserts)+"\n(check-sat)\n"
    z=run(Z3,src,q).strip()
    return ("ok" if z=="sat" else "BADMODEL" if z=="unsat" else "z3:"+z[:20]),q
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="BADMODEL": print(k,p)
