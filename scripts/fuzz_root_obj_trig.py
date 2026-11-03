#!/usr/bin/env python3
"""Differential soundness fuzz of `root-obj` constants and sin/cos purification.

Random conjunctions of polynomial atoms over reals x, y, `(root-obj p i)`
constants and — under `(check-sat-using qfnra-nlsat)` — `sin`/`cos` of a real
`t` used nowhere else (z3's purify-arith turns them into a point of the unit
circle). Only definite answers are compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_root_obj_trig.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
ROOTS=["(root-obj (+ (^ x 2) (- 2)) 1)","(root-obj (+ (^ x 2) (- 2)) 2)",
       "(root-obj (+ (* 2 (^ x 2)) (- 1)) 2)","(root-obj (+ (^ x 3) (- 2)) 1)",
       "(root-obj (+ (* 4 (^ x 2)) (- 3)) 1)","(root-obj (+ (^ x 2) (- 1)) 2)"]
def gen(r):
    trig=r.random()<.5
    vs=["x","y"]+(["(sin t)","(cos t)"] if trig else [])
    def num():
        k=r.random()
        if k<.35: return r.choice(ROOTS)
        n=r.choice([0,1,2,3,0.5]); return f"{float(n)}" if r.random()<.7 else f"(- {float(n)})"
    def mono():
        fs=[r.choice(vs) for _ in range(r.randint(0,2))]
        return f"(* {num()} {' '.join(fs)})" if fs else num()
    def poly(): return f"(+ {' '.join(mono() for _ in range(r.randint(1,3)))})"
    def atom():
        op=r.choice(["<","<=","=","=",">",">=","distinct"])
        return f"({op} {poly()} {poly() if r.random()<.3 else '0.0'})"
    src="(declare-const x Real)\n(declare-const y Real)\n(declare-const t Real)\n"
    src+="".join(f"(assert {atom()})\n" for _ in range(r.randint(1,3)))
    src+="(check-sat-using qfnra-nlsat)\n" if trig else "(check-sat)\n"
    return src
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/ro_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
