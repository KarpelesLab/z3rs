#!/usr/bin/env python3
"""Differential soundness fuzz of the higher-order sequence operations.

Random conjunctions over a (Seq Int) variable `a`, a (Seq Int) `b` and an
Int `i`, built from seq.map / seq.mapi / seq.foldl / seq.foldli whose
function argument is an uninterpreted function, an array, or a macro,
plus units, concatenation, seq.len and seq.nth. Definite answers are
compared (DISAGREE = soundness bug); for a z3rs `sat`, each assertion is
re-evaluated under the model (`eval`), and a `false` is a BADMODEL.

Usage: scripts/fuzz_seq_hof.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
HDR="""(declare-const a (Seq Int))
(declare-const b (Seq Int))
(declare-const i Int)
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-fun h (Int Int Int) Int)
(declare-const F (Array Int Int))
(declare-const G (Array Int Int Int))
(define-fun inc ((x Int)) Int (+ x 1))
(define-fun add ((x Int) (y Int)) Int (+ x y))
(define-fun addi ((k Int) (x Int) (y Int)) Int (+ k x y))
"""
def gen(r):
    def num(): return r.choice(["0","1","2","3","i","(seq.len a)"])
    def base(d):
        c=r.random()
        if d<2 and c<.25: return f"(seq.++ {sq(d+1)} {sq(d+1)})"
        if c<.45: return f"(seq.unit {num()})"
        if c<.5: return "(as seq.empty (Seq Int))"
        return r.choice(["a","a","b"])
    def sq(d=0):
        c=r.random()
        if d<2 and c<.25: return f"(seq.map {r.choice(['f','F','inc'])} {base(d+1)})"
        if d<2 and c<.4: return f"(seq.mapi {r.choice(['g','G','add'])} {num()} {base(d+1)})"
        return base(d)
    def fold():
        if r.random()<.5:
            return f"(seq.foldl {r.choice(['g','G','add'])} {num()} {sq()})"
        return f"(seq.foldli {r.choice(['h','addi'])} {num()} {num()} {sq()})"
    def atom():
        c=r.random()
        if c<.3: return f"({r.choice(['=','distinct'])} {sq()} {sq()})"
        if c<.5: return f"({r.choice(['<','<=','=','>'])} (seq.len {sq()}) {num()})"
        if c<.7: return f"({r.choice(['=','distinct','<'])} {fold()} {num()})"
        return f"({r.choice(['=','distinct'])} (seq.nth {sq()} {num()}) {num()})"
    atoms=[atom() for _ in range(r.randint(1,4))]
    return atoms
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")
    except subprocess.TimeoutExpired: return ["timeout"]
def one(n):
    atoms=gen(random.Random(n))
    src=HDR+"".join(f"(assert {x})\n" for x in atoms)+"(check-sat)\n"
    p=f"{OUT}/hof_{n}.smt2"; open(p,"w").write(src)
    b=run(Z3,p)[0]
    pe=f"{OUT}/hof_{n}_eval.smt2"
    open(pe,"w").write(src+"".join(f"(eval {x})\n" for x in atoms))
    out=run(RS,pe)
    a=out[0]
    if a=="sat" and "false" in out[1:]: return "BADMODEL",pe
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
