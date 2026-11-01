#!/usr/bin/env python3
"""Differential fuzz of goals made of independent components.

Each goal conjoins atoms from separate families (integers with a nonlinear
twist, reals, an Int→Int uninterpreted function, an Int-indexed array, a
bit-vector, an FP) that share no symbols, so the component split decides
them one by one and merges the models. Definite verdicts are compared with
z3 (DISAGREE = soundness bug), and each z3rs `sat` model is replayed through
z3 by appending its `define-fun`s to the assertions (BADMODEL).

Usage: scripts/fuzz_components.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
DECLS=["(declare-fun n () Int)","(declare-fun m () Int)","(declare-fun x () Real)",
       "(declare-fun y () Real)","(declare-fun f (Int) Int)","(declare-fun k () Int)",
       "(declare-fun a () (Array Int Int))","(declare-fun j () Int)",
       "(declare-fun u () (_ BitVec 4))","(declare-fun g () (_ FloatingPoint 3 5))"]
def gen(r):
    fams=[
        lambda: f"({r.choice(['=','<','<=','distinct'])} (* n m) {r.randint(-6,12)})",
        lambda: f"({r.choice(['=','<','>='])} (+ n m) {r.randint(-3,5)})",
        lambda: f"({r.choice(['<','<=','='])} (* 2.0 x) (+ y {r.randint(-2,2)}.5))",
        lambda: f"(= (/ x {r.choice(['2.0','3.0'])}) y)",
        lambda: f"({r.choice(['=','distinct'])} (f {r.choice(['k','0','(+ k 1)'])}) {r.choice(['k','1','(f k)'])})",
        lambda: f"({r.choice(['=','distinct'])} (select a {r.choice(['j','1','(+ j 1)'])}) {r.choice(['j','2','(select a 0)'])})",
        lambda: f"({r.choice(['=','bvult','distinct'])} (bvmul u #x{r.randrange(16):x}) #x{r.randrange(16):x})",
        lambda: f"({r.choice(['fp.isNormal','fp.isSubnormal','fp.isNegative'])} g)",
        lambda: f"(fp.lt g ((_ to_fp 3 5) RNE {r.choice(['1.0','-0.5','3.0'])}))",
    ]
    return [f"(assert {r.choice(fams)()})" for _ in range(r.randint(2,6))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    asserts=gen(random.Random(i))
    src="\n".join(DECLS)+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/cp_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/cp_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        body=out[out.find("(",4):]
        defs=re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)",body,re.S)
        names=set(re.findall(r"\(define-fun (\S+)",body))
        if defs:
            decls=[d for d in DECLS if d.split()[1] not in names]
            rep="\n".join(decls+[d.strip() for d in defs]+asserts)+"\n(check-sat)\n"
            z=run(Z3,rep,f"{OUT}/cp_{i}_replay.smt2").strip()
            if z.startswith("unsat"): return "BADMODEL",p
            if "error" in z: return "REPLAY-ERROR",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL","REPLAY-ERROR"): print(k,p)
