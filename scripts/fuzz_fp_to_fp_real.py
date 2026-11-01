#!/usr/bin/env python3
"""Differential fuzz of `((_ to_fp 3 5) rm r)` for constrained reals `r`.

Random linear bounds on reals `r`/`q`, conversions under constant rounding
modes, and FP atoms over the results (equalities with constants,
comparisons, classification). Definite verdicts are compared with z3
(DISAGREE = soundness bug), and every z3rs `sat` model is replayed through
z3 as define-funs (BADMODEL = wrong model).

Usage: scripts/fuzz_fp_to_fp_real.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
F="(_ FloatingPoint 3 5)"
DECLS=[("r","Real"),("q","Real"),("f",F)]
def gen(r):
    def rat():
        n=r.randint(-40,40); d=r.choice([1,2,4,8,16,3,10])
        return f"(/ {n}.0 {d}.0)" if n>=0 else f"(- (/ {-n}.0 {d}.0))"
    def conv():
        return f"((_ to_fp 3 5) {r.choice(['RNE','RNA','RTP','RTN','RTZ'])} {r.choice(['r','q','(+ r q)'])})"
    def fp():
        return r.choice([conv(),conv(),"f",f"((_ to_fp 3 5) RNE {rat()})"])
    def atom():
        c=r.random()
        if c<.35: return f"({r.choice(['<','<=','>','>=','='])} {r.choice(['r','q'])} {rat()})"
        if c<.65: return f"({r.choice(['=','fp.eq','fp.lt','fp.leq'])} {fp()} {fp()})"
        if c<.8: return f"({r.choice(['fp.isNormal','fp.isSubnormal','fp.isZero','fp.isInfinite','fp.isNegative'])} {fp()})"
        return f"(not (= {fp()} {fp()}))"
    return [f"(assert {atom()})" for _ in range(r.randint(2,5))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    asserts=gen(random.Random(i))
    decls="\n".join(f"(declare-const {n} {s})" for n,s in DECLS)
    src=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/tr_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/tr_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        defs=dict(re.findall(r"\(define-fun (\S+) \(\) (?:\(_ \S+ \d+(?: \d+)?\)|\S+)\s+(.*?)\)\n",out,re.S))
        if defs:
            rep="\n".join(f"(define-fun {n} () {s} {defs[n].strip()})" if n in defs else f"(declare-const {n} {s})" for n,s in DECLS)
            z=run(Z3,rep+"\n"+"\n".join(asserts)+"\n(check-sat)\n",f"{OUT}/tr_{i}_replay.smt2").strip()
            if z=="unsat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
