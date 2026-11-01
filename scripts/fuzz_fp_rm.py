#!/usr/bin/env python3
"""Differential fuzz of floating point under symbolic rounding modes.

Random (3,5)-float constraints (z3 folds fp.fma wrongly at 3 significand bits) whose operations take RoundingMode constants
(rm, rm2), plus mode (dis)equalities. Definite verdicts are compared with z3
(DISAGREE = soundness bug), and every z3rs `sat` model is replayed through z3
as define-funs (BADMODEL = wrong model).

Usage: scripts/fuzz_fp_rm.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
F="(_ FloatingPoint 3 5)"
DECLS=[("f",F),("g",F),("rm","RoundingMode"),("rm2","RoundingMode")]
def gen(r):
    def mode(): return r.choice(["rm","rm2","rm","RNE","RTZ"])
    def fp(d=0):
        c=r.random()
        if d<2 and c<.45:
            op=r.choice(["fp.add","fp.sub","fp.mul","fp.div"])
            return f"({op} {mode()} {fp(d+1)} {fp(d+1)})"
        if d<2 and c<.55: return f"(fp.roundToIntegral {mode()} {fp(d+1)})"
        if d<2 and c<.6: return f"(fp.fma {mode()} {fp(d+1)} {fp(d+1)} {fp(d+1)})"
        if d<2 and c<.65: return f"(fp.sqrt {mode()} {fp(d+1)})"
        return r.choice(["f","g",f"((_ to_fp 3 5) RNE {r.choice(['1.0','0.125','-2.5','0.375','3.0'])})"])
    def atom():
        c=r.random()
        if c<.55: return f"({r.choice(['fp.eq','fp.lt','fp.leq','fp.gt','='])} {fp()} {fp()})"
        if c<.7: return f"({r.choice(['fp.isNaN','fp.isZero','fp.isNormal','fp.isSubnormal','fp.isInfinite'])} {fp()})"
        if c<.9: return f"({r.choice(['=','distinct'])} {r.choice(['rm','rm2'])} {r.choice(['RNE','RNA','RTP','RTN','RTZ','rm2'])})"
        return f"(not (fp.eq {fp()} {fp()}))"
    return [f"(assert {atom()})" for _ in range(r.randint(1,4))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    asserts=gen(random.Random(i))
    decls="\n".join(f"(declare-const {n} {s})" for n,s in DECLS)
    src=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/rm_{i}.smt2"
    a=run(RS,src+"(get-model)\n",p).split("\n")[0]
    b=run(Z3,src,f"{OUT}/rm_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        out=run(RS,src+"(get-model)\n",p)
        defs=dict(re.findall(r"\(define-fun (\S+) \(\) \S+(?: \S+ \S+ \S+\))?\s+(.*?)\)\n",out,re.S))
        if defs:
            rep="\n".join(f"(define-fun {n} () {s} {defs[n].strip()})" if n in defs else f"(declare-const {n} {s})" for n,s in DECLS)
            z=run(Z3,rep+"\n"+"\n".join(asserts)+"\n(check-sat)\n",f"{OUT}/rm_{i}_replay.smt2").strip()
            if z=="unsat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
