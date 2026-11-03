#!/usr/bin/env python3
"""Differential fuzz of bit-vectors reinterpreted as floats (`(_ to_fp eb sb) bv`).

Random (3,5)-float constraints whose operands include `((_ to_fp 3 5) t)` for
8-bit bit-vector terms `t` (variables, bvadd/bvnot/concat/extract), mixed
with FP arithmetic, classification and comparisons. Definite verdicts are
compared with z3 (DISAGREE = soundness bug), and every z3rs `sat` model is
replayed through z3 as define-funs (BADMODEL = wrong model).

Usage: scripts/fuzz_fp_from_bv.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
F="(_ FloatingPoint 3 5)"
DECLS=[("u","(_ BitVec 8)"),("v","(_ BitVec 8)"),("w","(_ BitVec 5)"),("f",F)]
def gen(r):
    def bv(d=0):
        c=r.random()
        if d<2 and c<.2: return f"(bvadd {bv(d+1)} {bv(d+1)})"
        if d<2 and c<.3: return f"(bvnot {bv(d+1)})"
        if d<2 and c<.4: return f"(concat w ((_ extract 2 0) {bv(d+1)}))"
        if c<.5: return f"#b{r.getrandbits(8):08b}"
        return r.choice(["u","v"])
    def fp(d=0):
        c=r.random()
        if d<2 and c<.3:
            return f"({r.choice(['fp.add','fp.mul','fp.sub'])} RNE {fp(d+1)} {fp(d+1)})"
        if d<2 and c<.4: return f"(fp.neg {fp(d+1)})"
        if c<.75: return f"((_ to_fp 3 5) {bv()})"
        return r.choice(["f","((_ to_fp 3 5) RNE 1.5)"])
    def atom():
        c=r.random()
        if c<.45: return f"({r.choice(['fp.eq','fp.lt','fp.leq','='])} {fp()} {fp()})"
        if c<.7: return f"({r.choice(['fp.isNaN','fp.isZero','fp.isNormal','fp.isSubnormal','fp.isInfinite','fp.isNegative'])} {fp()})"
        if c<.85: return f"({r.choice(['=','bvult'])} {bv()} {bv()})"
        return f"(not (= {fp()} {fp()}))"
    return [f"(assert {atom()})" for _ in range(r.randint(1,4))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    asserts=gen(random.Random(i))
    decls="\n".join(f"(declare-const {n} {s})" for n,s in DECLS)
    src=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/fb_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/fb_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        defs=dict(re.findall(r"\(define-fun (\S+) \(\) (?:\(_ \S+ \d+(?: \d+)?\)|\S+)\s+(.*?)\)\n",out,re.S))
        if defs:
            rep="\n".join(f"(define-fun {n} () {s} {defs[n].strip()})" if n in defs else f"(declare-const {n} {s})" for n,s in DECLS)
            z=run(Z3,rep+"\n"+"\n".join(asserts)+"\n(check-sat)\n",f"{OUT}/fb_{i}_replay.smt2").strip()
            if z=="unsat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
