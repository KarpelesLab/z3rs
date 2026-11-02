#!/usr/bin/env python3
"""Differential soundness fuzz of `fp.to_ieee_bv`, NaN patterns included.

Random conjunctions over small-format floats (`(_ FloatingPoint 3 5)`) and
bit-vectors relating `fp.to_ieee_bv` of variables, NaN/inf/zero literals and
`to_fp` of bit-vectors, with `:rewriter.hi_fp_unspecified` on or off. Every
NaN is one value whose `fp.to_ieee_bv` is one fixed (unspecified) NaN
pattern. Only definite answers are compared: a DISAGREE is a soundness bug.

Usage: scripts/fuzz_fp_ieee_bv.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
EB,SB=3,5
W=EB+SB
def gen(r):
    fs=["x","y"]; bs=["b","c"]
    def fp():
        k=r.random()
        if k<.45: return r.choice(fs)
        if k<.6: return r.choice([f"(_ NaN {EB} {SB})",f"(_ +oo {EB} {SB})",f"(_ -zero {EB} {SB})"])
        if k<.75: return f"((_ to_fp {EB} {SB}) {r.choice(bs)})"
        if k<.85: return f"((_ to_fp {EB} {SB}) #b{r.getrandbits(W):0{W}b})"
        return f"(fp.abs {r.choice(fs)})"
    def bv():
        k=r.random()
        if k<.5: return f"(fp.to_ieee_bv {fp()})"
        if k<.75: return r.choice(bs)
        return f"#b{r.getrandbits(W):0{W}b}"
    def atom():
        k=r.random()
        if k<.4: a=f"(= {bv()} {bv()})"
        elif k<.6: a=f"(fp.isNaN {fp()})"
        elif k<.8: a=f"(= {fp()} {fp()})"
        else: a=f"(bvult {bv()} {bv()})"
        return a if r.random()<.6 else f"(not {a})"
    src=""
    if r.random()<.3: src+="(set-option :rewriter.hi_fp_unspecified true)\n"
    src+="".join(f"(declare-const {v} (_ FloatingPoint {EB} {SB}))\n" for v in fs)
    src+="".join(f"(declare-const {v} (_ BitVec {W}))\n" for v in bs)
    src+="".join(f"(assert {atom()})\n" for _ in range(r.randint(1,4)))
    return src+"(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/ieee_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
