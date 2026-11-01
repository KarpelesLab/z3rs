#!/usr/bin/env python3
"""Differential soundness fuzz of goals mixing bit-vectors with other theories.

Random conjunctions of bit-vector, integer, real, small-float and
rounding-mode atoms, plus occasional linking atoms (bv2nat, fp.to_real,
fp.to_ubv) that tie the groups together. Exercises the independent-component
split of mixed goals. Only definite answers are compared: a DISAGREE is a
soundness bug.

Usage: scripts/fuzz_mixed_components.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
F="(_ FloatingPoint 3 3)"
def gen(r):
    def bv():
        return r.choice(["u","v",f"(_ bv{r.randrange(16)} 4)",f"(bvadd u {r.choice(['u','v'])})",f"(bvmul v (_ bv{r.randrange(16)} 4))"])
    def ar():
        return r.choice(["n","m",str(r.randint(-3,3)),"(+ n m)","(* 2 n)"])
    def re():
        return r.choice(["q",f"{r.randint(-3,3)}.0","(* q 2.0)","(+ q 0.5)"])
    def fp():
        return r.choice(["f","g","(fp.add rm f g)","((_ to_fp 3 3) RNE 1.0)","(fp.neg f)"])
    atoms=[
        lambda: f"({r.choice(['=','bvult','bvsle','distinct'])} {bv()} {bv()})",
        lambda: f"({r.choice(['=','<','<=','distinct'])} {ar()} {ar()})",
        lambda: f"({r.choice(['=','<','<='])} {re()} {re()})",
        lambda: f"({r.choice(['fp.eq','fp.lt','fp.leq','='])} {fp()} {fp()})",
        lambda: f"({r.choice(['fp.isNaN','fp.isZero','fp.isNormal'])} {fp()})",
        lambda: f"({r.choice(['=','distinct'])} rm {r.choice(['RNE','RTZ','RTP','rm2'])})",
        # links
        lambda: f"(= n (bv2nat {bv()}))",
        lambda: f"(= q (fp.to_real {fp()}))",
        lambda: f"(= u ((_ fp.to_ubv 4) RTZ {fp()}))",
    ]
    w=[5,4,3,4,2,2,1,1,1]
    a=["(declare-const u (_ BitVec 4))","(declare-const v (_ BitVec 4))",
       "(declare-const n Int)","(declare-const m Int)","(declare-const q Real)",
       f"(declare-const f {F})",f"(declare-const g {F})",
       "(declare-const rm RoundingMode)","(declare-const rm2 RoundingMode)"]
    for _ in range(r.randint(2,6)):
        a.append(f"(assert {r.choices(atoms,weights=w)[0]()})")
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/mx_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
