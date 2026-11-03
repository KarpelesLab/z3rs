#!/usr/bin/env python3
"""Differential fuzz of fp.fma against z3 on concrete operands.

Random bit patterns (biased towards zeros, infinities, NaN, subnormals) in
small and standard formats, every rounding mode; the rounded result printed by
(get-value) must be byte-identical to z3's.

sb=3 formats are left out: z3 5.3.2 folds concrete fma with its software
floats, which mis-round there (e.g. (3,3) RNE 1.25*8+0 gives +oo, not 10);
z3rs agrees with exact rational rounding on all of those.

Usage: scripts/fuzz_fp_fma.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
FMTS=[(2,4),(3,4),(2,5),(4,4),(3,5),(4,6),(5,11),(8,24)]
RMS=["RNE","RNA","RTP","RTN","RTZ"]
def lit(r,eb,sb):
    m=sb-1; c=r.random()
    s=r.randint(0,1)
    if c<.1: e,f=0,0
    elif c<.18: e,f=(1<<eb)-1,0
    elif c<.22: e,f=(1<<eb)-1,r.randint(1,(1<<m)-1)
    elif c<.35: e,f=0,r.randint(0,(1<<m)-1)
    else: e,f=r.randint(0,(1<<eb)-1),r.randint(0,(1<<m)-1)
    b=lambda v,w: "#b"+format(v,f"0{w}b")
    return f"(fp {b(s,1)} {b(e,eb)} {b(f,m)})"
def gen(r):
    eb,sb=r.choice(FMTS); rm=r.choice(RMS)
    xs=[lit(r,eb,sb) for _ in range(3)]
    return (f"(declare-const r (_ FloatingPoint {eb} {sb}))\n"
            f"(assert (= r (fp.fma {rm} {' '.join(xs)})))\n(check-sat)\n(get-value (r))\n")
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/fma_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    return ("same" if a==b else "DIFF"),p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k!="same": print(k,p)
