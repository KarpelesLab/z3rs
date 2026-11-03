#!/usr/bin/env python3
"""Differential soundness fuzz of sequence constraints.

Random conjunctions over two (Seq Int) variables and an Int: units,
concatenation, seq.extract/seq.at/seq.nth/seq.len, `ite` over sequences
and the containment predicates. Only definite answers are compared: a
DISAGREE is a soundness bug.

Usage: scripts/fuzz_seq.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    def num(): return r.choice(["0","1","2","i","(seq.len a)","(- (seq.len b) 1)"])
    def el(): return r.choice(["0","1","2","i"])
    def sq(d=0):
        c=r.random()
        if d<2 and c<.2: return f"(seq.++ {sq(d+1)} {sq(d+1)})"
        if d<2 and c<.32: return f"(seq.extract {sq(d+1)} {num()} {num()})"
        if d<2 and c<.4: return f"(seq.at {sq(d+1)} {num()})"
        if d<2 and c<.48: return f"(ite (= {num()} {num()}) {sq(d+1)} {sq(d+1)})"
        if c<.65: return f"(seq.unit {el()})"
        if c<.7: return "(as seq.empty (Seq Int))"
        return r.choice(["a","b"])
    def atom():
        c=r.random()
        if c<.3: return f"({r.choice(['=','distinct'])} {sq()} {sq()})"
        if c<.5: return f"({r.choice(['<','<=','=','>'])} (seq.len {sq()}) {num()})"
        if c<.7: return f"({r.choice(['=','distinct'])} (seq.nth {sq()} {num()}) {el()})"
        return f"({r.choice(['seq.contains','seq.prefixof','seq.suffixof'])} {sq()} {sq()})"
    a=["(declare-const a (Seq Int))","(declare-const b (Seq Int))","(declare-const i Int)"]
    a+=[f"(assert {atom()})" for _ in range(r.randint(1,4))]
    return "\n".join(a)+"\n(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/sq_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
