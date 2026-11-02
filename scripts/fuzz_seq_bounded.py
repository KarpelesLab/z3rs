#!/usr/bin/env python3
"""Differential fuzz of length-bounded sequences read at symbolic positions.

Random conjunctions over two (Seq Int) variables whose lengths are bounded
to small ranges and two Int positions: seq.nth/seq.at/seq.extract at
symbolic positions, concatenation, `ite`, and quantifiers over a small
integer range nested in the formula. Definite verdicts are compared with
z3 (DISAGREE = soundness bug), and each z3rs `sat` is replayed through z3
with the get-value assignment (BADMODEL = wrong model; NONLITERAL = a
placeholder value instead of a concrete sequence).

Usage: scripts/fuzz_seq_bounded.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    def num(): return r.choice(["0","1","2","i","j","(+ i 1)","(- (seq.len a) i)","(seq.len b)"])
    def el(): return r.choice(["0","1","2","i","(seq.nth a j)"])
    def sq(d=0):
        c=r.random()
        if d<2 and c<.2: return f"(seq.++ {sq(d+1)} {sq(d+1)})"
        if d<2 and c<.35: return f"(seq.extract {sq(d+1)} {num()} {num()})"
        if d<2 and c<.42: return f"(seq.at {sq(d+1)} {num()})"
        if d<2 and c<.48: return f"(ite (< {num()} {num()}) {sq(d+1)} {sq(d+1)})"
        if c<.6: return f"(seq.unit {el()})"
        return r.choice(["a","b"])
    def atom(k=None):
        k=k or num()
        c=r.random()
        if c<.25: return f"({r.choice(['=','distinct'])} {sq()} {sq()})"
        if c<.4: return f"({r.choice(['<','<=','=','>'])} (seq.len {sq()}) {num()})"
        if c<.75: return f"({r.choice(['=','<','>='])} (seq.nth {r.choice(['a','b',sq()])} {r.choice([num(),k])}) {el()})"
        return f"({r.choice(['<','<=','='])} {num()} {num()})"
    def quant():
        q=r.choice(["forall","exists"])
        lo=r.randint(0,1); hi=lo+r.randint(1,3)
        g=f"(and (<= {lo} k) (< k {hi}))"
        body=atom("k")
        f=f"(=> {g} {body})" if q=="forall" else f"(and {g} {body})"
        return f"({q} ((k Int)) {f})"
    def form():
        c=r.random()
        if c<.25: return f"(or {quant()} {atom()})"
        if c<.35: return f"(not {quant()})"
        if c<.45: return f"(= p {quant()})"
        return atom()
    a=["(declare-const a (Seq Int))","(declare-const b (Seq Int))","(declare-const i Int)",
       "(declare-const j Int)","(declare-const p Bool)"]
    for v in "ab":
        lo=r.randint(0,2); hi=lo+r.randint(0,2)
        a.append(f"(assert (<= {lo} (seq.len {v})))")
        a.append(f"(assert (<= (seq.len {v}) {hi}))")
    a+=[f"(assert {form()})" for _ in range(r.randint(1,4))]
    return "\n".join(a)+"\n"
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def sexprs(s):
    """The top-level s-expressions of `s` as strings."""
    out,depth,start=[],0,None
    for k,ch in enumerate(s):
        if ch=="(":
            if depth==0: start=k
            depth+=1
        elif ch==")":
            depth-=1
            if depth==0: out.append(s[start:k+1])
    return out
def one(n):
    src=gen(random.Random(n))
    p=f"{OUT}/sb_{n}.smt2"
    out=run(RS,src+"(check-sat)\n(get-value (a b i j p))\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src+"(check-sat)\n",f"{OUT}/sb_{n}_z3.smt2").split("\n")[0]
    if a=="sat":
        vals=out[out.index("\n")+1:].strip()
        # A placeholder value (no concrete sequence) is a known model gap,
        # reported apart from wrong models.
        if "!val!" in vals: return "NONLITERAL",p
        if not vals.startswith("(("): return "BADMODEL",p
        pairs=sexprs(vals[1:-1])
        fix="\n".join(f"(assert (= {x[1:-1].split(' ',1)[0]} {x[1:-1].split(' ',1)[1]}))" for x in pairs)
        z=run(Z3,src+fix+"\n(check-sat)\n",f"{OUT}/sb_{n}_replay.smt2").strip()
        if z!="sat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
