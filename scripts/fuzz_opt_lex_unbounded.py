#!/usr/bin/env python3
"""Differential fuzz of lexicographic optimization after an unbounded objective.

Random small linear Int/Real problems with 2-3 objectives, run under z3rs and z3.
After an unbounded objective each later one takes a limit (z3's
optsmt::lex_after_unbounded); both solvers may print an interval instead of a
value, with search-dependent endpoints. Flags a definite value that differs
from z3's, or a value outside the other solver's interval (BAD-*), and verdict
disagreements.

Usage: scripts/fuzz_opt_lex_unbounded.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,re,concurrent.futures
from fractions import Fraction as F
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
c=lambda k: str(k) if k>=0 else f"(- {-k})"
def gen(r):
    srt=r.choice(["Int","Real"]); vs=["x","y","z"][:r.randint(2,3)]
    num=lambda k: (f"{k}.0" if k>=0 else f"(- {-k}.0)") if srt=="Real" else c(k)
    lin=lambda: "(+ "+" ".join(f"(* {num(r.randint(-2,2))} {v})" for v in vs)+")"
    a=[f"(declare-const {v} {srt})" for v in vs]
    for _ in range(r.randint(1,4)): a.append(f"(assert ({r.choice(['<=','>=','<','>'])} {lin()} {num(r.randint(-5,5))}))")
    for i in range(r.randint(2,3)): a.append(f"({r.choice(['maximize','minimize'])} {vs[i] if i<len(vs) and r.random()<.6 else lin()})")
    a.append("(check-sat)(get-objectives)")
    return "\n".join(a)+"\n"
def run(cmd,p):
    try: return subprocess.run([cmd,p],capture_output=True,text=True,timeout=60).stdout
    except subprocess.TimeoutExpired: return "TIMEOUT"
def sx(s):
    toks=re.findall(r"\(|\)|[^\s()]+",s); pos=[0]
    def go():
        t=toks[pos[0]]; pos[0]+=1
        if t=="(":
            l=[]
            while toks[pos[0]]!=")": l.append(go())
            pos[0]+=1; return l
        return t
    return go()
def ev(e):
    if e=="oo": return "oo"
    if isinstance(e,str):
        try: return F(e)
        except: return None
    if e==["*",["-","1"],"oo"]: return "-oo"
    if e[0]=="-" and len(e)==2:
        v=ev(e[1]); return -v if isinstance(v,F) else None
    if e[0]=="/":
        a,b=ev(e[1]),ev(e[2]); return a/b if isinstance(a,F) and isinstance(b,F) else None
    return None
def parse_line(ln):
    e=sx(ln)[1]
    if isinstance(e,list) and e and e[0]=="interval": return ("I",ev(e[1]),ev(e[2]))
    return ("V",ev(e))
def one(i):
    r=random.Random(i); src=gen(r); p=f"{OUT}/lau_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    if a==b: return "same",p
    la,lb=a.strip().split("\n"),b.strip().split("\n")
    if la[0]!=lb[0]: return ("VERDICT" if "unknown" not in (la[0],lb[0]) else "verd-unknown"),p
    if la[0]!="sat" or "oo)" not in b: return "other",p
    oa,ob=la[2:-1],lb[2:-1]
    for x,y in zip(oa,ob):
        if x==y: continue
        if "unknown" in x or "epsilon" in x+y: continue
        px,py=parse_line(x),parse_line(y)
        if px[0]=="V" and py[0]=="V": return "BAD-value",p
        if px[0]=="V" and py[0]=="I":
            lo,hi=py[1],py[2]
            v=px[1]
            if isinstance(v,F) and (lo=="-oo" or v>=lo) and (hi=="oo" or v<=hi): continue
            return "BAD-outside",p
        if px[0]=="I" and py[0]=="V":
            lo,hi=px[1],px[2]; v=py[1]
            if isinstance(v,F) and (lo=="-oo" or v>=lo) and (hi=="oo" or v<=hi): continue
            return "BAD-outside",p
    return "compatible",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k.startswith(("BAD","VERDICT")): print(k,p)
