#!/usr/bin/env python3
"""Differential fuzz of sequences of unbounded length (the length abstraction).

Random conjunctions over three (Seq Int) variables of unbounded length and
two Ints: word equations between concatenations of variables and units,
extract/at windows at symbolic offsets, the containment predicates, `ite`
over sequences and length constraints (some long: 5 to 8 elements).
Definite verdicts are compared with z3 (DISAGREE = soundness bug), and each
z3rs `sat` is replayed through z3 with its get-value assignment (BADMODEL =
wrong model; NONLITERAL = a placeholder instead of a concrete sequence).

Usage: scripts/fuzz_seq_lengths.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
VARS=["a","b","c"]
def gen(r):
    def num(): return r.choice(["0","1","2","i","j","(seq.len a)","(- (seq.len b) 1)","(seq.len c)"])
    def el(): return r.choice(["0","1","2","i"])
    def word(d=0):
        parts=[]
        for _ in range(r.randint(1,3)):
            c=r.random()
            if c<.45: parts.append(r.choice(VARS))
            elif c<.8: parts.append(f"(seq.unit {el()})")
            elif d<1 and c<.9: parts.append(f"(seq.extract {word(d+1)} {num()} {num()})")
            elif d<1: parts.append(f"(ite (= {num()} {num()}) {word(d+1)} {word(d+1)})")
            else: parts.append(r.choice(VARS))
        return parts[0] if len(parts)==1 else "(seq.++ "+" ".join(parts)+")"
    def atom():
        c=r.random()
        if c<.4: return f"(= {word()} {word()})"
        if c<.5: return f"(distinct {word()} {word()})"
        if c<.75: return f"({r.choice(['<','<=','=','>','>='])} (seq.len {word()}) {r.choice(['0','1','3','5','8',num()])})"
        if c<.85: return f"(= (seq.nth {word()} {num()}) {el()})"
        return f"({r.choice(['seq.contains','seq.prefixof','seq.suffixof'])} {word()} {word()})"
    a=[f"(declare-const {v} (Seq Int))" for v in VARS]+["(declare-const i Int)","(declare-const j Int)"]
    a+=[f"(assert {atom()})" for _ in range(r.randint(1,4))]
    return "\n".join(a)+"\n"
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip()
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
    p=f"{OUT}/sl_{n}.smt2"
    out=run(RS,src+"(check-sat)\n(get-value (a b c i j))\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src+"(check-sat)\n",f"{OUT}/sl_{n}_z3.smt2").split("\n")[0]
    if a=="sat":
        vals=out[out.index("\n")+1:].strip() if "\n" in out else ""
        if "!val!" in vals: return "NONLITERAL",p
        if not vals.startswith("(("): return "BADMODEL",p
        pairs=sexprs(vals[1:-1])
        fix="\n".join(f"(assert (= {x[1:-1].split(' ',1)[0]} {x[1:-1].split(' ',1)[1]}))" for x in pairs)
        z=run(Z3,src+fix+"\n(check-sat)\n",f"{OUT}/sl_{n}_replay.smt2").strip()
        if z!="sat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL","NONLITERAL"): print(k,p)
