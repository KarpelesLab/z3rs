#!/usr/bin/env python3
"""Differential fuzz of word equations.

Random conjunctions over string variables a..e: equations and disequations
between concatenations of variables and short literals, with linear length
constraints. Definite verdicts are compared with z3 (DISAGREE = soundness
bug), and each z3rs `sat` model is replayed through z3 as define-funs
(BADMODEL = wrong model or a non-literal value).

Usage: scripts/fuzz_word_eq.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
VARS=["a","b","c","d","e"]
def gen(r):
    vs=VARS[:r.randint(2,5)]
    def lit(): return r.choice(['"a"','"b"','"ab"','"ba"','"abc"','""'])
    def cat():
        k=r.randint(1,3)
        parts=[r.choice(vs) if r.random()<.6 else lit() for _ in range(k)]
        return parts[0] if k==1 else f"(str.++ {' '.join(parts)})"
    def atom():
        c=r.random()
        if c<.45: return f"(= {cat()} {cat()})"
        if c<.55: return f"(not (= {cat()} {cat()}))"
        if c<.8: return f"({r.choice(['=','<','<=','>','>='])} (str.len {r.choice(vs)}) {r.randint(0,6)})"
        return f"({r.choice(['=','<='])} (str.len {r.choice(vs)}) (str.len {r.choice(vs)}))"
    return [atom() for _ in range(r.randint(1,4))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    atoms=gen(random.Random(i))
    asserts=[f"(assert {x})" for x in atoms]
    decls="\n".join(f"(declare-const {n} String)" for n in VARS)
    src=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/we_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/we_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        if "!val!" in out: return "BADMODEL",p
        defs=dict(re.findall(r"\(define-fun (\S+) \(\) \S+\s+(.*?)\)\n",out,re.S))
        rep="\n".join(f"(define-fun {n} () String {defs[n].strip()})" if n in defs else f"(declare-const {n} String)" for n in VARS)
        z=run(Z3,rep+"\n"+"\n".join(asserts)+"\n(check-sat)\n",f"{OUT}/we_{i}_replay.smt2").strip()
        if z!="sat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
