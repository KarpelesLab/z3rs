#!/usr/bin/env python3
"""Differential fuzz of string constraints.

Random conjunctions over two string variables and an integer: concatenation,
`str.len`, `str.at`, `str.substr`, `str.replace`, `str.indexof`, and the
predicates `prefixof`/`suffixof`/`contains`, with short literals. Definite
verdicts are compared with z3 (DISAGREE = soundness bug), and each z3rs
`sat` model is replayed through z3 as define-funs and each assertion is
re-evaluated with `eval` (BADMODEL = wrong model, a non-literal string value,
or an assertion evaluating to `false`).

Usage: scripts/fuzz_str.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
DECLS=[("a","String"),("b","String"),("i","Int")]
def gen(r):
    def lit(): return r.choice(['""','"a"','"b"','"ab"','"ba"','"aab"'])
    def num(): return r.choice(["0","1","2","i","(str.len a)","(- 1)"])
    def s(d=0):
        c=r.random()
        if d<2 and c<.2: return f"(str.++ {s(d+1)} {s(d+1)})"
        if d<2 and c<.3: return f"(str.at {s(d+1)} {num()})"
        if d<2 and c<.4: return f"(str.substr {s(d+1)} {num()} {num()})"
        if d<2 and c<.47: return f"(str.replace {s(d+1)} {s(d+1)} {s(d+1)})"
        if c<.65: return lit()
        return r.choice(["a","b"])
    def atom():
        c=r.random()
        if c<.3: return f"({r.choice(['=','distinct'])} {s()} {s()})"
        if c<.55: return f"({r.choice(['str.prefixof','str.suffixof','str.contains'])} {s()} {s()})"
        if c<.75: return f"({r.choice(['=','<','<=','>'])} (str.len {s()}) {num()})"
        if c<.85: return f"(= (str.indexof {s()} {s()} {num()}) {num()})"
        return f"(not ({r.choice(['str.prefixof','str.contains'])} {s()} {s()}))"
    return [atom() for _ in range(r.randint(1,3))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    atoms=gen(random.Random(i))
    asserts=[f"(assert {x})" for x in atoms]
    decls="\n".join(f"(declare-const {n} {s})" for n,s in DECLS)
    src=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/st_{i}.smt2"
    out=run(RS,src+"(get-model)\n"+"".join(f"(eval {x})\n" for x in atoms),p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/st_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        if "!val!" in out or "\nfalse" in out: return "BADMODEL",p
        defs=dict(re.findall(r"\(define-fun (\S+) \(\) \S+\s+(.*?)\)\n",out,re.S))
        if defs:
            rep="\n".join(f"(define-fun {n} () {s} {defs[n].strip()})" if n in defs else f"(declare-const {n} {s})" for n,s in DECLS)
            z=run(Z3,rep+"\n"+"\n".join(asserts)+"\n(check-sat)\n",f"{OUT}/st_{i}_replay.smt2").strip()
            if z=="unsat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
