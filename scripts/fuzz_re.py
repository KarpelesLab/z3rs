#!/usr/bin/env python3
"""Differential fuzz of regular-expression membership.

Random conjunctions over two string variables: `str.in_re` against random
constant regexes (literals, ranges, union, concatenation, star, plus, opt,
loops, intersection, complement, and `str.to_re` over symbolic string
terms), together with length constraints and
literal (dis)equalities. Definite verdicts are compared with z3 (DISAGREE =
soundness bug), and each z3rs `sat` model is replayed through z3 as
define-funs (BADMODEL = wrong model or a non-literal string value).

Usage: scripts/fuzz_re.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
DECLS=[("a","String"),("b","String")]
def gen(r):
    def lit(): return r.choice(['""','"a"','"b"','"ab"','"ba"','"aab"'])
    def rx(d=0):
        c=r.random()
        if d<3 and c<.15: return f"(re.union {rx(d+1)} {rx(d+1)})"
        if d<3 and c<.3: return f"(re.++ {rx(d+1)} {rx(d+1)})"
        if d<3 and c<.38: return f"(re.* {rx(d+1)})"
        if d<3 and c<.44: return f"(re.+ {rx(d+1)})"
        if d<3 and c<.48: return f"(re.opt {rx(d+1)})"
        if d<3 and c<.55:
            lo=r.randint(0,3); hi=lo+r.randint(0,2)
            return f"((_ re.loop {lo} {hi}) {rx(d+1)})"
        if d<3 and c<.6: return f"(re.inter {rx(d+1)} {rx(d+1)})"
        if d<3 and c<.64: return f"(re.comp {rx(d+1)})"
        if c<.7: return f'(re.range "a" "{r.choice("abc")}")'
        if c<.75: return r.choice(["re.allchar","re.all","re.none"])
        if c<.82: return f"(str.to_re {r.choice([var(), f'(str.++ {var()} {lit()})', f'(str.substr {var()} 0 {r.randint(0,2)})'])})"
        return f"(str.to_re {lit()})"
    def var(): return r.choice(["a","b"])
    def atom():
        c=r.random()
        if c<.5: return f"(str.in_re {var()} {rx()})"
        if c<.6: return f"(not (str.in_re {var()} {rx()}))"
        if c<.85: return f"({r.choice(['=','<','<=','>','>='])} (str.len {var()}) {r.randint(0,7)})"
        if c<.95: return f"({r.choice(['=','distinct'])} {var()} {lit()})"
        return f"(= a b)"
    return [atom() for _ in range(r.randint(1,4))]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    atoms=gen(random.Random(i))
    asserts=[f"(assert {x})" for x in atoms]
    decls="\n".join(f"(declare-const {n} {s})" for n,s in DECLS)
    src=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/re_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/re_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        if "!val!" in out: return "BADMODEL",p
        defs=dict(re.findall(r"\(define-fun (\S+) \(\) \S+\s+(.*?)\)\n",out,re.S))
        if defs:
            rep="\n".join(f"(define-fun {n} () {s} {defs[n].strip()})" if n in defs else f"(declare-const {n} {s})" for n,s in DECLS)
            z=run(Z3,rep+"\n"+"\n".join(asserts)+"\n(check-sat)\n",f"{OUT}/re_{i}_replay.smt2").strip()
            if z!="sat": return "BADMODEL",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
