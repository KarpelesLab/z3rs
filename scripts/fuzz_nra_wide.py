#!/usr/bin/env python3
"""Differential fuzz of nonlinear goals over many variables.

Random QF_NRA / QF_NIA goals over 5-8 variables mixing products, real
division by a variable, `div`/`mod` on Real operands (z3 coerces them with
`to_int`), linear constraints and a Boolean skeleton. Exercises the nonlinear
witness searches that pin a cover of the products (or every nonlinear
variable) and decide the linear rest. Definite verdicts are compared with z3
(DISAGREE = soundness bug) and each z3rs `sat` model is replayed through z3
(BADMODEL).

Usage: scripts/fuzz_nra_wide.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    S=r.choice(["Real","Real","Int"])
    vs=[f"x{i}" for i in range(r.randint(5,8))]
    decls=[f"(declare-fun {v} () {S})" for v in vs]
    def num():
        k=r.randint(-3,6)
        s=str(abs(k)) if S=="Int" else f"{abs(k)}.0"
        return s if k>=0 else f"(- {s})"
    def term(d=0):
        k=r.random()
        if d>=2 or k<.35: return r.choice(vs) if r.random()<.8 else num()
        if k<.6: return f"(* {term(d+1)} {term(d+1)})"
        if k<.75: return f"(+ {term(d+1)} {term(d+1)})"
        if k<.85 and S=="Real": return f"(/ {term(d+1)} (+ {r.choice(vs)} {num()}))"
        if k<.9 and S=="Real":
            op=r.choice(["div","mod"])
            return f"(to_real ({op} {r.choice(vs)} {r.choice(['2.0','3.5','(- 2.0)'])}))"
        return f"(- {term(d+1)} {num()})"
    def atom():
        op=r.choice(["=","<=","<",">=","distinct"])
        return f"({op} {term()} {term()})"
    def lit():
        a=atom(); return a if r.random()<.75 else f"(not {a})"
    asserts=[]
    for _ in range(r.randint(3,7)):
        asserts.append(f"(assert {lit()})" if r.random()<.6 else f"(assert (or {lit()} {lit()}))")
    for v in r.sample(vs,2):
        asserts.append(f"(assert (= {v} {num()}))")
    return decls,asserts
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=30).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    decls,asserts=gen(random.Random(i))
    src="\n".join(decls)+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/nw_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/nw_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        body=out[out.find("(",4):]
        defs=re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)",body,re.S)
        names=set(re.findall(r"\(define-fun (\S+)",body))
        if defs:
            ds=[d for d in decls if d.split()[1] not in names]
            rep="\n".join(ds+[d.strip() for d in defs]+asserts)+"\n(check-sat)\n"
            z=run(Z3,rep,f"{OUT}/nw_{i}_replay.smt2").strip()
            if z.startswith("unsat"): return "BADMODEL",p
            if "error" in z: return "REPLAY-ERROR",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL","REPLAY-ERROR"): print(k,p)
