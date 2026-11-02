#!/usr/bin/env python3
"""Differential fuzz of the online DPLL(T) core on fuzzsmt-shaped goals.

Random QF_AUFLIA / QF_UFLIA / QF_LIA formulas in the style of the `fuzzsmt`
benchmarks (t168-t170): a chain of let-bound integer, array and Boolean
terms over uninterpreted functions, `store`/`select`, array-valued `ite`s,
linear arithmetic and predicates, combined by a deep Boolean skeleton. They
exercise the online congruence closure and simplex (conflicts and
propagations on partial assignments), the model-based case splits
(disequalities, integer branches) and model-based theory combination (many
interface terms). Definite verdicts are compared with z3 (DISAGREE =
soundness bug), and each z3rs `sat` model is replayed through z3 (BADMODEL).

Usage: scripts/fuzz_dpllt.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    arrays=r.random()<.6
    ints=[f"v{i}" for i in range(r.randint(2,4))]
    arrs=[f"a{i}" for i in range(r.randint(2,3))] if arrays else []
    decls=[f"(declare-fun {v} () Int)" for v in ints]
    decls+=[f"(declare-fun {a} () (Array Int Int))" for a in arrs]
    decls+=["(declare-fun f0 (Int) Int)","(declare-fun p0 (Int Int) Bool)"]
    if arrays:
        decls+=["(declare-fun f1 ((Array Int Int)) (Array Int Int))",
                "(declare-fun p1 ((Array Int Int)) Bool)"]
    I,A,B=list(ints),list(arrs),[]
    lets=[]
    def name():
        return f"e{len(lets)}"
    def num(): return str(r.randint(0,9)) if r.random()<.7 else f"(- {r.randint(1,9)})"
    for _ in range(r.randint(10,45)):
        k=r.random()
        if k<.35:
            x,y=r.choice(I),r.choice(I)
            t=r.choice([f"(+ {x} {y})",f"(- {x} {y})",f"(* {x} {num()})",f"(f0 {x})",
                        f"(+ {x} {num()})",f"(ite {r.choice(B)} {x} {y})" if B else f"(f0 {y})"])
            if A and r.random()<.4: t=f"(select {r.choice(A)} {x})"
            lets.append((name(),t)); I.append(lets[-1][0])
        elif k<.55 and A:
            a=r.choice(A)
            t=r.choice([f"(store {a} {r.choice(I)} {r.choice(I)})",f"(f1 {a})",
                        f"(ite {r.choice(B)} {a} {r.choice(A)})" if B else f"(f1 {r.choice(A)})"])
            lets.append((name(),t)); A.append(lets[-1][0])
        else:
            x,y=r.choice(I),r.choice(I)
            choices=[f"(= {x} {y})",f"(distinct {x} {y})",f"(< {x} {y})",f"(<= {x} {num()})",
                     f"(>= {x} {y})",f"(p0 {x} {y})"]
            if A: choices+=[f"(= {r.choice(A)} {r.choice(A)})",f"(p1 {r.choice(A)})"]
            lets.append((name(),r.choice(choices))); B.append(lets[-1][0])
    if not B:
        lets.append((name(),f"(= {ints[0]} {ints[-1]})")); B.append(lets[-1][0])
    # Boolean skeleton
    for _ in range(r.randint(len(B)//2+1,len(B)+3)):
        op=r.choice(["and","or","=>","xor","=","not","or"])
        if op=="not": t=f"(not {r.choice(B)})"
        else: t=f"({op} {r.choice(B)} {r.choice(B)})"
        lets.append((name(),t)); B.append(lets[-1][0])
    body=B[-1]
    for n,t in reversed(lets):
        body=f"(let (({n} {t})) {body})"
    return decls,[f"(assert {body})"]
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=30).stdout
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    decls,asserts=gen(random.Random(i))
    src="\n".join(decls)+"\n"+"\n".join(asserts)+"\n(check-sat)\n"
    p=f"{OUT}/dt_{i}.smt2"
    out=run(RS,src+"(get-model)\n",p)
    a=out.split("\n")[0]
    b=run(Z3,src,f"{OUT}/dt_{i}_z3.smt2").split("\n")[0]
    if a=="sat":
        body=out[out.find("(",4):]
        defs=re.findall(r"\(define-fun .*?(?=\n  \(define-fun|\n\)\s*$)",body,re.S)
        names=set(re.findall(r"\(define-fun (\S+)",body))
        if defs:
            ds=[d for d in decls if d.split()[1] not in names]
            rep="\n".join(ds+[d.strip() for d in defs]+asserts)+"\n(check-sat)\n"
            z=run(Z3,rep,f"{OUT}/dt_{i}_replay.smt2").strip()
            if z.startswith("unsat"): return "BADMODEL",p
            if "error" in z: return "REPLAY-ERROR",p
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL","REPLAY-ERROR"): print(k,p)
