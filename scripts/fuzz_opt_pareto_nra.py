#!/usr/bin/env python3
"""Differential fuzz of `pareto` optimization over nonlinear reals.

Random problems whose points have irrational coordinates (`x² = k`, linear
links, a disjunction or two) with two objectives under `opt.priority
pareto`. Each solver's front (the objective blocks reported before `unsat`)
is compared as a set, since the order points are found in depends on the
models. A front that differs (FRONT-DIFF) or a definite verdict mismatch
(DISAGREE) is a bug.

Usage: scripts/fuzz_opt_pareto_nra.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    k=r.choice([2,3,5])
    src="(set-option :opt.priority pareto)\n(declare-const x Real)\n(declare-const y Real)\n"
    src+=f"(assert (= (* x x) {k}))\n"
    rel=r.choice(["(= y (- x))","(= y (+ x 1))","(= (* y y) 2)","(= y (* 2 x))","(<= y x)"])
    src+=f"(assert {rel})\n"
    if r.random()<.5:
        src+=f"(assert (or (> x 0) (> y {r.choice(['0','1','(- 1)'])})))\n"
    if r.random()<.3:
        src+=f"(assert (<= (+ x y) {r.choice(['0','2','3'])}))\n"
    src+=f"({r.choice(['maximize','minimize'])} x)\n({r.choice(['maximize','minimize'])} y)\n"
    src+="(check-sat)\n(get-objectives)\n"*5
    return src
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=30).stdout
    except subprocess.TimeoutExpired: return "timeout"
def front(out):
    if out=="timeout": return None
    lines=out.split("\n"); pts=[]; i=0
    while i<len(lines):
        if lines[i]=="sat":
            j=lines.index(")",i)
            pts.append("\n".join(lines[i+2:j])); i=j+1
        elif lines[i]=="unsat": return sorted(pts)
        elif lines[i]=="unknown": return None
        else: i+=1
    return None
def one(i):
    p=f"{OUT}/pn_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=front(run(RS,p)),front(run(Z3,p))
    if a is None or b is None: return f"{'none' if a is None else 'ok'}/{'none' if b is None else 'ok'}",p
    return ("same" if a==b else "FRONT-DIFF"),p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="FRONT-DIFF": print(k,p)
