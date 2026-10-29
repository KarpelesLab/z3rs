#!/usr/bin/env python3
"""Differential fuzz of opt.priority (box / pareto / lex) against z3.

Random small Int problems over bounded boxes, each with 2-3 objectives and five
repeated (check-sat)(get-objectives). box and lex output must be byte-identical
to z3's (apart from the interval z3 prints after `unsat`, which depends on its
preprocessing). The pareto front order depends on the solver's models, so each
pareto answer is instead checked against the front computed by brute force:
distinct front points, `sat` once per point, then `unsat`.

Usage: scripts/fuzz_opt_priority.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,itertools,re,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
c=lambda k: str(k) if k>=0 else f"(- {-k})"
def gen(r):
    nv=r.randint(2,3); vs=[f"x{i}" for i in range(nv)]
    bounds=[(lo:=r.randint(-4,3), lo+r.randint(1,6)) for _ in vs]
    def lin(): return [r.randint(-3,3) for _ in vs]
    def txt(co): return "(+ "+" ".join(f"(* {c(k)} {v})" for k,v in zip(co,vs))+")"
    cons=[(lin(),r.choice(["<=",">="]),r.randint(-6,6)) for _ in range(r.randint(0,3))]
    objs=[(lin(),r.random()<.5) for _ in range(r.randint(2,3))]
    pri=r.choice(["box","pareto","lex"])
    a=[f"(set-option :opt.priority {pri})"]+[f"(declare-const {v} Int)" for v in vs]
    a+=[f"(assert (<= {c(lo)} {v} {c(hi)}))" for v,(lo,hi) in zip(vs,bounds)]
    a+=[f"(assert ({op} {txt(co)} {c(k)}))" for co,op,k in cons]
    a+=[f"({'maximize' if mx else 'minimize'} {txt(co)})" for co,mx in objs]
    a+=["(check-sat)(get-objectives)"]*5
    # brute-force front (in "bigger is better" coordinates)
    pts=set()
    for x in itertools.product(*[range(lo,hi+1) for lo,hi in bounds]):
        if all((sum(k*v for k,v in zip(co,x))<=k0) if op=="<=" else (sum(k*v for k,v in zip(co,x))>=k0) for co,op,k0 in cons):
            pts.add(tuple(sum(k*v for k,v in zip(co,x)) for co,_ in objs))
    sgn=[1 if mx else -1 for _,mx in objs]
    better=lambda p,q: all(a*s>=b*s for a,b,s in zip(p,q,sgn)) and p!=q
    front={p for p in pts if not any(better(q,p) for q in pts)}
    return pri,"\n".join(a)+"\n",front
def run(cmd,p):
    try: return subprocess.run([cmd,p],capture_output=True,text=True,timeout=30).stdout
    except subprocess.TimeoutExpired: return "TIMEOUT"
def parse(o):
    res=[];
    for blk in re.split(r"\n(?=sat|unsat|unknown)", o.strip()):
        lines=blk.split("\n"); vals=[]
        for ln in lines[2:-1]:
            m=re.match(r"^ \(.*\) (\(- \d+\)|-?\d+)\)$",ln)
            vals.append(None if not m else int(m.group(1).replace("(- ","-").replace(")","")))
        res.append((lines[0],tuple(vals)))
    return res
def one(i):
    r=random.Random(i); pri,src,front=gen(r); p=f"{OUT}/of_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    if a==b: return "same",p
    if pri!="pareto": return "DIFF-"+pri,p
    ra=parse(a); exp_n=min(len(front),5)
    verds=[v for v,_ in ra]
    if "unknown" in verds: return "rs-unknown",p
    want=["sat"]*exp_n+(["unsat"] if exp_n<5 else [])
    if not front: want=["unsat"]*5
    pts=[v for vv,v in ra[:exp_n]]
    ok = verds[:len(want)]==want and len(set(pts))==len(pts) and all(q in front for q in pts)
    return ("pareto-valid" if ok else "BAD-pareto"),p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k.startswith(("DIFF","BAD","rs-")): print(k,p)
