#!/usr/bin/env python3
"""Model-validation fuzz of nonlinear real arithmetic with algebraic models.

Random polynomial systems over 1-3 reals with equalities likely to force
irrational solutions (`x² = 2`, ...). Whenever z3rs answers `sat`, its model
is replayed into z3: a rational value is a `define-fun`, an irrational
`(root-obj p k)` becomes a constant constrained by `p(x) = 0` and a 10^-25
window around the `:pp.decimal` rendering (precision 30) of the same model.
z3 re-checks the assertions: anything but `sat` is a wrong model (BADMODEL).

Usage: scripts/fuzz_nra_alg_models.py <z3rs> <z3> <n> <outdir>
"""
import random,re,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
def gen(r):
    vs=[f"x{i}" for i in range(r.randint(1,3))]
    def num(): k=r.randint(-3,3); return f"{k}.0" if k>=0 else f"(- {-k}.0)"
    def mono():
        fs=[r.choice(vs) for _ in range(r.randint(0,3))]
        return f"(* {num()} {' '.join(fs)})" if fs else num()
    def poly(): return f"(+ {' '.join(mono() for _ in range(r.randint(1,3)))})"
    def atom():
        op=r.choice(["<","<=","=","=","=",">",">=","distinct"])
        return f"({op} {poly()} 0.0)"
    def sq():
        v=r.choice(vs); k=r.choice([2,3,5,6,7])
        return f"(= (* {v} {r.choice(vs)}{' '+v if r.random()<.3 else ''}) {k}.0)"
    asserts=[f"(assert {atom() if r.random()<.6 else sq()})" for _ in range(r.randint(1,3))]
    return vs,asserts
def run(c,src,p):
    open(p,"w").write(src)
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout
    except subprocess.TimeoutExpired: return "timeout"
def defs_of(out):
    return dict((n,v.strip()) for n,v in re.findall(r"\(define-fun (\S+) \(\) Real\s+(.*?)\)\n",out[4:],re.S))
def one(i):
    r=random.Random(i); vs,asserts=gen(r)
    decls="\n".join(f"(declare-const {v} Real)" for v in vs)
    body=decls+"\n"+"\n".join(asserts)+"\n(check-sat)\n(get-model)\n"
    p=f"{OUT}/a_{i}.smt2"
    out=run(RS,body,p)
    if not out.startswith("sat"): return "skip",p
    defs=defs_of(out)
    if not defs: return "nomodel",p
    dec=defs_of(run(RS,"(set-option :pp.decimal true)\n(set-option :pp.decimal-precision 30)\n"+body,f"{OUT}/a_{i}_dec.smt2"))
    src=[]; alg=False
    for n,v in defs.items():
        if "root-obj" not in v:
            src.append(f"(define-fun {n} () Real {v})"); continue
        alg=True
        m=re.match(r"\(root-obj (.*) \d+\)$",v,re.S); d=dec.get(n,"")
        dm=re.match(r"^(\(- )?([0-9.]+)\??\)?$",d)
        if not m or not dm: return "badformat",p
        mid=f"(- {dm.group(2)})" if dm.group(1) else dm.group(2)
        poly=re.sub(r"\bx\b",n,m.group(1))
        src.append(f"(declare-const {n} Real)\n(assert (= {poly} 0))")
        src.append(f"(assert (< (- {n} {mid}) 0.0000000000000000000000001))")
        src.append(f"(assert (> (- {n} {mid}) (- 0.0000000000000000000000001)))")
    src+= [f"(declare-const {v} Real)" for v in vs if v not in defs]
    q=f"{OUT}/a_{i}_replay.smt2"
    z=run(Z3,"\n".join(src)+"\n"+"\n".join(asserts)+"\n(check-sat)\n",q).strip()
    tag="alg" if alg else "rat"
    return (f"ok-{tag}" if z=="sat" else "BADMODEL" if z=="unsat" else "z3:"+z[:20]),q
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="BADMODEL" or not k.startswith(("ok","skip")): print(k,p)
