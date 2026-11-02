#!/usr/bin/env python3
"""Differential fuzz of `(simplify …)` on regular-expression terms.

Random membership atoms and regex equalities over a string variable, regex
variables and constant regexes are simplified by z3rs and z3. A ground
membership simplifying to opposite truth values is a soundness bug
(WRONG); any other textual difference is reported as DIFF (z3 orders union
and intersection operands by internal expression ids, which z3rs only
approximates by creation order). One simplify per script, so earlier
commands do not perturb z3's ids.

Usage: scripts/fuzz_re_simplify.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
HDR="(declare-const a String)\n(declare-const r (RegEx String))\n(declare-const s (RegEx String))\n"
def gen(r, ground):
    def lit(): return r.choice(['""','"a"','"b"','"ab"','"ba"'])
    def rx(d=0):
        c=r.random()
        if d<3 and c<.14: return f"(re.union {rx(d+1)} {rx(d+1)})"
        if d<3 and c<.28: return f"(re.++ {rx(d+1)} {rx(d+1)})"
        if d<3 and c<.36: return f"(re.* {rx(d+1)})"
        if d<3 and c<.42: return f"(re.+ {rx(d+1)})"
        if d<3 and c<.46: return f"(re.opt {rx(d+1)})"
        if d<3 and c<.5:
            lo=r.randint(0,2); hi=lo+r.randint(0,2)
            return f"((_ re.loop {lo} {hi}) {rx(d+1)})"
        if d<3 and c<.56: return f"(re.inter {rx(d+1)} {rx(d+1)})"
        if d<3 and c<.6: return f"(re.comp {rx(d+1)})"
        if d<3 and c<.62: return f"(re.diff {rx(d+1)} {rx(d+1)})"
        if c<.68: return f'(re.range "a" "{r.choice("abc")}")'
        if c<.74: return r.choice(["re.allchar","re.all","re.none"])
        if not ground and c<.84: return r.choice(["r","s"])
        return f"(str.to_re {lit()})"
    if ground:
        return f"(str.in_re {lit()} {rx()})"
    c=r.random()
    if c<.5: return f"(str.in_re a {rx()})"
    return f"(= {rx()} {rx()})"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip()
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    r=random.Random(i)
    ground=r.random()<.4
    t=gen(r,ground)
    p=f"{OUT}/rs_{i}.smt2"; open(p,"w").write(HDR+f"(simplify {t})\n")
    a,b=run(RS,p),run(Z3,p)
    if a==b: return "same",p
    if {a,b}=={"true","false"}: return "WRONG",p
    return "DIFF",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k!="same": print(k,p)
