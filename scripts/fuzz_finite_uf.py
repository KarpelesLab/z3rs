#!/usr/bin/env python3
"""Differential soundness fuzz of uninterpreted functions over finite sorts.

Functions whose arguments range over an enumeration datatype and Bool (with
enumeration, Bool and Int results), applied at constant and symbolic
arguments and nested, plus enumeration-sorted constants, equalities and
integer constraints. These are decided through finite value tables; the
z3rs `get-value` of the constants and some applications is checked against
the assertions by z3 (and must name a constructor: an `E!val!k`
abstract value for the datatype sort is a BADMODEL). A DISAGREE or BADMODEL is a soundness bug.

Usage: scripts/fuzz_finite_uf.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures,re
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    E=["e0","e1","e2"]
    def et(d=0):
        c=r.random()
        if d<2 and c<.3: return f"(f {et(d+1)} {bt(d+1)})"
        if d<2 and c<.4: return f"(ite {bt(d+1)} {et(d+1)} {et(d+1)})"
        if c<.65: return r.choice(["x","y"])
        return r.choice(E)
    def bt(d=0):
        c=r.random()
        if d<2 and c<.3: return f"(p {et(d+1)})"
        if d<2 and c<.4: return f"(q {et(d+1)} {bt(d+1)})"
        if c<.6: return r.choice(["b","c"])
        return r.choice(["true","false"])
    def it(d=0):
        c=r.random()
        if d<2 and c<.4: return f"(h {et(d+1)} {bt(d+1)})"
        if c<.6: return r.choice(["n","m"])
        return str(r.randint(-1,3))
    def atom():
        c=r.random()
        if c<.3: return f"(= {et()} {et()})"
        if c<.5: return bt()
        if c<.75: return f"(<= {it()} {it()})"
        if c<.85: return f"(distinct {et()} {et()} {et()})"
        return f"(= {it()} {it()})"
    def form(d=0):
        c=r.random()
        if d>=2 or c<.45: return atom() if r.random()<.75 else f"(not {atom()})"
        return f"({r.choice(['and','or','=>'])} {form(d+1)} {form(d+1)})"
    a=["(set-option :produce-models true)","(declare-datatypes () ((E e0 e1 e2)))",
       "(declare-fun f (E Bool) E)","(declare-fun p (E) Bool)","(declare-fun q (E Bool) Bool)",
       "(declare-fun h (E Bool) Int)","(declare-const x E)","(declare-const y E)",
       "(declare-const b Bool)","(declare-const c Bool)","(declare-const n Int)","(declare-const m Int)"]
    for _ in range(r.randint(1,5)):
        a.append(f"(assert {form()})")
    vals="x y b c n m (f x b) (p y) (h x c) (f e0 true) (p e1) (h e2 false)"
    return "\n".join(a)+f"\n(check-sat)\n(get-value ({vals}))\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip()
    except subprocess.TimeoutExpired: return "timeout"
def check_model(src,vals,p):
    # E is a datatype: every value must be a constructor, never `E!val!k`.
    if "!val!" in vals: return False
    pins=re.findall(r"\(((?:\([^()]*\))|\w+) (true|false|e\d|\(- \d+\)|-?\d+)\)",vals)
    if not pins: return True
    body=src.split("(check-sat)")[0]
    q=p+".check.smt2"
    open(q,"w").write(body+"".join(f"(assert (= {t} {v}))\n" for t,v in pins)+"(check-sat)\n")
    return run(Z3,q).split("\n")[0]!="unsat"
def one(i):
    src=gen(random.Random(i)); p=f"{OUT}/fu_{i}.smt2"; open(p,"w").write(src)
    a,b=run(RS,p),run(Z3,p)
    a0,b0=a.split("\n")[0],b.split("\n")[0]
    if a0 in("sat","unsat") and b0 in("sat","unsat"):
        if a0!=b0: return "DISAGREE",p
        if a0=="sat" and not check_model(src,a,p): return "BADMODEL",p
        return "agree",p
    return f"{a0}/{b0}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k in("DISAGREE","BADMODEL"): print(k,p)
