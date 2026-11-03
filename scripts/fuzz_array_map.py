#!/usr/bin/env python3
"""Differential fuzz of `(_ map f)` arrays in array equalities.

Random goals over Int-indexed Bool and Int arrays built from variables,
`store`, constant arrays and `(_ map f)` (not / and / or / + / <= / ite),
related by array equalities, disequalities and reads. Exercises the map
axioms: pointwise reads at every index term and at the default index, and
the axioms of the arrays read through a map. Definite verdicts are compared
with z3 (DISAGREE = soundness bug).

Usage: scripts/fuzz_array_map.py <z3rs> <z3> <n> <outdir> [seed-offset]
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
OFF = int(sys.argv[5]) if len(sys.argv) > 5 else 0  # seed offset
def gen(r):
    BA=["x","y","z"]; IA=["a","b","c"]; IX=["i","j","0","1","2"]
    def idx(): return r.choice(IX)
    def barr(d=0):
        k=r.random()
        if d>=2 or k<.35: return r.choice(BA)
        if k<.45: return f"((as const (Array Int Bool)) {r.choice(['true','false'])})"
        if k<.6: return f"(store {barr(d+1)} {idx()} {r.choice(['true','false'])})"
        if k<.72: return f"((_ map not) {barr(d+1)})"
        if k<.86: return f"((_ map {r.choice(['and','or'])}) {barr(d+1)} {barr(d+1)})"
        return f"((_ map (<= (Int Int) Bool)) {iarr(d+1)} {iarr(d+1)})"
    def iarr(d=0):
        k=r.random()
        if d>=2 or k<.4: return r.choice(IA)
        if k<.5: return f"((as const (Array Int Int)) {r.randint(0,2)})"
        if k<.7: return f"(store {iarr(d+1)} {idx()} {r.randint(0,2)})"
        if k<.85: return f"((_ map (+ (Int Int) Int)) {iarr(d+1)} {iarr(d+1)})"
        return f"((_ map (ite (Bool Int Int) Int)) {barr(d+1)} {iarr(d+1)} {iarr(d+1)})"
    def atom():
        k=r.random()
        if k<.3: return f"(= {barr()} {barr()})"
        if k<.55: return f"(= {iarr()} {iarr()})"
        if k<.75: return f"(select {barr()} {idx()})"
        if k<.9: return f"(= (select {iarr()} {idx()}) {r.randint(0,3)})"
        return f"(distinct {r.choice(['i','j'])} {idx()})"
    def lit():
        a=atom(); return a if r.random()<.7 else f"(not {a})"
    src="".join(f"(declare-const {v} (Array Int Bool))\n" for v in BA)
    src+="".join(f"(declare-const {v} (Array Int Int))\n" for v in IA)
    src+="(declare-const i Int)\n(declare-const j Int)\n"
    for _ in range(r.randint(2,5)):
        src+=f"(assert {lit()})\n" if r.random()<.75 else f"(assert (or {lit()} {lit()}))\n"
    return src+"(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=30).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/am_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(OFF, OFF + N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE": print(k,p)
