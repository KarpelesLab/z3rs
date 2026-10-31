#!/usr/bin/env python3
"""Differential soundness fuzz of quantifiers over theory sorts against z3.

Random universal / existential assertions whose binders range over BV, FP,
RoundingMode, String, Seq, a datatype or an array, mixing in a free constant
of the same sort. Only definite sat/unsat answers are compared: a DISAGREE is
a soundness bug, an unknown on either side is just counted.

Usage: scripts/fuzz_quant_sorts.py <z3rs> <z3> <n> <outdir>
"""
import random,subprocess,sys,concurrent.futures
from collections import Counter
RS,Z3,N,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
DT="(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n"
def atoms(r,srt,x,c):
    if srt.startswith("(_ BitVec"):
        w=int(srt.split()[2][:-1]); k=lambda: f"(_ bv{r.randint(0,(1<<w)-1)} {w})"
        return [f"(bvule {x} {k()})",f"(= (bvadd {x} {k()}) {c})",f"(bvult {c} {x})",
                f"(= (bvand {x} {c}) {x})",f"(= {x} {c})",f"(bvsle {x} {k()})"]
    if srt=="Float16":
        one="((_ to_fp 5 11) RNE 1.0)"
        return [f"(fp.isNaN {x})",f"(fp.leq {x} {c})",f"(fp.eq {x} {x})",f"(= {x} {c})",
                f"(fp.isZero (fp.mul RNE {x} {c}))",f"(fp.lt {x} {one})",f"(fp.isInfinite {x})",
                f"(= (fp.abs {x}) {x})"]
    if srt=="RoundingMode":
        return [f"(= {x} RNE)",f"(= {x} {c})",f"(= {x} RTZ)",f"(not (= {x} RTP))"]
    if srt=="String":
        return [f"(= (str.len {x}) 0)",f"(str.prefixof {c} {x})",f"(= {x} {c})",
                f"(str.in_re {x} (re.* (str.to_re \"a\")))",f"(<= (str.len {x}) (str.len {c}))",
                f"(= (str.++ {x} \"\") {x})",f"(str.contains {x} \"b\")"]
    if srt=="(Seq Int)":
        return [f"(= (seq.len {x}) 0)",f"(= {x} {c})",f"(seq.prefixof {c} {x})",
                f"(= (seq.++ {x} (as seq.empty (Seq Int))) {x})"]
    if srt=="L":
        return [f"((_ is cons) {x})",f"(= {x} {c})",f"(= (hd {x}) 5)",f"(= {x} nil)",
                f"(not (= (tl {x}) {x}))",f"(< (hd {x}) (hd {c}))"]
    if srt=="(Array Int Int)":
        return [f"(= (select {x} 0) 0)",f"(= {x} {c})",f"(= (select {x} 1) (select {c} 1))",
                f"(= (store {x} 0 1) {x})"]
SORTS=["(_ BitVec 4)","(_ BitVec 12)","Float16","RoundingMode","String","(Seq Int)","L","(Array Int Int)"]
def gen(r):
    srt=r.choice(SORTS); pre=DT if srt=="L" else ""
    pre+=f"(declare-const c {srt})\n"
    def fm(x,d):
        at=atoms(r,srt,x,"c"); k=r.random()
        if d>=2 or k<.4: return r.choice(at)
        if k<.6: return f"(or {fm(x,d+1)} {fm(x,d+1)})"
        if k<.8: return f"(and {fm(x,d+1)} {fm(x,d+1)})"
        return f"(not {fm(x,d+1)})"
    q=r.choice(["forall","exists"])
    body=fm("x",0)
    if r.random()<.3:
        q2=r.choice(["forall","exists"])
        body=f"({q2} ((y {srt})) (or {body} {fm('y',1)}))"
    a=pre+f"(assert ({q} ((x {srt})) {body}))\n"
    if r.random()<.5: a+=f"(assert {r.choice(atoms(r,srt,'c','c'))})\n"
    return a+"(check-sat)\n"
def run(c,p):
    try: return subprocess.run([c,p],capture_output=True,text=True,timeout=20).stdout.strip().split("\n")[0]
    except subprocess.TimeoutExpired: return "timeout"
def one(i):
    p=f"{OUT}/qs_{i}.smt2"; open(p,"w").write(gen(random.Random(i)))
    a,b=run(RS,p),run(Z3,p)
    if a in("sat","unsat") and b in("sat","unsat"): return ("agree" if a==b else "DISAGREE"),p
    return f"{a}/{b}",p
res=list(concurrent.futures.ThreadPoolExecutor(8).map(one,range(N)))
print(Counter(k for k,_ in res))
for k,p in res:
    if k=="DISAGREE" or k.startswith("(error"): print(k,p)
