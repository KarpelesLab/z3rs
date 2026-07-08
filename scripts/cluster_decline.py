#!/usr/bin/env python3
import os, sys, subprocess, concurrent.futures, re, collections

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
Z3RS = os.path.join(ROOT, "target/release/z3rs")
CORPUS = os.path.join(ROOT, "z3test")
VERDICTS = {"sat", "unsat", "unknown"}

def verdict_seq(text):
    return [ln.strip() for ln in text.splitlines() if ln.strip() in VERDICTS]

def logic_of(path):
    try:
        with open(path, errors="replace") as f:
            t = f.read()
    except Exception:
        return "?", set()
    m = re.search(r"\(set-logic\s+([A-Za-z0-9_]+)\)", t)
    logic = m.group(1) if m else "NONE"
    ops = set(re.findall(r"[\(\s]((?:fp\.[a-z]+)|(?:bv[a-z]+)|(?:str\.[a-z.]+)|(?:seq\.[a-z.]+)|(?:re\.[a-z.]+)|(?:_ [a-z0-9_]+)|is_int|to_int|to_real|distinct)", t))
    return logic, ops

def run_one(smt2, timeout):
    exp_path = smt2[:-5] + ".expected.out"
    if not os.path.exists(exp_path):
        return None
    with open(exp_path, "rb") as f:
        expected = f.read()
    exp_text = expected.decode("utf-8", "replace")
    exp_verd = verdict_seq(exp_text)
    try:
        p = subprocess.run([Z3RS, smt2], capture_output=True, timeout=timeout)
        produced = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return None
    prod_text = produced.decode("utf-8", "replace")
    if produced == expected:
        return None
    prod_verd = verdict_seq(prod_text)
    low = prod_text.lower()
    unsupported = any(k in low for k in ("error", "unsupported", "unexpected", "cannot", "panic"))
    if prod_verd == exp_verd and exp_verd:
        return None
    for a, b in zip(exp_verd, prod_verd):
        if a in ("sat", "unsat") and b in ("sat", "unsat") and a != b:
            return None
    if not exp_verd:
        return None
    if unsupported or not prod_verd:
        return None
    # DECLINE
    logic, ops = logic_of(smt2)
    exp_def = [v for v in exp_verd if v in ("sat","unsat")]
    return (smt2, logic, ops, exp_def)

def main():
    subdirs = ["regressions/smt2", "old-regressions/smt2"]
    files = []
    for sd in subdirs:
        base = os.path.join(CORPUS, sd)
        for dp, _, fns in os.walk(base):
            for fn in fns:
                if fn.endswith(".smt2"):
                    files.append(os.path.join(dp, fn))
    files.sort()
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        for res in ex.map(lambda f: run_one(f, 8.0), files):
            if res:
                results.append(res)
    print(f"DECLINE total: {len(results)}\n")
    bylogic = collections.Counter(r[1] for r in results)
    print("=== by logic ===")
    for k, v in bylogic.most_common():
        print(f"  {v:4d}  {k}")
    # verdict split
    print("\n=== by (logic, expected verdict) ===")
    lv = collections.Counter((r[1], tuple(sorted(set(r[3])))) for r in results)
    for k, v in lv.most_common():
        print(f"  {v:4d}  {k}")
    # list files per logic
    print("\n=== files by logic ===")
    perlogic = collections.defaultdict(list)
    for r in results:
        perlogic[r[1]].append(r)
    for lg, rs in sorted(perlogic.items(), key=lambda x: -len(x[1])):
        print(f"\n## {lg}  ({len(rs)})")
        for smt2, logic, ops, exp in rs:
            rel = os.path.relpath(smt2, CORPUS)
            opss = ",".join(sorted(ops))[:80]
            print(f"  {'/'.join(exp):12s} {rel}  [{opss}]")

if __name__ == "__main__":
    main()
