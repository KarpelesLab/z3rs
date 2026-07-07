#!/usr/bin/env python3
"""Differential harness against the z3 regression corpus (z3test/, gitignored).

For every `X.smt2` with a companion `X.expected.out`, run z3rs and compare its
combined stdout+stderr byte-for-byte to the expected output — exactly what z3's own
`test_benchmark` does with `filecmp.cmp`. Failures are bucketed so the output-format
gap can be closed systematically:

  PASS            byte-for-byte identical
  VERDICT         differing definite sat/unsat          (SOUNDNESS bug)
  FORMAT          same verdicts, bytes differ           (model/echo/whitespace)
  DECLINE         z3rs unknown where z3 was definite     (completeness gap)
  UNSUPPORTED     z3rs printed an error / unsupported    (missing feature)
  TIMEOUT         z3rs exceeded the time budget
  Z3-INDEFINITE   expected itself is unknown/empty       (skipped from the ratio)

Usage: scripts/z3test_diff.py [subdir ...] [--timeout S] [--limit N] [--show K]
"""
import os, sys, subprocess, concurrent.futures

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
Z3RS = os.path.join(ROOT, "target/release/z3rs")
CORPUS = os.path.join(ROOT, "z3test")
VERDICTS = {"sat", "unsat", "unknown"}


def verdict_seq(text):
    return [ln.strip() for ln in text.splitlines() if ln.strip() in VERDICTS]


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
        return ("TIMEOUT", smt2, exp_text, "<timeout>")
    prod_text = produced.decode("utf-8", "replace")
    if produced == expected:
        return ("PASS", smt2, exp_text, prod_text)
    prod_verd = verdict_seq(prod_text)
    # A z3rs error / unsupported construct.
    low = prod_text.lower()
    unsupported = any(k in low for k in ("error", "unsupported", "unexpected", "cannot", "panic"))
    if prod_verd == exp_verd and exp_verd:
        return ("FORMAT", smt2, exp_text, prod_text)
    # Definite disagreement: both produced a definite verdict at some position that differs.
    for a, b in zip(exp_verd, prod_verd):
        if a in ("sat", "unsat") and b in ("sat", "unsat") and a != b:
            return ("VERDICT", smt2, exp_text, prod_text)
    if not exp_verd:
        return ("Z3-INDEFINITE", smt2, exp_text, prod_text)
    if unsupported or not prod_verd:
        return ("UNSUPPORTED", smt2, exp_text, prod_text)
    # z3rs produced verdict(s) with no definite clash → an unknown where z3 decided.
    return ("DECLINE", smt2, exp_text, prod_text)


def main():
    args = sys.argv[1:]
    timeout = 10.0
    limit = None
    show = 8
    subdirs = []
    i = 0
    while i < len(args):
        if args[i] == "--timeout":
            timeout = float(args[i + 1]); i += 2
        elif args[i] == "--limit":
            limit = int(args[i + 1]); i += 2
        elif args[i] == "--show":
            show = int(args[i + 1]); i += 2
        else:
            subdirs.append(args[i]); i += 1
    if not subdirs:
        subdirs = ["regressions/smt2"]
    files = []
    for sd in subdirs:
        base = os.path.join(CORPUS, sd)
        for dp, _, fns in os.walk(base):
            for fn in fns:
                if fn.endswith(".smt2"):
                    files.append(os.path.join(dp, fn))
    files.sort()
    if limit:
        files = files[:limit]
    buckets = {k: [] for k in ("PASS", "FORMAT", "VERDICT", "DECLINE", "UNSUPPORTED", "TIMEOUT", "Z3-INDEFINITE")}
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        for res in ex.map(lambda f: run_one(f, timeout), files):
            if res:
                buckets[res[0]].append(res)
    total = sum(len(v) for v in buckets.values())
    definite = total - len(buckets["Z3-INDEFINITE"])
    print(f"corpus: {total} files ({definite} with a definite z3 verdict)\n")
    for k in ("PASS", "FORMAT", "DECLINE", "UNSUPPORTED", "VERDICT", "TIMEOUT", "Z3-INDEFINITE"):
        print(f"  {k:14} {len(buckets[k])}")
    print(f"\nbyte-for-byte PASS: {len(buckets['PASS'])}/{definite} "
          f"({100*len(buckets['PASS'])/max(1,definite):.1f}%)")
    if buckets["VERDICT"]:
        print(f"\n*** {len(buckets['VERDICT'])} VERDICT DISAGREEMENTS (soundness/completeness) ***")
        for _, f, e, p in buckets["VERDICT"][:show]:
            print(f"  {os.path.relpath(f, CORPUS)}: exp={verdict_seq(e)} got={verdict_seq(p)}")
    for bucket in ("FORMAT", "UNSUPPORTED"):
        if buckets[bucket]:
            print(f"\n--- sample {bucket} ---")
            for _, f, e, p in buckets[bucket][:show]:
                print(f"  {os.path.relpath(f, CORPUS)}")
                print(f"    exp: {e[:120]!r}")
                print(f"    got: {p[:120]!r}")


if __name__ == "__main__":
    main()
