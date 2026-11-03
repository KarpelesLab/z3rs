#!/usr/bin/env python3
"""Compare two z3rs binaries over the cases every differential fuzzer generates.

Each scripts/fuzz_*.py is run with a recording stub in place of both solvers:
the stub snapshots every input the fuzzer hands to z3rs (with its extra
arguments) and answers `unknown`, so no solver work is done while generating.
Then both binaries run every recorded case (same worker, back to back) and the
script reports, per fuzzer:

  FLIP       sat <-> unsat between OLD and NEW            (a soundness bug in one)
  REGRESS    OLD decided (sat/unsat), NEW did not          (unknown/timeout/error)
  IMPROVE    NEW decided, OLD did not
  SLOWER     NEW took more than --slow x OLD (and > --min-time s), re-timed alone
  CHANGED    any other stdout difference (models, objectives, messages)

Usage:
  scripts/regress_check.py OLD NEW [--offset K] [-n N] [--only a,b] [--skip a,b]
                           [--timeout S] [--jobs J] [--z3 Z3] [--out DIR]
                           [--slow F] [--min-time S] [--show-changed]

  --offset K   seed offset passed to every fuzzer (default 0)
  -n N         cases per fuzzer (default 100)
  --only/skip  comma-separated fuzzer names (`nlsat` or `fuzz_nlsat`)
  --z3 Z3      real z3 for generation, for fuzzers that only query z3rs after
               z3 decided (default: a stub that answers `unknown`)
  --out DIR    work directory (default: a fresh temporary directory); cases
               land in DIR/<fuzzer>/, the full table in DIR/report.tsv

Exit status 1 when any FLIP or REGRESS is found. Typical use before pushing:
  cp target/release/z3rs /tmp/z3rs_old   # from the base commit
  ... build ...
  scripts/regress_check.py /tmp/z3rs_old target/release/z3rs --only nlsat,nra_div,nia
"""
import argparse
import concurrent.futures
import glob
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The recording stub. It snapshots the input file (the last argument) at call
# time, since some fuzzers rewrite one path for several queries.
STUB = """#!/bin/sh
f=""
for a in "$@"; do f="$a"; done
if [ -n "$REGRESS_SNAP" ] && [ -f "$f" ]; then
  base=$(basename "$f" .smt2)
  n=$(mktemp "$REGRESS_SNAP/$base.XXXXXX")
  cp "$f" "$n"
  mv "$n" "$n.smt2"
  extra=""
  for a in "$@"; do [ "$a" = "$f" ] || extra="$extra$a\t"; done
  printf '%s\\t%s\\n' "$n.smt2" "$extra" >> "$REGRESS_SNAP/cases.tsv"
fi
echo unknown
"""

Z3_STUB = """#!/bin/sh
echo unknown
"""


def write_exe(path, body):
    with open(path, "w") as f:
        f.write(body)
    os.chmod(path, os.stat(path).st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def fuzzers(only, skip):
    names = sorted(os.path.basename(p)[5:-3] for p in glob.glob(os.path.join(ROOT, "scripts/fuzz_*.py")))
    norm = lambda s: {x.strip().removeprefix("fuzz_").removesuffix(".py") for x in s.split(",") if x.strip()}
    if only:
        want = norm(only)
        missing = want - set(names)
        if missing:
            sys.exit(f"unknown fuzzers: {', '.join(sorted(missing))}")
        names = [n for n in names if n in want]
    if skip:
        names = [n for n in names if n not in norm(skip)]
    return names


def generate(name, args, work, stub, z3):
    """Run fuzzer `name` against the stub; return its recorded cases."""
    d = os.path.join(work, name)
    os.makedirs(os.path.join(d, "gen"), exist_ok=True)
    env = dict(os.environ, REGRESS_SNAP=d)
    cmd = [sys.executable, os.path.join(ROOT, f"scripts/fuzz_{name}.py"), stub, z3, str(args.n),
           os.path.join(d, "gen"), str(args.offset)]
    try:
        subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=args.gen_timeout)
    except subprocess.TimeoutExpired:
        print(f"  [{name}] generation timed out; using the cases recorded so far", file=sys.stderr)
    cases = []
    tsv = os.path.join(d, "cases.tsv")
    if os.path.exists(tsv):
        for line in open(tsv):
            parts = line.rstrip("\n").split("\t")
            cases.append((parts[0], [p for p in parts[1:] if p]))
    return cases


def run(binary, case, timeout):
    path, extra = case
    t0 = time.monotonic()
    try:
        p = subprocess.run([binary, *extra, path], capture_output=True, text=True, timeout=timeout)
        out = p.stdout
        if p.returncode not in (0, 1) and not out.strip():
            out = f"crash (exit {p.returncode})"
    except subprocess.TimeoutExpired:
        out = "timeout"
    return out, time.monotonic() - t0


def head(out):
    lines = out.strip().split("\n")
    return lines[0].strip() if lines else ""


def decided(h):
    return h in ("sat", "unsat")


def classify(o, n, args):
    ho, hn = head(o[0]), head(n[0])
    if decided(ho) and decided(hn) and ho != hn:
        return "FLIP"
    if decided(ho) and not decided(hn):
        return "REGRESS"
    if decided(hn) and not decided(ho):
        return "IMPROVE"
    if n[1] > args.slow * o[1] and n[1] > args.min_time:
        return "SLOWER"
    if o[0] != n[0]:
        return "CHANGED"
    return "same"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("old")
    ap.add_argument("new")
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("-n", type=int, default=100)
    ap.add_argument("--only", default="")
    ap.add_argument("--skip", default="")
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--gen-timeout", type=float, default=600.0)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 4) // 2))
    ap.add_argument("--z3", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--slow", type=float, default=2.0)
    ap.add_argument("--min-time", type=float, default=0.3)
    ap.add_argument("--show-changed", action="store_true")
    args = ap.parse_args()
    old, new = os.path.abspath(args.old), os.path.abspath(args.new)
    for b in (old, new):
        if not os.access(b, os.X_OK):
            sys.exit(f"not executable: {b}")
    work = args.out or tempfile.mkdtemp(prefix="regress_check_")
    os.makedirs(work, exist_ok=True)
    stub = os.path.join(work, "stub_z3rs.sh")
    write_exe(stub, STUB)
    z3 = args.z3
    if not z3:
        z3 = os.path.join(work, "stub_z3.sh")
        write_exe(z3, Z3_STUB)
    names = fuzzers(args.only, args.skip)
    print(f"work dir: {work}; {len(names)} fuzzers, {args.n} cases each at offset {args.offset}")

    # Generate (each fuzzer runs its own small thread pool; a few at a time).
    all_cases = {}
    with concurrent.futures.ThreadPoolExecutor(max(1, args.jobs // 4)) as ex:
        futs = {ex.submit(generate, nm, args, work, stub, z3): nm for nm in names}
        for f in concurrent.futures.as_completed(futs):
            all_cases[futs[f]] = f.result()
    flat = [(nm, c) for nm in names for c in all_cases[nm]]
    print(f"{len(flat)} cases recorded")

    def both(item):
        nm, c = item
        o = run(old, c, args.timeout)
        n = run(new, c, args.timeout)
        return nm, c, o, n

    results = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        for r in ex.map(both, flat):
            results.append(r)

    # Confirm slowdowns alone (parallel timing is noisy).
    final = []
    for nm, c, o, n in results:
        k = classify(o, n, args)
        if k == "SLOWER":
            o2, n2 = run(old, c, args.timeout), run(new, c, args.timeout)
            o, n = (o[0], min(o[1], o2[1])), (n[0], min(n[1], n2[1]))
            k = classify(o, n, args)
        final.append((nm, c, o, n, k))

    per = defaultdict(Counter)
    with open(os.path.join(work, "report.tsv"), "w") as f:
        f.write("fuzzer\tkind\tcase\told\tnew\told_s\tnew_s\n")
        for nm, c, o, n, k in final:
            per[nm][k] += 1
            f.write(f"{nm}\t{k}\t{c[0]}\t{head(o[0])}\t{head(n[0])}\t{o[1]:.2f}\t{n[1]:.2f}\n")
    total = Counter()
    for nm in names:
        total.update(per[nm])
        bad = {k: v for k, v in per[nm].items() if k != "same"}
        print(f"  {nm:24} {sum(per[nm].values()):5} cases  {dict(sorted(bad.items())) if bad else 'same'}")
    print(f"TOTAL {dict(sorted(total.items()))}")
    order = ["FLIP", "REGRESS", "SLOWER", "IMPROVE"] + (["CHANGED"] if args.show_changed else [])
    for kind in order:
        rows = [r for r in final if r[4] == kind]
        if rows:
            print(f"--- {kind} ({len(rows)}) ---")
            for nm, c, o, n, _ in rows:
                ex = " ".join(c[1])
                print(f"  {c[0]}{' [' + ex + ']' if ex else ''}: {head(o[0])} {o[1]:.2f}s -> {head(n[0])} {n[1]:.2f}s")
    print(f"report: {os.path.join(work, 'report.tsv')}")
    sys.exit(1 if total["FLIP"] or total["REGRESS"] else 0)


if __name__ == "__main__":
    main()
