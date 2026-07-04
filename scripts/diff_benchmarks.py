#!/usr/bin/env python3
"""Differential-test z3rs against upstream z3 over a directory of .smt2 files.

Usage:  python3 scripts/diff_benchmarks.py <glob-or-dir> [timeout_s]

Runs `./target/debug/z3rs <file>` and `z3 <file>`, compares the position-wise
(check-sat) verdict lines, and reports aggregate agreement. A z3rs `unknown`
(sound abstention) never counts as a disagreement; only differing definite
sat/unsat verdicts do. z3's own test suite is C++ unit tests of its internals
and cannot be run against z3rs — this SMT-LIB2 black-box comparison is the
runnable equivalent (see ROADMAP §7).
"""
import subprocess, sys, glob, os

Z3RS = "./target/debug/z3rs"
DEFINITE = ("sat", "unsat")
ERR_MARKERS = ("error", "unsupported", "unknown symbol", "unknown function", "unknown sort")


def verdicts(cmd, timeout):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    out = r.stdout
    v = [l.strip() for l in out.splitlines() if l.strip() in ("sat", "unsat", "unknown")]
    err = "error" if (any(m in out.lower() for m in ERR_MARKERS) or r.returncode not in (0, 1)) else None
    return v, err


def main():
    pat = sys.argv[1] if len(sys.argv) > 1 else "**/*.smt2"
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    if os.path.isdir(pat):
        pat = os.path.join(pat, "**", "*.smt2")
    files = sorted(glob.glob(pat, recursive=True))
    agree = disagree = unk = err = tmo = z3fail = 0
    mismatches = []
    for f in files:
        ours, oerr = verdicts([Z3RS, f], timeout)
        if oerr == "timeout":
            tmo += 1; continue
        if oerr == "error":
            err += 1; continue
        theirs, _ = verdicts(["z3", f], timeout)
        if not theirs:
            z3fail += 1; continue
        bad = False
        for o, t in zip(ours, theirs):
            if o == "unknown":
                unk += 1
            elif o in DEFINITE and t in DEFINITE and o != t:
                bad = True
        (mismatches.append((os.path.basename(f), ours, theirs)) or None) if bad else None
        agree += 0 if bad else 1
        disagree += 1 if bad else 0
    print(f"files={len(files)} agree={agree} disagree={disagree} "
          f"z3rs_unknown_lines={unk} z3rs_gap(error)={err} z3rs_timeout={tmo} z3_no_verdict={z3fail}")
    for name, o, t in mismatches:
        print(f"  MISMATCH {name}: z3rs={o} z3={t}")
    sys.exit(1 if disagree else 0)


if __name__ == "__main__":
    main()
