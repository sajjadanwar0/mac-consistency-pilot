#!/usr/bin/env python3
"""mast_anomaly_capable.py -- re-base the MAST A1 rate on the
anomaly-capable denominator.

The headline "0 of 600" includes traces that cannot exhibit A1 by
construction (e.g. single-operation sessions: MetaGPT ~1.0 events/sess,
AG2 ~1.4). A1 (stale-generation) requires a SHARED CELL: a cell read by
one operation and written by a different operation in the same trace.
This script partitions the parsed MAST traces into A1-capable and
not-capable, recomputes the A1 firing rate over the capable subset, and
reports an exact Clopper-Pearson interval on that honest denominator.

Definition (A1-capable): a trace t is A1-capable iff there exist two
distinct operation records i != j in t and a cell c such that
c in read_set(op_i) and c in write_set(op_j). (The read need not precede
the write; capability is structural, not temporal. detect_a1 then applies
the temporal test to decide actual firing.)

Usage:
  python3 mast_anomaly_capable.py --traces <dir-of-parsed-mast-jsonl>
  # point --traces at whatever directory holds the 600 parsed MAST
  # op-record traces (the ones analyse.py / the MAST run consumed).

Outputs per framework and overall:
  n_parsed, n_capable, n_fired, A1 rate over capable, 95% Clopper-Pearson.
Prints a SCHEMA DUMP and aborts if it cannot find read_set/write_set.
"""
import argparse, glob, json, math, os, sys
from pathlib import Path

# Reuse the project's own loader/detector if importable; else fall back.
def _import_detectors():
    for p in ("python/baselines", "baselines", "."):
        if os.path.exists(os.path.join(p, "detectors.py")):
            sys.path.insert(0, p)
            try:
                from detectors import detect_a1, load_trace
                return detect_a1, load_trace
            except Exception:
                pass
    return None, None

DETECT_A1, LOAD_TRACE = _import_detectors()

def load_trace_fallback(path):
    recs = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                recs.append(json.loads(line))
    return recs

def is_a1_capable(recs):
    """Structural: some cell is read by one op and written by a different op."""
    n = len(recs)
    for i in range(n):
        rs = set(recs[i].get("read_set", []) or [])
        if not rs:
            continue
        for j in range(n):
            if i == j:
                continue
            ws = set(recs[j].get("write_set", []) or [])
            if rs & ws:
                return True
    return False

def clopper_pearson(k, n, alpha=0.05):
    """Exact CI for a binomial proportion. Returns (lo, hi) as fractions."""
    if n == 0:
        return (float("nan"), float("nan"))
    # Use the Beta-quantile form via a simple bisection on the regularized
    # incomplete beta (no scipy dependency).
    from math import lgamma, log, exp
    def betacf(a, b, x):
        MAXIT, EPS, FPMIN = 200, 3e-12, 1e-300
        qab, qap, qam = a+b, a+1.0, a-1.0
        c = 1.0; d = 1.0 - qab*x/qap
        if abs(d) < FPMIN: d = FPMIN
        d = 1.0/d; h = d
        for m in range(1, MAXIT+1):
            m2 = 2*m
            aa = m*(b-m)*x/((qam+m2)*(a+m2))
            d = 1.0+aa*d
            if abs(d) < FPMIN: d = FPMIN
            c = 1.0+aa/c
            if abs(c) < FPMIN: c = FPMIN
            d = 1.0/d; h *= d*c
            aa = -(a+m)*(qab+m)*x/((a+m2)*(qap+m2))
            d = 1.0+aa*d
            if abs(d) < FPMIN: d = FPMIN
            c = 1.0+aa/c
            if abs(c) < FPMIN: c = FPMIN
            d = 1.0/d; de = d*c; h *= de
            if abs(de-1.0) < EPS: break
        return h
    def betai(a, b, x):
        if x <= 0.0: return 0.0
        if x >= 1.0: return 1.0
        lbeta = lgamma(a+b)-lgamma(a)-lgamma(b)+a*log(x)+b*log(1.0-x)
        bt = exp(lbeta)
        if x < (a+1.0)/(a+b+2.0):
            return bt*betacf(a, b, x)/a
        return 1.0 - bt*betacf(b, a, 1.0-x)/b
    def invbeta(p, a, b):
        lo, hi = 0.0, 1.0
        for _ in range(200):
            mid = (lo+hi)/2.0
            if betai(a, b, mid) < p: lo = mid
            else: hi = mid
        return (lo+hi)/2.0
    lo = 0.0 if k == 0 else invbeta(alpha/2, k, n-k+1)
    hi = 1.0 if k == n else invbeta(1-alpha/2, k+1, n-k)
    return (lo, hi)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--traces", required=True,
                    help="dir of parsed MAST op-record jsonl (recursively globbed)")
    ap.add_argument("--by-framework", action="store_true",
                    help="if trace files are under <dir>/<framework>/*.jsonl, split")
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(args.traces, "**", "*.jsonl"),
                             recursive=True))
    if not files:
        sys.exit("no *.jsonl under %s" % args.traces)

    load = LOAD_TRACE or load_trace_fallback
    detect = DETECT_A1
    if detect is None:
        sys.exit("could not import detect_a1 from detectors.py; run from the "
                 "repo root or place detectors.py on the path.")

    # schema check on first trace
    first = load(Path(files[0]))
    if not first or ("read_set" not in first[0] and "write_set" not in first[0]):
        print("SCHEMA DUMP (first record):")
        if first:
            for k, v in first[0].items():
                print("  %s: %r" % (k, v))
        sys.exit("traces lack read_set/write_set; point --traces at the parsed "
                 "op-record traces, not raw MAST logs.")

    def framework_of(path):
        # Two layouts supported:
        #  (1) <dir>/<framework>/file.jsonl   -> framework is the subdir
        #  (2) flat: <framework>-mast-<Name>_<idx>.jsonl -> prefix before "-mast-"
        rel = os.path.relpath(path, args.traces)
        parts = rel.split(os.sep)
        if len(parts) > 1:
            return parts[0]
        base = os.path.basename(path)
        if "-mast-" in base:
            return base.split("-mast-")[0]
        return "all"

    agg = {}  # fw -> [n_parsed, n_capable, n_fired]
    for f in files:
        recs = load(Path(f))
        fw = framework_of(f)  # auto: subdir or {fw}-mast- filename prefix
        a = agg.setdefault(fw, [0, 0, 0])
        a[0] += 1
        cap = is_a1_capable(recs)
        if cap:
            a[1] += 1
            if detect(recs) is not None:
                a[2] += 1

    print("MAST A1 rate on the ANOMALY-CAPABLE denominator")
    print("(A1-capable = some cell read by one op and written by a different op)\n")
    print("%-14s %8s %9s %7s  %s" % ("framework", "parsed", "capable",
                                     "fired", "A1 rate over capable [95% CP]"))
    tot = [0, 0, 0]
    for fw in sorted(agg):
        n, cap, fired = agg[fw]
        tot[0]+=n; tot[1]+=cap; tot[2]+=fired
        if cap:
            lo, hi = clopper_pearson(fired, cap)
            rate = "%.1f%% [%.2f, %.2f]" % (100*fired/cap, 100*lo, 100*hi)
        else:
            rate = "n/a (0 capable)"
        print("%-14s %8d %9d %7d  %s" % (fw, n, cap, fired, rate))
    n, cap, fired = tot
    lo, hi = clopper_pearson(fired, cap) if cap else (float('nan'),)*2
    print("-"*70)
    print("%-14s %8d %9d %7d  %s" % ("TOTAL", n, cap, fired,
                                     "%.1f%% [%.2f, %.2f]" % (100*fired/cap, 100*lo, 100*hi) if cap
                                     else "n/a"))
    print()
    print("Headline to report: 0 of %d anomaly-capable traces "
          "(was 0 of %d total); exact 95%% Clopper-Pearson upper bound "
          "%.2f%% on the capable denominator." % (cap, n, 100*hi if cap else 0))

if __name__ == "__main__":
    main()