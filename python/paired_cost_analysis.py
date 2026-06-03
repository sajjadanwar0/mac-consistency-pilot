#!/usr/bin/env python3
"""
paired_cost_analysis.py

PURPOSE
-------
Closes two reviewer items at once:
  (1) "the wall-clock study is underpowered / presented as confirmatory"
  (2) "add a power analysis: show n is sufficient to detect the minimum
       effect size of interest"

The original wall-clock study used an UNPAIRED design (independent sessions
per strategy), so between-session variance swamped the runtime-overhead signal
at n=30. A PAIRED design removes that variance: run the same seed/workload
under each strategy, then analyse the per-pair difference. This script does the
paired analysis and reports, per workload and strategy pair:
  * paired mean delta (strategyB - strategyA),
  * 95% paired-bootstrap CI on the mean delta,
  * a sign-flip permutation p-value (exact-ish, distribution-free),
  * the observed paired SD,
  * the MINIMUM DETECTABLE EFFECT (MDE) at alpha=0.05, power=0.80 for the
    achieved n -- i.e. the smallest true overhead this design could detect.
If your effect-size-of-interest (say, 10% of vanilla cost) is >= MDE, the study
is adequately powered; if it is < MDE you need more pairs (the script also
prints the n required to reach a target MDE).

INPUT
-----
A CSV with one row per session and columns:
    workload,strategy,seed,total_tokens,wallclock_s,aborts
Pairing is on (workload, seed): for a given workload and seed, the rows for
different strategies form a matched set. Produce this CSV from your harness
(see HARNESS NOTE below).

USAGE
-----
  pip install numpy scipy
  python paired_cost_analysis.py runs.csv --metric total_tokens
  python paired_cost_analysis.py runs.csv --metric wallclock_s --baseline vanilla

HARNESS NOTE (how to generate runs.csv with a PAIRED design)
------------------------------------------------------------
Modify wallclock_cost_study.py so the seed loop is OUTERMOST and the SAME seed
drives all three strategies in a triple (do not redraw per strategy):

    for seed in seeds:                       # e.g. range(60) for n=60 pairs
        for workload in ["edit_review","plan_execute","triage"]:
            random.seed(seed); set_all_rng(seed)     # identical inputs
            for strategy in ["vanilla","pessimistic","ssi"]:
                # IMPORTANT: re-seed to the SAME seed before each strategy so
                # the LLM inputs/tool-mock draws are identical across strategies
                set_all_rng(seed)
                r = run_session(workload, strategy, seed)
                writer.writerow([workload, strategy, seed,
                                 r["total_tokens"], r["wallclock_s"], r["aborts"]])

To raise contention (so triage actually exercises the guard), increase the
write-conflict probability in the triage workload (e.g. make engineer and
triager both write the same cell with prob 0.6), and/or add a genuine
write-write contention cell. Higher contention -> larger true overhead ->
easier to detect at fixed n. For zero API jitter, point the client at a local
vLLM server (same model weights) instead of the hosted API.
"""
from __future__ import annotations
import argparse
import csv
import sys
from collections import defaultdict

import numpy as np
from scipy.stats import norm


def load(path: str):
    rows = []
    with open(path) as f:
        for r in csv.DictReader(f):
            rows.append(r)
    return rows


def paired_series(rows, workload, metric, base, other):
    """Return matched arrays (base_vals, other_vals) aligned on seed."""
    by_seed = defaultdict(dict)
    for r in rows:
        if r["workload"] != workload:
            continue
        try:
            by_seed[r["seed"]][r["strategy"]] = float(r[metric])
        except (KeyError, ValueError):
            continue
    a, b = [], []
    for seed, d in by_seed.items():
        if base in d and other in d:
            a.append(d[base]); b.append(d[other])
    return np.array(a), np.array(b)


def paired_bootstrap_ci(delta, n_boot=10000, alpha=0.05, seed=0):
    rng = np.random.default_rng(seed)
    k = len(delta)
    means = np.empty(n_boot)
    for i in range(n_boot):
        idx = rng.integers(0, k, k)
        means[i] = delta[idx].mean()
    lo = np.percentile(means, 100 * alpha / 2)
    hi = np.percentile(means, 100 * (1 - alpha / 2))
    return lo, hi


def sign_flip_p(delta, n_perm=20000, seed=0):
    """Two-sided permutation test: randomly flip signs of paired deltas."""
    rng = np.random.default_rng(seed)
    obs = abs(delta.mean())
    k = len(delta)
    count = 0
    for _ in range(n_perm):
        signs = rng.choice([-1.0, 1.0], k)
        if abs((delta * signs).mean()) >= obs - 1e-12:
            count += 1
    return (count + 1) / (n_perm + 1)


def mde(sd_pair, n, alpha=0.05, power=0.80):
    """Minimum detectable mean paired difference for a paired z/t test."""
    if n <= 1 or sd_pair == 0:
        return float("nan")
    z = norm.ppf(1 - alpha / 2) + norm.ppf(power)
    return z * sd_pair / np.sqrt(n)


def n_for_mde(sd_pair, target, alpha=0.05, power=0.80):
    if target <= 0 or sd_pair == 0:
        return float("nan")
    z = norm.ppf(1 - alpha / 2) + norm.ppf(power)
    return (z * sd_pair / target) ** 2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("csv")
    ap.add_argument("--metric", default="total_tokens",
                    choices=["total_tokens", "wallclock_s", "aborts"])
    ap.add_argument("--baseline", default="vanilla")
    ap.add_argument("--target-frac", type=float, default=0.10,
                    help="effect size of interest as fraction of baseline mean")
    args = ap.parse_args()

    rows = load(args.csv)
    workloads = sorted({r["workload"] for r in rows})
    strategies = sorted({r["strategy"] for r in rows})
    others = [s for s in strategies if s != args.baseline]
    if not others:
        print("no non-baseline strategies found", file=sys.stderr); return

    print(f"metric={args.metric}  baseline={args.baseline}  "
          f"target effect = {args.target_frac:.0%} of baseline mean\n")
    hdr = (f"{'workload':14}{'strategy':12}{'n':>4}{'base_mean':>11}"
           f"{'paired_d':>10}{'95% CI':>20}{'perm_p':>9}{'MDE':>10}{'powered?':>9}")
    print(hdr); print("-" * len(hdr))

    for wl in workloads:
        for oth in others:
            a, b = paired_series(rows, wl, args.metric, args.baseline, oth)
            n = len(a)
            if n < 2:
                print(f"{wl:14}{oth:12}{n:>4}  (insufficient pairs)")
                continue
            delta = b - a
            base_mean = a.mean()
            d_mean = delta.mean()
            lo, hi = paired_bootstrap_ci(delta)
            p = sign_flip_p(delta)
            sd = delta.std(ddof=1)
            this_mde = mde(sd, n)
            target = args.target_frac * base_mean
            powered = "yes" if this_mde <= target else "NO"
            ci = f"[{lo:+.3g}, {hi:+.3g}]"
            print(f"{wl:14}{oth:12}{n:>4}{base_mean:>11.3g}{d_mean:>+10.3g}"
                  f"{ci:>20}{p:>9.3f}{this_mde:>10.3g}{powered:>9}")
            if powered == "NO":
                need = n_for_mde(sd, target)
                print(f"{'':26}-> to detect {target:.3g} at power .80 you need "
                      f"~{need:.0f} pairs (have {n})")
    print("\nNotes:")
    print(" * paired_d>0 means the strategy costs MORE than baseline on matched inputs.")
    print(" * 95% CI excluding 0 => statistically separable overhead at this n.")
    print(" * MDE is the smallest true overhead detectable at alpha=.05, power=.80")
    print("   for the achieved n; compare it to your effect-size-of-interest.")


if __name__ == "__main__":
    main()