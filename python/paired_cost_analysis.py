#!/usr/bin/env python3
"""
paired_cost_analysis.py

PURPOSE
-------
Closes three reviewer items:
  (1) "the wall-clock study is underpowered / presented as confirmatory"
  (2) "add a power analysis: show n is sufficient to detect the minimum
       effect size of interest"
  (3) "overlapping CIs are absence-of-evidence, not evidence of absence --
       use an equivalence test (TOST) with a pre-declared margin"

The original wall-clock study used an UNPAIRED design (independent sessions
per strategy), so between-session variance swamped the runtime-overhead signal
at n=30. A PAIRED design removes that variance: run the same seed/workload
under each strategy, then analyse the per-pair difference. This script does the
paired analysis and reports, per workload and strategy pair:
  * paired mean delta (strategyB - strategyA),
  * 95% paired-bootstrap CI on the mean delta (difference test),
  * a sign-flip permutation p-value (exact-ish, distribution-free),
  * the observed paired SD,
  * the MINIMUM DETECTABLE EFFECT (MDE) at alpha=0.05, power=0.80,
  * TOST EQUIVALENCE: whether the 90% paired-bootstrap CI lies entirely
    inside the PRE-DECLARED margin +/- delta, where delta = target_frac x
    baseline mean (CI-inclusion TOST at alpha=0.05), plus the parametric
    two-one-sided-t p-value as a secondary check.

PRE-REGISTRATION DISCIPLINE (read before running)
-------------------------------------------------
The equivalence margin is delta = TARGET_FRAC x baseline mean, with
TARGET_FRAC = 0.10 by default. This is the SAME effect-size-of-interest the
MDE analysis already uses, declared before any TOST was computed; do NOT
tune it after seeing results (margin-shopping converts an equivalence test
into a rhetorical device, and a competent reviewer will ask when the margin
was fixed). If you need a different margin, justify it from external cost
considerations and state in the paper that it was set a priori.

VERDICT TAXONOMY (the four honest outcomes)
-------------------------------------------
  EQUIVALENT       90% CI within (-d, +d) and 95% CI includes 0:
                   evidence of absence of a practically relevant difference.
  DIFF<MARGIN      95% CI excludes 0 AND 90% CI within (-d, +d):
                   a real, statistically separable overhead that is smaller
                   than the pre-declared practical-relevance margin. Report
                   the overhead AND the equivalence; they answer different
                   questions. (Expected outcome for plan-execute tokens.)
  DIFFERENT        95% CI excludes 0 and 90% CI crosses the margin:
                   separable overhead of potentially practical size.
  INCONCLUSIVE     neither: the data cannot distinguish equivalence from
                   difference at this n. Say "inconclusive", never "no
                   overhead".

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
  python paired_cost_analysis.py runs.csv --metric total_tokens --target-frac 0.10

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
from scipy.stats import norm, t as t_dist


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


# ---------------------------------------------------------------------------
# TOST equivalence (new)
# ---------------------------------------------------------------------------

def tost_parametric_p(delta, margin):
    """Two one-sided paired t-tests against +/- margin.

    H0: |mu_d| >= margin (non-equivalence).
    p_lower tests mu_d > -margin; p_upper tests mu_d < +margin.
    Equivalence is concluded when BOTH reject, i.e. p_tost = max(p1, p2)
    < alpha. Parametric; treat as secondary to the bootstrap-CI inclusion
    when n is small or deltas are skewed (token counts often are).
    """
    n = len(delta)
    if n < 2:
        return float("nan")
    m = delta.mean()
    se = delta.std(ddof=1) / np.sqrt(n)
    if se == 0:
        return 0.0 if abs(m) < margin else 1.0
    df = n - 1
    t_lower = (m + margin) / se   # H1: mu_d > -margin
    t_upper = (m - margin) / se   # H1: mu_d < +margin
    p_lower = 1 - t_dist.cdf(t_lower, df)
    p_upper = t_dist.cdf(t_upper, df)
    return max(p_lower, p_upper)


def tost_verdict(delta, margin, alpha=0.05, seed=0):
    """CI-inclusion TOST (primary) + difference test, combined verdict.

    Equivalence at level alpha  <=>  the (1 - 2*alpha) CI of the paired mean
    lies inside (-margin, +margin). With alpha=0.05 that is the 90% CI.
    Difference at level alpha   <=>  the 95% CI excludes 0.
    Returns (verdict, ci90, ci95, p_tost).
    """
    lo90, hi90 = paired_bootstrap_ci(delta, alpha=2 * alpha, seed=seed)
    lo95, hi95 = paired_bootstrap_ci(delta, alpha=alpha, seed=seed)
    equivalent = (-margin < lo90) and (hi90 < margin)
    different = (lo95 > 0) or (hi95 < 0)
    p = tost_parametric_p(delta, margin)
    if equivalent and not different:
        v = "EQUIVALENT"
    elif equivalent and different:
        v = "DIFF<MARGIN"
    elif different:
        v = "DIFFERENT"
    else:
        v = "INCONCLUSIVE"
    return v, (lo90, hi90), (lo95, hi95), p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("csv")
    ap.add_argument("--metric", default="total_tokens",
                    choices=["total_tokens", "wallclock_s", "aborts"])
    ap.add_argument("--baseline", default="vanilla")
    ap.add_argument("--target-frac", type=float, default=0.10,
                    help="PRE-DECLARED effect size of interest / equivalence "
                         "margin, as a fraction of the baseline mean. Do not "
                         "tune after seeing results.")
    args = ap.parse_args()

    rows = load(args.csv)
    workloads = sorted({r["workload"] for r in rows})
    strategies = sorted({r["strategy"] for r in rows})
    others = [s for s in strategies if s != args.baseline]
    if not others:
        print("no non-baseline strategies found", file=sys.stderr); return

    print(f"metric={args.metric}  baseline={args.baseline}")
    print(f"PRE-DECLARED margin: delta = {args.target_frac:.0%} of baseline "
          f"mean (same constant drives MDE and TOST; fixed a priori)\n")
    hdr = (f"{'workload':14}{'strategy':12}{'n':>4}{'base_mean':>11}"
           f"{'paired_d':>10}{'95% CI':>20}{'perm_p':>9}{'MDE':>10}"
           f"{'90% CI':>20}{'margin':>9}{'tost_p':>8}  verdict")
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
            margin = args.target_frac * base_mean
            verdict, ci90, ci95, p_tost = tost_verdict(delta, margin)
            ci_s = f"[{lo:+.3g}, {hi:+.3g}]"
            ci90_s = f"[{ci90[0]:+.3g}, {ci90[1]:+.3g}]"
            print(f"{wl:14}{oth:12}{n:>4}{base_mean:>11.3g}{d_mean:>+10.3g}"
                  f"{ci_s:>20}{p:>9.3f}{this_mde:>10.3g}"
                  f"{ci90_s:>20}{margin:>9.3g}{p_tost:>8.3f}  {verdict}")
            if verdict == "INCONCLUSIVE":
                need = n_for_mde(sd, margin)
                print(f"{'':26}-> inconclusive at n={n}; ~{need:.0f} pairs "
                      f"needed to power the margin")
    print("\nNotes:")
    print(" * paired_d>0 means the strategy costs MORE than baseline on matched inputs.")
    print(" * 95% CI excluding 0 => statistically separable overhead (difference test).")
    print(" * 90% CI inside +/-margin => equivalence at alpha=.05 (CI-inclusion TOST).")
    print(" * DIFF<MARGIN = both at once: a real overhead smaller than the pre-declared")
    print("   practical-relevance margin. Report the overhead AND the equivalence.")
    print(" * tost_p is the parametric two-one-sided-t secondary check (normality")
    print("   assumption; trust the bootstrap CI when they disagree at small n).")
    print(" * MDE is the smallest true overhead detectable at alpha=.05, power=.80.")


if __name__ == "__main__":
    main()