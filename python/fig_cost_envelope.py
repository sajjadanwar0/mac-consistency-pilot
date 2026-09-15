#!/usr/bin/env python3
"""fig_cost_envelope.py -- regenerate Figure 2 from committed data.

WHAT CHANGED, 2026-09-14 (round 2), AND WHY
-------------------------------------------
The previous version plotted SSI token overhead against the realized abort
rate and fitted `overhead = +0% + 108% * abort_rate`.  That fit is an
accounting identity, not a measurement, and the committed data proves it:

    for every one of the 155 SSI sessions   generations = W*depth + aborts
    for every vanilla and pessimistic one   generations = W*depth

so abort_rate = aborts/(W*depth) is exactly `extra generations / baseline
generations`, and token overhead is `extra tokens / baseline tokens`.  The
slope of overhead against abort rate therefore carries one number and one
only: how much a RETRIED generation costs relative to a first-attempt one.
Plotting the two against each other and reporting R^2 = 0.94 as a "law" is
plotting x against x.  Worse, the old caption presented the collapse of the
fan-in and cell-count sweeps onto a common line as validation; any
mechanism that produces aborts lands on that line by construction.

This version reports what the identity does NOT force, which is where the
evidence actually is:

  (a) the intercept is indistinguishable from zero -- SSI has no fixed
      cost, only a per-abort one;
  (b) the slope does not steepen as contention rises -- aborts do not
      compound;
  (c) the two contention mechanisms agree on the per-abort cost, so the
      retry price is a property of the discipline, not of the workload;
  (d) a retried generation costs measurably MORE than a first-attempt one,
      and that ratio -- the only empirical content of the old 108% -- is
      what the figure now shows directly.

Panel A plots mean overhead against the swept parameter, which is what the
experimenter set, rather than against another outcome of the same run.
Panel B plots extra tokens against aborts in absolute units against the
null line "a retry costs the same as a first attempt"; the gap between the
two lines is (d).

    python3 python/fig_cost_envelope.py --out fig_cost_envelope.pdf
    python3 python/fig_cost_envelope.py --stats-only

Needs matplotlib and numpy for the figure; --stats-only needs neither.
Offline, deterministic (the bootstrap is seeded).
"""
import argparse
import json
import os
import random
import statistics as st

SRC = ["hc_curve", "hc_ceiling"]
FILE = "sessions__gpt-4o-mini.jsonl"
SEED = 20260914
BOOT = 2000


def load(base):
    rows = []
    for d in SRC:
        p = os.path.join(base, d, FILE)
        if not os.path.isfile(p):
            raise SystemExit(f"FAIL: {p} not found")
        with open(p) as fh:
            for line in fh:
                if line.strip():
                    r = json.loads(line)
                    r["_src"] = d
                    rows.append(r)
    return rows


def pair(rows):
    key = lambda r: (r["_src"], r["scenario_seed"], r["W"], r["cells"], r["depth"])
    van = {key(r): r for r in rows if r["strategy"] == "vanilla"}
    ssi = {key(r): r for r in rows if r["strategy"] == "ssi"}
    return [(van[k], ssi[k]) for k in ssi if k in van]


def ols(x, y):
    n = len(x)
    mx, my = sum(x) / n, sum(y) / n
    sxx = sum((a - mx) ** 2 for a in x)
    sxy = sum((a - mx) * (b - my) for a, b in zip(x, y))
    b1 = sxy / sxx
    b0 = my - b1 * mx
    sst = sum((b - my) ** 2 for b in y)
    ssr = sum((b - (b0 + b1 * a)) ** 2 for a, b in zip(x, y))
    return b0, b1, (1 - ssr / sst if sst else float("nan"))


def boot_ci(items, stat, rng):
    vals = sorted(stat(rng.choices(items, k=len(items))) for _ in range(BOOT))
    return vals[int(0.025 * BOOT)], vals[int(0.975 * BOOT)]


def identity_holds(rows):
    """generations = W*depth + aborts for ssi; = W*depth otherwise."""
    ok = {}
    for strat in ("vanilla", "ssi", "pessimistic"):
        sub = [r for r in rows if r["strategy"] == strat]
        ok[strat] = (len(sub), sum(
            1 for r in sub
            if r["generations"] - r["W"] * r["depth"] - r["aborts"] == 0))
    return ok


def stats(P, rows):
    rng = random.Random(SEED)
    ar = [s["aborts"] / (s["W"] * s["depth"]) for _, s in P]
    ov = [100 * (s["tokens_total"] / v["tokens_total"] - 1) for v, s in P]
    b0, b1, r2 = ols(ar, ov)
    pairs = list(zip(ar, ov))
    i_lo, i_hi = boot_ci(pairs, lambda pp: ols([p[0] for p in pp],
                                               [p[1] for p in pp])[0], rng)

    zero = [(v, s) for v, s in P if s["aborts"] == 0]
    zov = [100 * (s["tokens_total"] / v["tokens_total"] - 1) for v, s in zero]

    halves = {}
    for nm, sel in (("low", lambda a: a < 0.5), ("high", lambda a: a >= 0.5)):
        h = [(a, o) for a, o in pairs if sel(a)]
        hb0, hb1, hr2 = ols([p[0] for p in h], [p[1] for p in h])
        lo, hi = boot_ci(h, lambda pp: ols([p[0] for p in pp],
                                           [p[1] for p in pp])[1], rng)
        halves[nm] = (len(h), hb1, lo, hi)

    def inflation(sel):
        sub = [(v, s) for v, s in P if sel(s) and s["aborts"] > 0]
        per = [(s["tokens_total"] - v["tokens_total"]) / s["aborts"] for v, s in sub]
        base = [v["tokens_total"] / v["generations"] for v, s in sub]
        lo, hi = boot_ci(list(zip(per, base)),
                         lambda pp: st.mean([p[0] for p in pp])
                         / st.mean([p[1] for p in pp]), rng)
        return len(sub), st.mean(per), st.mean(base), \
            st.mean(per) / st.mean(base), lo, hi

    return {
        "n_pairs": len(P), "intercept": b0, "intercept_ci": (i_lo, i_hi),
        "slope": b1, "r2": r2,
        "zero_abort": (len(zov), st.mean(zov) if zov else float("nan"),
                       st.median(zov) if zov else float("nan")),
        "halves": halves,
        "pooled": inflation(lambda s: True),
        "fanin": inflation(lambda s: s["cells"] == 1),
        "cells": inflation(lambda s: s["W"] == 8 and s["cells"] > 1),
        "identity": identity_holds(rows),
    }


def report(S):
    print(f"  paired SSI/vanilla sessions: {S['n_pairs']}")
    print("\n  ACCOUNTING IDENTITY, checked on the committed data")
    for k, (n, ok) in S["identity"].items():
        tag = "generations = W*depth + aborts" if k == "ssi" else "generations = W*depth"
        print(f"    {k:12s} {ok}/{n}  {tag}")
    print("    => abort_rate is extra generations / baseline generations, and the")
    print("       slope of overhead on abort_rate is the retry price. Nothing else.")

    print("\n  WHAT THE IDENTITY DOES NOT FORCE")
    lo, hi = S["intercept_ci"]
    print(f"    (a) intercept {S['intercept']:+.2f}% 95% CI [{lo:+.2f},{hi:+.2f}]"
          "  -- no fixed SSI cost")
    n, m, md = S["zero_abort"]
    print(f"        {n} zero-abort sessions: mean {m:+.2f}%, median {md:+.2f}%")
    for nm in ("low", "high"):
        n, b1, l, h = S["halves"][nm]
        rng_ = "abort<0.5" if nm == "low" else "abort>=0.5"
        print(f"    (b) {rng_:11s} n={n:3d} slope {b1:6.1f}% 95% CI [{l:.1f},{h:.1f}]")
    print("        -- overlapping: aborts do not compound")
    for nm, lab in (("fanin", "fan-in sweep"), ("cells", "cell-count sweep")):
        n, per, base, ratio, l, h = S[nm]
        print(f"    (c) {lab:17s} n={n:3d} {per:5.1f} tok/abort vs {base:5.1f} tok/gen"
              f"  ratio {ratio:.3f} [{l:.3f},{h:.3f}]")
    n, per, base, ratio, l, h = S["pooled"]
    print(f"    (d) pooled: a retried generation costs {ratio:.3f}x a first-attempt"
          f" one, 95% CI [{l:.3f},{h:.3f}] (n={n})")
    print(f"        this ratio IS the old {S['slope']:.0f}% slope; "
          f"R2={S['r2']:.3f} measures the identity, not a law")
    print(f"    C*: the abort rate at which overhead reaches 15% is "
          f"{15.0 / S['slope']:.2f}, i.e. 0.15/{S['slope'] / 100:.3f}")


def figure(P, S, out):
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (axA, axB) = plt.subplots(1, 2, figsize=(7.0, 2.8), dpi=300)

    # ---- Panel A: dose-response against the SWEPT parameter ----------
    def group(sel, knob):
        g = {}
        for v, s in P:
            if sel(s):
                g.setdefault(knob(s), []).append(
                    100 * (s["tokens_total"] / v["tokens_total"] - 1))
        return {k: (st.mean(q), st.pstdev(q) / max(len(q) ** 0.5, 1))
                for k, q in sorted(g.items())}

    fan = group(lambda s: s["cells"] == 1, lambda s: s["W"])
    cel = group(lambda s: s["W"] == 8 and s["cells"] > 1, lambda s: s["cells"])
    axA.axhspan(0, 15, color="#d8f0d8", zorder=0, label="low-overhead band (<15%)")
    axA.errorbar(list(fan), [v[0] for v in fan.values()],
                 yerr=[v[1] for v in fan.values()], marker="s", ms=5, lw=1.2,
                 color="#1c4587", capsize=2, label="fan-in $W$ (cells=1)")
    axA.errorbar(list(cel), [v[0] for v in cel.values()],
                 yerr=[v[1] for v in cel.values()], marker="D", ms=5, lw=1.2,
                 color="#e69138", capsize=2, label="cell count $C$ ($W$=8)")
    axA.set_xscale("log", base=2)
    ticks = sorted(set(list(fan) + list(cel)))
    axA.set_xticks(ticks)
    axA.set_xticklabels([str(t) for t in ticks])
    axA.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    axA.set_xlabel("swept parameter: fan-in $W$, or cell count $C$", fontsize=7)
    axA.set_ylabel("SSI token overhead vs vanilla (%)", fontsize=7)
    axA.set_title("A  dose-response", fontsize=7.5, loc="left")
    axA.tick_params(labelsize=6)
    axA.legend(fontsize=5.5, loc="upper right", framealpha=0.9)

    # ---- Panel B: the decomposition, in absolute tokens ---------------
    ab = np.array([s["aborts"] for _, s in P], dtype=float)
    ex = np.array([s["tokens_total"] - v["tokens_total"] for v, s in P], dtype=float)
    tok_gen = st.mean([v["tokens_total"] / v["generations"] for v, _ in P])
    _, per_abort, _, ratio, r_lo, r_hi = S["pooled"]
    xs = np.linspace(0, ab.max(), 50)
    axB.scatter(ab, ex, s=9, color="#9fc5e8", zorder=2, label="SSI session")
    axB.plot(xs, tok_gen * xs, color="#666666", ls="--", lw=1.2, zorder=3,
             label=f"null: a retry costs one generation ({tok_gen:.0f} tok)")
    axB.plot(xs, per_abort * xs, color="#cc0000", lw=1.4, zorder=4,
             label=f"measured: {per_abort:.0f} tok/abort "
                   f"= {ratio:.3f}$\\times$ [{r_lo:.2f},{r_hi:.2f}]")
    axB.set_xlabel("aborts in the session (count)", fontsize=7)
    axB.set_ylabel("extra tokens vs paired vanilla run", fontsize=7)
    axB.set_title("B  what an abort actually costs", fontsize=7.5, loc="left")
    axB.tick_params(labelsize=6)
    axB.legend(fontsize=5.3, loc="upper left", framealpha=0.9)

    fig.tight_layout(pad=0.3)
    # Deterministic bytes: the PDF backend stamps a CreationDate by default,
    # so two runs over identical data produce different files and every
    # regeneration dirties the working tree. CreationDate=None omits it.
    fig.savefig(out, metadata={"CreationDate": None})
    print(f"\n  wrote {out}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="python")
    ap.add_argument("--out", default="fig_cost_envelope.pdf")
    ap.add_argument("--stats-only", action="store_true")
    a = ap.parse_args()

    rows = load(a.base)
    P = pair(rows)
    if len(P) != 155:
        print(f"  warning: {len(P)} paired sessions, manuscript reports 155")
    S = stats(P, rows)
    report(S)
    if not a.stats_only:
        figure(P, S, a.out)


if __name__ == "__main__":
    main()
