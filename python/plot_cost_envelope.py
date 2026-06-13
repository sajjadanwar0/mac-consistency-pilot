#!/usr/bin/env python3
"""plot_cost_envelope.py -- committed generator for Fig. 2 (cost envelope).

Regenerates fig_cost_envelope.pdf from the committed per-session sweep
rows, using the SAME metric definitions as high_contention_cost.py
(analyze --regress). Closes the artifact-provenance gap without
hardcoding any digitized value.

Metric definitions (mirrored from high_contention_cost.py):
  * Pairing: vanilla and ssi sessions are paired BY scenario_seed
    (within-scenario paired design), per lines 407-414.
  * abort_rate = ssi.aborts / (W * depth)                 (line 416)
  * ssi_rel_overhead = (ssi.tokens_total - van) / van,
        van = paired vanilla.tokens_total                 (lines 407,414)
  * One regression point per paired scenario; plain OLS.   (lines 472-478)

INTEGRITY GATES (abort rather than plot wrong data):
  G1  >= 100 paired (vanilla,ssi) scenarios with W*depth > 0 and van > 0.
  G2  Recomputed OLS fit reproduces the published fit:
      intercept in [-0.04, +0.02], slope in [1.03, 1.18]
      (published: -1% [-3,+1] + 110% [106,115] * abort_rate).
If a gate fails, prints a schema/pairing diagnostic; send it back.

Fig.2 sweep = hc_curve (cell-count sweep, diamonds, cells>1)
            + hc_ceiling (fan-in sweep at one cell, squares, cells==1).

Usage:
  python3 python/plot_cost_envelope.py --model gpt-4o-mini
  python3 python/plot_cost_envelope.py --dir python/hc_curve python/hc_ceiling
"""
import argparse, glob, json, os, sys

def load_rows(path):
    out = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out

def ols(xs, ys):
    n = len(xs); mx = sum(xs)/n; my = sum(ys)/n
    sxx = sum((x-mx)**2 for x in xs)
    sxy = sum((x-mx)*(y-my) for x, y in zip(xs, ys))
    m = sxy/sxx
    return my - m*mx, m

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", nargs="+",
                    default=["python/hc_curve", "python/hc_ceiling"],
                    help="Fig.2 sweep dirs (cell-sweep + fan-in)")
    ap.add_argument("--model", default="gpt-4o-mini")
    ap.add_argument("--out", default="fig_cost_envelope.pdf")
    args = ap.parse_args()

    files = []
    for d in args.dir:
        files.extend(sorted(glob.glob(os.path.join(d, "sessions__*.jsonl"))))
    files = sorted(set(f for f in files if args.model in os.path.basename(f)))
    if not files:
        sys.exit("FAIL: no sessions__%s*.jsonl under %s" % (args.model, args.dir))

    rows = []
    for f in files:
        rows.extend(load_rows(f))
    print("Reading %d rows from: %s" % (len(rows), ", ".join(files)))

    # Index by (W, cells, scenario_seed) -> {strategy: row}, last-write-wins,
    # exactly as high_contention_cost.py line 392. The 5 replicates per
    # (triple, strategy) collapse to the last in file order; the published
    # regression has one point per distinct (W, cells, seed).
    cells_idx = {}
    for r in rows:
        key = (r.get("W"), r.get("cells"), r.get("scenario_seed"))
        cells_idx.setdefault(key, {})[r.get("strategy")] = r

    pts = []  # (abort_rate, ssi_rel_overhead, W, cells)
    skipped = {"no_pair": 0, "bad_denom": 0, "bad_van": 0}
    for (W, C, seed), bystrat in cells_idx.items():
        if "vanilla" not in bystrat:
            skipped["no_pair"] += 1
            continue
        van = bystrat["vanilla"].get("tokens_total", 0)
        if van <= 0:
            skipped["bad_van"] += 1
            continue
        if "ssi" not in bystrat:
            skipped["no_pair"] += 1
            continue
        ssi = bystrat["ssi"]
        depth = ssi.get("depth")
        if not W or not depth or W*depth <= 0:
            skipped["bad_denom"] += 1
            continue
        ar = ssi.get("aborts", 0) / (W * depth)
        d = (ssi.get("tokens_total", 0) - van) / van
        pts.append((ar, d, W, C))

    if len(pts) < 100:
        sys.exit("GATE G1 FAILED: %d paired scenarios (need >=100). "
                 "Skipped: %r. First seed groups: %r"
                 % (len(pts), skipped,
                    {k: list(v.keys()) for k, v in list(by_seed.items())[:5]}))

    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    b, m = ols(xs, ys)
    if not (-0.04 <= b <= 0.02 and 1.03 <= m <= 1.18):
        sys.exit("GATE G2 FAILED: recomputed fit %+.3f + %.3f*abort does not "
                 "reproduce published -0.01 + 1.10*abort (n=%d paired). "
                 "Metric or pairing mismatch; do not plot." % (b, m, len(pts)))

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size": 9})
    fig, ax = plt.subplots(figsize=(5.4, 3.6))
    xstar = (0.15 - b)/m
    ax.axhspan(-0.08, 0.15, color="honeydew", zorder=0,
               label="low-overhead band (<15%)")
    ax.scatter(xs, ys, s=14, color="cornflowerblue", alpha=0.5, zorder=2,
               label="SSI session")
    xf = [0.0, max(xs)*1.05]
    ax.plot(xf, [b + m*x for x in xf], color="firebrick", lw=2.5, zorder=3,
            label="fit: %+.0f%% + %.0f%%\u00b7abort" % (b*100, m*100))
    ax.axvline(xstar, color="purple", ls="--", lw=1.2, zorder=1)
    ax.text(xstar + 0.012, 1.02, "C* abort\u2248%.2f" % xstar, rotation=90,
            color="purple", va="top", ha="left", fontsize=7)
    # Two arms (caption): cells==1 fan-in (squares, by W); cells>1 cell-sweep
    # (diamonds, labelled C).
    cell_groups, fanin_groups = {}, {}
    for a, o, W, C in pts:
        if C is not None and float(C) == 1.0:
            fanin_groups.setdefault(W, []).append((a, o))
        elif C is not None:
            cell_groups.setdefault(C, []).append((a, o))
    for C, vs in cell_groups.items():
        ax_ = sum(v[0] for v in vs)/len(vs); ay_ = sum(v[1] for v in vs)/len(vs)
        ax.scatter([ax_], [ay_], marker="D", s=60, color="navy",
                   edgecolor="white", linewidth=0.6, zorder=5)
        # label above-left so it clears both the diamond and the rising line
        ax.annotate("C=%s" % (int(C) if float(C).is_integer() else C),
                    (ax_, ay_), xytext=(-4, 9), textcoords="offset points",
                    color="navy", fontsize=7.5, ha="right",
                    fontweight="bold", zorder=6)
    for W, vs in fanin_groups.items():
        ax_ = sum(v[0] for v in vs)/len(vs); ay_ = sum(v[1] for v in vs)/len(vs)
        ax.scatter([ax_], [ay_], marker="s", s=55, color="darkorange",
                   edgecolor="white", linewidth=0.6, zorder=5)
    # legend proxies for the two sweep arms
    from matplotlib.lines import Line2D
    arm_handles = [
        Line2D([0],[0], marker="D", color="w", markerfacecolor="navy",
               markersize=8, label="cell-count sweep (C, W=8)"),
        Line2D([0],[0], marker="s", color="w", markerfacecolor="darkorange",
               markersize=8, label="fan-in sweep (cells=1)"),
    ]
    ax.set_xlabel("realized abort rate (aborts per agent-step)")
    ax.set_ylabel("SSI token overhead vs vanilla (%)")
    ax.set_xlim(0, max(xs)*1.08)
    from matplotlib.ticker import FuncFormatter
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: "%d" % round(v*100)))
    h, l = ax.get_legend_handles_labels()
    ax.legend(h + arm_handles, l + [a.get_label() for a in arm_handles],
              loc="upper left", fontsize=7, framealpha=0.9)
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(args.out)
    print("OK: wrote %s" % args.out)
    print("RECONCILIATION (must match the paper):")
    print("  paired scenarios : %d   (paper: 155)" % len(pts))
    print("  fit intercept    : %+.1f%%  (paper: -1%% [-3,+1])" % (b*100))
    print("  fit slope        : %.0f%%  (paper: 110%% [106,115])" % (m*100))
    print("  breakpoint       : %.3f  (paper: ~0.14 [0.13,0.16])" % xstar)
    print("If any line disagrees materially, do NOT commit; send this block.")

if __name__ == "__main__":
    main()
