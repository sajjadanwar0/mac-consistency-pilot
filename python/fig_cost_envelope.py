#!/usr/bin/env python3
"""fig_cost_envelope.py -- regenerate Figure 2 from committed data.

The manuscript's Figure 2 was previously a loose PDF with no generator
in the tree, so the fitted line could not be checked.  This rebuilds it
from python/hc_curve and python/hc_ceiling.

The abort rate is aborts per AGENT-STEP, i.e. aborts / (W * depth) --
not aborts / generations, which gives a different slope.  Pairing
vanilla against ssi on (source, scenario_seed, W, cells, depth) yields
exactly 155 paired sessions and the fit the manuscript reports:

    overhead = +0.1% + 108% * abort_rate,  C* = 0.14

    python3 python/fig_cost_envelope.py --out fig_cost_envelope.pdf

Needs matplotlib and numpy.  Offline.
"""
import argparse, json, os

SRC = ["hc_curve", "hc_ceiling"]
FILE = "sessions__gpt-4o-mini.jsonl"


def load(base):
    rows = []
    for d in SRC:
        p = os.path.join(base, d, FILE)
        if not os.path.isfile(p):
            raise SystemExit(f"FAIL: {p} not found")
        with open(p) as fh:
            for l in fh:
                if l.strip():
                    r = json.loads(l)
                    r["_src"] = d
                    rows.append(r)
    return rows


def main():
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="python")
    ap.add_argument("--out", default="fig_cost_envelope.pdf")
    a = ap.parse_args()

    rows = load(a.base)
    key = lambda r: (r["_src"], r["scenario_seed"], r["W"], r["cells"], r["depth"])
    van = {key(r): r for r in rows if r["strategy"] == "vanilla"}
    ssi = {key(r): r for r in rows if r["strategy"] == "ssi"}
    P = [(van[k], ssi[k]) for k in ssi if k in van]
    if len(P) != 155:
        print(f"  warning: {len(P)} paired sessions, manuscript reports 155")

    pt = lambda v, s: (s["aborts"] / (s["W"] * s["depth"]),
                       100 * (s["tokens_total"] / v["tokens_total"] - 1))
    X, Y = zip(*[pt(v, s) for v, s in P])
    b, c = np.polyfit(X, Y, 1)

    def means(sel):
        g = {}
        for v, s in P:
            if sel(s):
                g.setdefault((s["W"], s["cells"]), []).append(pt(v, s))
        return {k: (np.mean([p[0] for p in q]), np.mean([p[1] for p in q])) for k, q in g.items()}

    fan = means(lambda s: s["cells"] == 1)
    cel = means(lambda s: s["W"] == 8 and s["cells"] > 1)

    fig, ax = plt.subplots(figsize=(3.5, 2.8), dpi=300)
    ax.axhspan(0, 15, color="#d8f0d8", zorder=0, label="low-overhead band (<15%)")
    ax.scatter(X, Y, s=9, color="#9fc5e8", zorder=2, label="SSI session")
    xs = np.linspace(0, 1, 50)
    ax.plot(xs, c + b * xs, color="#cc0000", lw=1.4, zorder=4,
            label=f"fit: {c:+.0f}% + {b:.0f}%$\\cdot$abort")
    if fan:
        ax.scatter(*zip(*fan.values()), marker="s", s=42, color="#1c4587",
                   zorder=5, label="fan-in sweep (cells=1)")
    if cel:
        ax.scatter(*zip(*cel.values()), marker="D", s=42, color="#e69138",
                   zorder=5, label="cell-count sweep (C, W=8)")
        for (W, C), (x, y) in cel.items():
            ax.annotate(f"C={C}", (x, y), textcoords="offset points",
                        xytext=(4, 5), fontsize=6)
    cstar = (15 - c) / b
    ax.axvline(cstar, color="#8e24aa", ls="--", lw=0.9, zorder=3)
    ax.annotate(f"C* abort$\\approx${cstar:.2f}", (cstar, 118), fontsize=6,
                rotation=90, ha="right", va="top", color="#8e24aa")
    ax.set_xlabel("realized abort rate (aborts per agent-step)", fontsize=7)
    ax.set_ylabel("SSI token overhead vs vanilla (%)", fontsize=7)
    ax.set_xlim(-0.02, 1.0)
    ax.set_ylim(-12, 125)
    ax.tick_params(labelsize=6)
    ax.legend(fontsize=5.3, loc="upper left", framealpha=0.9)
    fig.tight_layout(pad=0.25)
    fig.savefig(a.out)
    print(f"{len(P)} paired sessions; fit = {c:+.1f}% + {b:.0f}% * abort_rate ; C* = {cstar:.2f}")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()
