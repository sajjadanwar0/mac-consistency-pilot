#!/usr/bin/env python3
"""realstore_metrics.py -- price ANY per-call metric of a committed real-store
run: per session, per committed operation, per SOUND committed operation.

WHY (2026-09-19 round 34). The wall-clock study of Section 5.9
(wallclock_cost_study.py) does not run the stores. It wraps the workload's
tools so that a write fails with a FIXED probability -- pessimistic 0.20, SSI
0.05 -- and is retried, independently of contention. Its overheads price an
injected retry at rates we chose, not a discipline. Meanwhile every model call
of the 900-session real-store run (runs/20260913T0150Z, gpt-4o) and of its
Claude replication (pilot_tokens_claude) already carries `wall_clock_ms` and an
end-of-call `timestamp_iso`, written by tokens_capture.py, on the REAL stores,
at n = 100 per cell against the injected study's 30. The measurement was in the
tree the whole time. This tool reads it. No new inference.

OVERRULED (rounds <= 33): reading a discipline's wall-clock cost off the
injected-abort study.

GENERIC. The metric is a parameter -- usd, tokens, wall_s (time inside model
calls), span_s (first call's start to last call's end) -- so one loader and one
set of statistics serve every per-call quantity the run recorded. With
`--metric usd --tex` the per-denominator table is workcost.py's Table 5 byte
for byte, and the round's fix script gates on exactly that.

STATISTICS. Standard library only, seeded, so every figure reproduces:
mean and 95% bootstrap CI per cell; overhead against the unguarded cell as a
ratio of means with 95% and 90% bootstrap CIs; a two-sample permutation test on
the difference of means, Holm-corrected across the six guarded cells of a run;
the minimum detectable effect at alpha 0.05 and power 0.80; and equivalence
against the +-10% margin Section 5.9 pre-declared (the 90% CI of the overhead
lies inside the margin).

THE CONTROL, AND WHAT IT COSTS THE DESIGN. The nine cells of a run were
executed one after another, not interleaved, so a difference between two cells
also carries whatever the provider's latency did between them. plan-execute is
the control: no runtime aborts on it and all three do the same work, so any
"overhead" there is drift, not discipline. Its largest absolute overhead is
reported as the run's NULL BAND, and every other overhead is marked inside or
outside it. An overhead inside the band is not evidence of a cost, however
small its p-value: the control cells themselves differ significantly.

Sessions are NOT paired, deliberately. autogen_pilot.py gives every session of
a workload the same task and never reads its --seed flag, so session k under
one runtime shares nothing with session k under another beyond the workload.
A paired analysis by session index would remove no variance and claim a design
the run does not have.

    python3 python/realstore_metrics.py                      # wall-clock, both runs
    python3 python/realstore_metrics.py --metric usd --tex   # == workcost.py --tex
    python3 python/realstore_metrics.py --tex                # LaTeX body, wall-clock
    python3 python/realstore_metrics.py --write              # write the tracked results
    python3 python/realstore_metrics.py --check              # recompute; exit 1 on any disagreement
    python3 python/realstore_metrics.py --selftest           # known-answer checks

Offline. No API key, no network. Run from the repository root.
"""
import argparse
import json
import math
import os
import random
import re
import sys
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from workcost import RUNTIMES, WORKLOADS, stale_readers  # noqa: E402

SEED = 20260919
RESAMPLES = 5000
MARGIN = 0.10
Z_ALPHA, Z_POWER = 1.959964, 0.841621
METRICS = ["usd", "tokens", "wall_s", "span_s"]
TRACKED = "python/realstore_wallclock.json"
TRACKED_METRIC = "span_s"
RUNS = [
    # label, token cells, trace cells (None: the run's traces are not joined to
    # its token cells in the artifact, so only the per-session price exists)
    ("gpt-4o", "runs/20260913T0150Z/tokens-{wl}-{rt}", "runs/20260913T0150Z/{wl}-{rt}"),
    ("claude-sonnet-4-5", "pilot_tokens_claude", None),
]
LABEL = {"pessimistic": "pessimistic", "snapshot_isolation": "SSI"}


# ---------------------------------------------------------------- loading
def end_of_call(ts):
    """`timestamp_iso` is written when the call RETURNS (see check_timestamps)."""
    return datetime.fromisoformat(ts.replace("Z", "+00:00")).timestamp()


def session_metrics(rows):
    """Every per-session quantity the per-call records support."""
    ends = [end_of_call(r["timestamp_iso"]) for r in rows]
    starts = [e - r["wall_clock_ms"] / 1000.0 for e, r in zip(ends, rows)]
    return {
        "usd": sum(r["total_cost_usd"] for r in rows),
        "tokens": sum(r["total_tokens"] for r in rows),
        "wall_s": sum(r["wall_clock_ms"] for r in rows) / 1000.0,
        "span_s": max(ends) - min(starts),
        "calls": len(rows),
        "t0": min(starts),
        "t1": max(ends),
    }


def load_cell(tokens_dir, traces_dir, wl, rt):
    """Sessions of one cell, in file order: [{metrics..., ops, sound}]."""
    name = re.compile(r"^%s-%s-(\d{4})\.tokens\.jsonl$" % (re.escape(wl), re.escape(rt)))
    tdir = tokens_dir.format(wl=wl, rt=rt)
    if not os.path.isdir(tdir):
        raise SystemExit("FAIL: %s not found -- run from the repository root" % tdir)
    toks = {}
    for f in sorted(os.listdir(tdir)):
        m = name.match(f)
        if m:
            with open(os.path.join(tdir, f)) as fh:
                rows = [json.loads(l) for l in fh if l.strip()]
            if rows:
                toks[m.group(1)] = session_metrics(rows)
    traces = None
    if traces_dir is not None:
        traces, xdir = {}, traces_dir.format(wl=wl, rt=rt)
        for f in sorted(os.listdir(xdir)):
            m = re.search(r"(\d{4})", f)
            if f.endswith(".jsonl") and m:
                with open(os.path.join(xdir, f)) as fh:
                    traces[m.group(1)] = [json.loads(l) for l in fh if l.strip()]
    keys = [k for k in (traces if traces is not None else toks) if k in toks]
    if not keys:
        raise SystemExit("FAIL: no session of %s-%s joins %s" % (wl, rt, tdir))
    out = []
    for k in keys:
        s = dict(toks[k])
        if traces is not None:
            s["ops"] = len(traces[k])
            s["sound"] = len(traces[k]) - len(stale_readers(traces[k]))
        out.append(s)
    return out


def check_timestamps(tokens_dir):
    """Is `timestamp_iso` the END of a call?  Under that reading the gap between
    one call's end and the next call's start is small and non-negative; under
    the other reading it is not.  Returns the share of non-negative gaps under
    (end, start)."""
    ok = {"end": 0, "start": 0}
    n = 0
    for wl in WORKLOADS:
        for rt in RUNTIMES:
            tdir = tokens_dir.format(wl=wl, rt=rt)
            for f in sorted(os.listdir(tdir)):
                if not (f.startswith("%s-%s-" % (wl, rt)) and f.endswith(".tokens.jsonl")):
                    continue
                with open(os.path.join(tdir, f)) as fh:
                    rows = [json.loads(l) for l in fh if l.strip()]
                for a, b in zip(rows, rows[1:]):
                    ta, tb = end_of_call(a["timestamp_iso"]), end_of_call(b["timestamp_iso"])
                    n += 1
                    if (tb - b["wall_clock_ms"] / 1000.0) - ta >= -0.05:
                        ok["end"] += 1
                    if tb - (ta + a["wall_clock_ms"] / 1000.0) >= -0.05:
                        ok["start"] += 1
    return ok["end"] / max(n, 1), ok["start"] / max(n, 1)


def stamp(t):
    return datetime.fromtimestamp(t, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ------------------------------------------------------------- statistics
def mean(xs):
    return sum(xs) / len(xs)


def var(xs):
    m = mean(xs)
    return sum((x - m) ** 2 for x in xs) / (len(xs) - 1)


def quantile(sorted_xs, q):
    if len(sorted_xs) == 1:
        return sorted_xs[0]
    pos = q * (len(sorted_xs) - 1)
    lo = int(math.floor(pos))
    hi = min(lo + 1, len(sorted_xs) - 1)
    return sorted_xs[lo] + (sorted_xs[hi] - sorted_xs[lo]) * (pos - lo)


def resample(n, rng):
    return [int(rng.random() * n) for _ in range(n)]


def boot(stat, groups, rng, levels=(0.95,)):
    """Bootstrap `stat(*resampled groups)`; groups resampled independently."""
    draws = []
    for _ in range(RESAMPLES):
        draws.append(stat(*[[g[i] for i in resample(len(g), rng)] for g in groups]))
    draws.sort()
    return [(quantile(draws, (1 - lv) / 2), quantile(draws, 1 - (1 - lv) / 2)) for lv in levels]


def perm_test(a, b, rng):
    """Two-sided permutation test on the difference of means."""
    obs = abs(mean(a) - mean(b))
    pool, na = list(a) + list(b), len(a)
    hits = 0
    for _ in range(RESAMPLES):
        # Fisher-Yates on rng.random() alone: that stream is stable across
        # Python versions, random.shuffle's internals are not promised to be
        for k in range(len(pool) - 1, 0, -1):
            j = int(rng.random() * (k + 1))
            pool[k], pool[j] = pool[j], pool[k]
        if abs(mean(pool[:na]) - mean(pool[na:])) >= obs - 1e-12:
            hits += 1
    return (hits + 1) / (RESAMPLES + 1)


def holm(pvals):
    order = sorted(range(len(pvals)), key=lambda i: pvals[i])
    adj, running = [0.0] * len(pvals), 0.0
    for rank, i in enumerate(order):
        running = max(running, min(1.0, (len(pvals) - rank) * pvals[i]))
        adj[i] = running
    return adj


def mde_fraction(guarded, base):
    """Minimum detectable difference of means, as a fraction of the base mean."""
    return (Z_ALPHA + Z_POWER) * math.sqrt(var(guarded) / len(guarded) + var(base) / len(base)) / mean(base)


def price(cell, metric, denom):
    """Ratio of totals, as workcost.py prices: sum(metric) / sum(denominator)."""
    top = sum(s[metric] for s in cell)
    return top / (len(cell) if denom == "session" else sum(s[denom] for s in cell))


def overhead(guarded, base, metric, denom):
    return price(guarded, metric, denom) / price(base, metric, denom) - 1


# ---------------------------------------------------------------- analysis
def analyse(metric):
    rng = random.Random(SEED)
    out = {"metric": metric, "seed": SEED, "resamples": RESAMPLES, "margin": MARGIN, "runs": {}}
    for label, tokens_dir, traces_dir in RUNS:
        cells = {(wl, rt): load_cell(tokens_dir, traces_dir, wl, rt) for wl in WORKLOADS for rt in RUNTIMES}
        run = {"cells": {}, "overheads": {}}
        for (wl, rt), cell in cells.items():
            xs = [s[metric] for s in cell]
            (lo, hi), = boot(lambda g: mean(g), [xs], rng)
            run["cells"]["%s-%s" % (wl, rt)] = {
                "n": len(xs), "mean": round(mean(xs), 4), "ci95": [round(lo, 4), round(hi, 4)],
                "median": round(quantile(sorted(xs), 0.5), 4),
                "calls_per_session": round(mean([s["calls"] for s in cell]), 3),
                "window_utc": [stamp(min(s["t0"] for s in cell)), stamp(max(s["t1"] for s in cell))],
            }
        names, pvals = [], []
        for wl in WORKLOADS:
            base = cells[(wl, "vanilla")]
            for rt in RUNTIMES:
                if rt == "vanilla":
                    continue
                g = cells[(wl, rt)]
                gx, bx = [s[metric] for s in g], [s[metric] for s in base]
                ci95, ci90 = boot(lambda a, b: mean(a) / mean(b) - 1, [gx, bx], rng, levels=(0.95, 0.90))
                p = perm_test(gx, bx, rng)
                row = {
                    "per_session": round(overhead(g, base, metric, "session"), 4),
                    "per_session_median": round(quantile(sorted(gx), 0.5) / quantile(sorted(bx), 0.5) - 1, 4),
                    "ci95": [round(ci95[0], 4), round(ci95[1], 4)],
                    "ci90": [round(ci90[0], 4), round(ci90[1], 4)],
                    "p_perm": round(p, 4),
                    "mde": round(mde_fraction(gx, bx), 4),
                    "equivalent_within_margin": bool(-MARGIN < ci90[0] and ci90[1] < MARGIN),
                }
                if traces_dir is not None:
                    for denom, key in (("ops", "per_commit"), ("sound", "per_sound_commit")):
                        row[key] = round(overhead(g, base, metric, denom), 4)
                        (lo, hi), = boot(lambda a, b, d=denom: overhead(a, b, metric, d), [g, base], rng)
                        row[key + "_ci95"] = [round(lo, 4), round(hi, 4)]
                name = "%s-%s" % (wl, rt)
                run["overheads"][name] = row
                names.append(name)
                pvals.append(p)
        for name, adj in zip(names, holm(pvals)):
            run["overheads"][name]["p_holm"] = round(adj, 4)
        control = [run["overheads"]["plan-execute-%s" % rt] for rt in RUNTIMES if rt != "vanilla"]
        band = max(abs(c["per_session"]) for c in control)
        band_median = max(abs(c["per_session_median"]) for c in control)
        run["null_band"] = {
            "value": round(band, 4),
            "median": round(band_median, 4),
            "basis": "plan-execute: no runtime aborts and all three do the same work, so its overheads are drift between cells",
        }
        # outside only when the mean AND the median agree: a mean dragged by a
        # few stalled calls (claude edit-review SSI: mean +51%, median -0.6%) is
        # not a cost of the discipline
        for name, row in run["overheads"].items():
            row["outside_null_band"] = bool(abs(row["per_session"]) > band and abs(row["per_session_median"]) > band_median)
        out["runs"][label] = run
    return out


# ------------------------------------------------------------------ output
def pc(x):
    return "%+.1f%%" % (100 * x)


def print_text(res):
    unit = {"usd": "USD", "tokens": "tokens", "wall_s": "s", "span_s": "s"}[res["metric"]]
    for label, run in res["runs"].items():
        print("\nRun %s -- metric %s (%s), per session\n" % (label, res["metric"], unit))
        print("  %-36s %5s %10s %22s %10s %8s  %s" % ("cell", "n", "mean", "95% CI", "median", "calls", "ran (UTC)"))
        for name, c in run["cells"].items():
            print("  %-36s %5d %10.3f %22s %10.3f %8.2f  %s .. %s" % (
                name, c["n"], c["mean"], "[%.3f, %.3f]" % tuple(c["ci95"]), c["median"], c["calls_per_session"],
                c["window_utc"][0][5:16], c["window_utc"][1][11:16]))
        print("\n  null band: mean %s, median %s  (%s)" % (
            pc(run["null_band"]["value"]).replace("+", "+-"), pc(run["null_band"]["median"]).replace("+", "+-"), run["null_band"]["basis"]))
        print("\n  %-30s %9s %9s %20s %8s %7s %6s %8s %11s %12s" % (
            "overhead vs vanilla", "mean", "median", "95% CI (mean)", "p Holm", "MDE", "equiv", "band", "per commit", "per sound"))
        for name, o in run["overheads"].items():
            print("  %-30s %9s %9s %20s %8.4f %7s %6s %8s %11s %12s" % (
                name, pc(o["per_session"]), pc(o["per_session_median"]), "[%s, %s]" % (pc(o["ci95"][0]), pc(o["ci95"][1])),
                o["p_holm"], pc(o["mde"]).lstrip("+"), "yes" if o["equivalent_within_margin"] else "no",
                "OUTSIDE" if o["outside_null_band"] else "inside",
                pc(o["per_commit"]) if "per_commit" in o else "--",
                pc(o["per_sound_commit"]) if "per_sound_commit" in o else "--"))


def print_tex(res):
    if res["metric"] == "usd":
        # workcost.py's Table 5 body, same arithmetic, same format, byte for byte
        label, tokens_dir, traces_dir = RUNS[0]
        cells = {(wl, rt): load_cell(tokens_dir, traces_dir, wl, rt) for wl in WORKLOADS for rt in RUNTIMES}
        for wl in WORKLOADS:
            n0, o0, s0 = len(cells[(wl, "vanilla")]), sum(s["ops"] for s in cells[(wl, "vanilla")]), sum(s["sound"] for s in cells[(wl, "vanilla")])
            u0 = sum(s["usd"] for s in cells[(wl, "vanilla")])
            base_sess, base_op, base_sound = 1000 * u0 / n0, 1000 * u0 / o0, 1000 * u0 / s0
            for rt in RUNTIMES:
                if rt == "vanilla":
                    continue
                c = cells[(wl, rt)]
                n, o, s, u = len(c), sum(x["ops"] for x in c), sum(x["sound"] for x in c), sum(x["usd"] for x in c)
                x, y, z = (1000 * u / n) / base_sess - 1, (1000 * u / o) / base_op - 1, (1000 * u / s) / base_sound - 1
                print(f"{wl:12s} & {LABEL[rt]:11s} & ${100*x:+.1f}\\%$ & "
                      f"${100*y:+.1f}\\%$ & ${100*z:+.1f}\\%$ \\\\")
        return
    for label, run in res["runs"].items():
        print("%% run %s, metric %s" % (label, res["metric"]))
        for name, o in run["overheads"].items():
            wl = [w for w in WORKLOADS if name.startswith(w + "-")][0]
            rt = name[len(wl) + 1:]
            tail = " & $%+.1f\\%%$ & $%+.1f\\%%$" % (100 * o["per_commit"], 100 * o["per_sound_commit"]) if "per_commit" in o else " & --- & ---"
            print("%-12s & %-11s & $%+.1f\\%%$ & $[%+.1f, %+.1f]$ & $%+.1f\\%%$ & $%.3f$ & %s%s \\\\" % (
                wl, LABEL[rt], 100 * o["per_session"], 100 * o["ci95"][0], 100 * o["ci95"][1],
                100 * o["per_session_median"], o["p_holm"], "outside" if o["outside_null_band"] else "inside", tail))


def diff(a, b, path=""):
    if isinstance(a, dict) and isinstance(b, dict):
        out = []
        for k in sorted(set(a) | set(b)):
            out += diff(a.get(k), b.get(k), "%s/%s" % (path, k)) if k in a and k in b else ["%s/%s: present on one side only" % (path, k)]
        return out
    if isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
        out = []
        for i, (x, y) in enumerate(zip(a, b)):
            out += diff(x, y, "%s[%d]" % (path, i))
        return out
    return [] if a == b else ["%s: tracked %r, recomputed %r" % (path, a, b)]


# ---------------------------------------------------------------- selftest
def selftest():
    fails = []

    def expect(name, got, want):
        if got != want and not (isinstance(want, float) and abs(got - want) < 1e-9):
            fails.append("%s: got %r, want %r" % (name, got, want))

    rows = [
        {"total_cost_usd": 1.0, "total_tokens": 10, "wall_clock_ms": 2000, "timestamp_iso": "2026-01-01T00:00:10.000Z"},
        {"total_cost_usd": 2.0, "total_tokens": 20, "wall_clock_ms": 1000, "timestamp_iso": "2026-01-01T00:00:13.000Z"},
    ]
    m = session_metrics(rows)
    expect("span is first start to last end", m["span_s"], 5.0)
    expect("wall is time inside calls", m["wall_s"], 3.0)
    expect("usd sums", m["usd"], 3.0)
    rng = random.Random(1)
    expect("permutation test separates disjoint groups", perm_test([0.0] * 50, [1.0] * 50, rng) < 0.001, True)
    expect("permutation test on identical groups", perm_test([1.0, 2.0, 3.0] * 10, [1.0, 2.0, 3.0] * 10, rng) > 0.5, True)
    (lo, hi), = boot(lambda g: mean(g), [[4.0] * 20], rng)
    expect("bootstrap CI of a constant", (lo, hi), (4.0, 4.0))
    expect("holm", [round(x, 6) for x in holm([0.01, 0.04, 0.03])], [0.03, 0.06, 0.06])
    g, b = [{"span_s": 2.0, "ops": 1, "sound": 1}] * 4, [{"span_s": 1.0, "ops": 2, "sound": 1}] * 4
    expect("overhead sign, per session", overhead(g, b, "span_s", "session"), 1.0)
    expect("overhead per commit divides by operations", overhead(g, b, "span_s", "ops"), 3.0)
    expect("mde closed form", round(mde_fraction([1.0, 3.0] * 8, [1.0, 3.0] * 8), 6),
           round((Z_ALPHA + Z_POWER) * math.sqrt(2 * (16 / 15.0) / 16) / 2.0, 6))
    h = [
        {"agent": "a", "read_set": [], "write_set": ["c"], "read_time": 0, "write_time": 1, "read_values": {}, "write_values": {"c": "v1"}},
        {"agent": "b", "read_set": ["c"], "write_set": ["d"], "read_time": 0, "write_time": 2, "read_values": {"c": None}, "write_values": {"d": "x"}},
    ]
    expect("the stale reader is not sound work", len(h) - len(stale_readers(h)), 1)
    for f in fails:
        print("SELFTEST FAIL  " + f)
    print("selftest: %d checks, %d failed" % (11, len(fails)))
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--metric", choices=METRICS, default=TRACKED_METRIC)
    ap.add_argument("--tex", action="store_true")
    ap.add_argument("--write", action="store_true", help="write %s" % TRACKED)
    ap.add_argument("--check", action="store_true", help="recompute and compare with %s" % TRACKED)
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.tex and a.metric == "usd":
        print_tex({"metric": "usd"})
        return 0
    end_ok, start_ok = check_timestamps(RUNS[0][1])
    if end_ok < 0.99:
        raise SystemExit("FAIL: timestamp_iso does not behave as an end-of-call stamp (%.3f of gaps fit; %.3f under the start reading)" % (end_ok, start_ok))
    res = analyse(TRACKED_METRIC if (a.write or a.check) else a.metric)
    res["timestamp_reading"] = {"end_of_call_fit": round(end_ok, 4), "start_of_call_fit": round(start_ok, 4)}
    if a.write:
        with open(TRACKED, "w") as fh:
            json.dump(res, fh, indent=1, sort_keys=True)
            fh.write("\n")
        print("wrote %s" % TRACKED)
        return 0
    if a.check:
        with open(TRACKED) as fh:
            tracked = json.load(fh)
        bad = diff(tracked, res)
        for line in bad[:12]:
            print("DISAGREES  " + line)
        print("check: %s against the committed cells -- %s" % (TRACKED, "%d disagreement(s)" % len(bad) if bad else "identical"))
        return 1 if bad else 0
    print_tex(res) if a.tex else print_text(res)
    return 0


if __name__ == "__main__":
    sys.exit(main())
