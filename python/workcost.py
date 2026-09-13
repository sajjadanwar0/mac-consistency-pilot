#!/usr/bin/env python3
"""workcost.py -- price prevention per unit of SOUND delivered work.

Findings 1-4 of Section 5.6 divide cost by the session.  The three
runtimes do not complete the same work in a session: Table 4 shows
pessimistic locking reaching 0% A1 by dropping the reviewer's operation
in 99 of 100 edit-review sessions, and snapshot isolation aborts
commits.  A per-session denominator therefore credits a discipline for
work it declined to do.

This script re-prices run 20260913T0150Z against three denominators:

    per session              what Section 5.6 reports
    per committed operation  over-penalizes the guarded runtimes, since
                             the unguarded baseline is credited with
                             anomalous output
    per SOUND committed op   a committed operation that is not the stale
                             reader i of any Definition-1 witness

The third is the fair price.  Output is Table 5 (Finding 6).

    python3 python/workcost.py                 # from the repo root
    python3 python/workcost.py --tex           # LaTeX tabular body
    python3 python/workcost.py --run RUNID

Offline.  No API key, no network.
"""
import argparse, json, os, re, sys

WORKLOADS = ["edit-review", "plan-execute", "triage"]
RUNTIMES = ["vanilla", "pessimistic", "snapshot_isolation"]


def agent(r):
    a = r.get("agent")
    return a if a is not None else r.get("agent_id")


def stale_readers(h):
    """Indices that are the reader i of some Definition-1 witness.

    Anomalies.tla lines 6-13, transcribed:
      \\E i,j : i # j /\\ h[i].agent # h[j].agent
                /\\ \\E c \\in h[i].read_set \\cap h[j].write_set :
                     h[i].read_time  < h[j].write_time
                  /\\ h[j].write_time < h[i].write_time
                  /\\ h[i].read_values[c] # h[j].write_values[c]
    """
    bad, n = set(), len(h)
    for i in range(n):
        for j in range(n):
            if i == j or agent(h[i]) == agent(h[j]):
                continue
            for c in set(h[i].get("read_set") or []) & set(h[j].get("write_set") or []):
                if h[i]["read_time"] < h[j]["write_time"] < h[i]["write_time"] \
                   and (h[i].get("read_values") or {}).get(c) != (h[j].get("write_values") or {}).get(c):
                    bad.add(i)
    return bad


def sid(name):
    m = re.search(r"(\d{4})", name)
    return m.group(1) if m else None


def cell(run, wl, rt):
    """Return (n_sessions, committed_ops, sound_ops, usd)."""
    td = os.path.join(run, f"{wl}-{rt}")
    kd = os.path.join(run, f"tokens-{wl}-{rt}")
    traces, toks = {}, {}
    for f in sorted(os.listdir(td)):
        if f.endswith(".jsonl"):
            with open(os.path.join(td, f)) as fh:
                traces[sid(f)] = [json.loads(l) for l in fh if l.strip()]
    for f in sorted(os.listdir(kd)):
        if f.endswith(".jsonl"):
            with open(os.path.join(kd, f)) as fh:
                toks[sid(f)] = sum(json.loads(l)["total_cost_usd"] for l in fh if l.strip())
    keys = [k for k in traces if k in toks]
    if not keys:
        raise SystemExit(f"FAIL: no session index joins {td} to {kd}")
    ops = sum(len(traces[k]) for k in keys)
    sound = sum(len(traces[k]) - len(stale_readers(traces[k])) for k in keys)
    usd = sum(toks[k] for k in keys)
    return len(keys), ops, sound, usd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", default="runs/20260913T0150Z")
    ap.add_argument("--tex", action="store_true", help="emit the LaTeX tabular body")
    a = ap.parse_args()
    if not os.path.isdir(a.run):
        raise SystemExit(f"FAIL: {a.run} not found -- run from the repository root")

    data, rows = {}, []
    for wl in WORKLOADS:
        for rt in RUNTIMES:
            data[(wl, rt)] = cell(a.run, wl, rt)

    if not a.tex:
        print(f"Run {a.run}\n")
        print(f"  {'cell':36s}{'$/sess (m)':>12s}{'ops':>7s}{'sound':>7s}"
              f"{'$/op (m)':>11s}{'$/sound (m)':>13s}")
    for wl in WORKLOADS:
        n0, o0, s0, u0 = data[(wl, "vanilla")]
        base_sess, base_op, base_sound = 1000 * u0 / n0, 1000 * u0 / o0, 1000 * u0 / s0
        for rt in RUNTIMES:
            n, o, s, u = data[(wl, rt)]
            ps, po, pd = 1000 * u / n, 1000 * u / o, 1000 * u / s
            if not a.tex:
                print(f"  {wl + '-' + rt:36s}{ps:12.2f}{o:7d}{s:7d}{po:11.3f}{pd:13.3f}")
            if rt != "vanilla":
                rows.append((wl, rt, ps / base_sess - 1, po / base_op - 1, pd / base_sound - 1))
        if not a.tex:
            print()

    label = {"pessimistic": "pessimistic", "snapshot_isolation": "SSI"}
    if a.tex:
        for wl, rt, x, y, z in rows:
            print(f"{wl:12s} & {label[rt]:11s} & ${100*x:+.1f}\\%$ & "
                  f"${100*y:+.1f}\\%$ & ${100*z:+.1f}\\%$ \\\\")
    else:
        print(f"  {'overhead vs vanilla':36s}{'per session':>14s}{'per commit':>13s}{'per sound commit':>19s}")
        for wl, rt, x, y, z in rows:
            print(f"  {wl + '-' + label[rt]:36s}{100*x:13.1f}%{100*y:12.1f}%{100*z:18.1f}%")
        print("\n  Counts feed the manuscript's Table 5 caption; --tex emits the tabular body.")


if __name__ == "__main__":
    main()
