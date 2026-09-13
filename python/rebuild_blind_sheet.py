#!/usr/bin/env python3
"""rebuild_blind_sheet.py -- a blind sheet for the 43 genuine firings.

python/audit_sheet.csv holds 60 rows: 35 editor, 10 engineer, 15
reviewer.  Section 5.9 withdraws the editor and engineer events as later
rewrites that the corrected predicate does not classify as A1, so 45 of
the 60 blind-coded rows belong to a class the paper no longer claims,
and only 15 of the reviewer's 43 genuine firings were ever coded.
Cohen's kappa is therefore not established on the claim it is cited for.

This emits a sheet restricted to the 43 reviewer firings in
cf_trace_edit.jsonl, in shuffled order under a fixed seed, with the
judge's verdict withheld.

    python3 python/rebuild_blind_sheet.py --stats
    python3 python/rebuild_blind_sheet.py --out python/audit_sheet_43.csv

Then fill in human_diverged (YES / NO) from output_A and output_B alone,
and score with python/audit_agreement.py or your own kappa.

Offline.  No API key.
"""
import argparse, csv, json, os, random


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="python/cf_trace_edit.jsonl")
    ap.add_argument("--out", default="python/audit_sheet_43.csv")
    ap.add_argument("--agent", default="reviewer")
    ap.add_argument("--seed", type=int, default=20260913)
    ap.add_argument("--stats", action="store_true", help="report composition only")
    a = ap.parse_args()

    if not os.path.isfile(a.src):
        raise SystemExit(f"FAIL: {a.src} not found -- run from the repository root")
    with open(a.src) as fh:
        recs = [json.loads(l) for l in fh if l.strip()]

    by_agent = {}
    for r in recs:
        by_agent.setdefault(r.get("agent"), []).append(r)

    old = "python/audit_sheet.csv"
    if os.path.isfile(old):
        with open(old) as fh:
            comp = {}
            for row in csv.DictReader(fh):
                comp[row["agent"]] = comp.get(row["agent"], 0) + 1
        total = sum(comp.values())
        print(f"  existing {old}: {total} rows, " +
              ", ".join(f"{k} {v}" for k, v in sorted(comp.items())))
        withdrawn = sum(v for k, v in comp.items() if k != a.agent)
        print(f"  of which {withdrawn} ({100*withdrawn//total}%) are not "
              f"'{a.agent}' and are withdrawn by Section 5.9")

    sel = [r for r in by_agent.get(a.agent, []) if r.get("diverged") is not None]
    print(f"  {a.src}: " + ", ".join(f"{k} {len(v)}" for k, v in sorted(by_agent.items())))
    print(f"  selected {len(sel)} '{a.agent}' events for re-coding")
    if a.stats:
        return

    random.Random(a.seed).shuffle(sel)
    with open(a.out, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["key", "agent", "decision_cell", "output_A", "output_B", "human_diverged"])
        for r in sel:
            w.writerow([r.get("key", ""), r.get("agent", ""), r.get("decision_cell", ""),
                        r.get("d_stale", ""), r.get("d_fresh", ""), ""])
    print(f"  wrote {a.out} ({len(sel)} rows, seed {a.seed}, judge verdict withheld)")
    print("  fill human_diverged with YES or NO from output_A and output_B alone.")


if __name__ == "__main__":
    main()
