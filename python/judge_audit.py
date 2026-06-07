#!/usr/bin/env python3
"""
judge_audit.py -- quantify agreement between the deployed-trace LLM judge
(counterfactual_trace.py, judge_text_divergence) and a blind human coder, so
Section 5.10's "a manual check of judge verdicts is consistent with the
categorical separation" becomes a number (Cohen's kappa + percent agreement)
instead of a hand-wave.

It is a TWO-STEP, human-in-the-loop tool and is deliberately dependency-free
(Python 3 stdlib only). It never lets the human see the judge's verdict.

WORKFLOW
  Step 1 -- build a blind coding sheet from the judge's JSONL output(s):

    python judge_audit.py make-sheet cf_trace_edit.jsonl cf_trace_triage.jsonl \
        --n 60 --seed 1 --out audit_sheet.csv

  This selects the LLM-judged (type == "text") firings that the judge actually
  scored (diverged is not None), draws a reproducible stratified sample across
  agents, and writes audit_sheet.csv with columns:
       key, agent, decision_cell, output_A, output_B, human_diverged
  The judge's own verdict is NOT written to the sheet. A second person (ideally
  not the author) fills human_diverged with YES (materially different decision)
  or NO (same decision), judging output_A vs output_B by the same rubric the
  model used.

  Step 2 -- score the filled sheet against the judge's verdicts:

    python judge_audit.py score audit_sheet.csv \
        cf_trace_edit.jsonl cf_trace_triage.jsonl

  This joins on `key`, prints the 2x2 table, percent agreement, Cohen's kappa
  with an approximate 95% CI, and a ready-to-paste sentence for Section 5.10.

NOTES
  * Audit ONLY the judged (free-text) firings: the categorical cells are an
    exact comparator and need no audit.
  * kappa CI is the standard asymptotic (large-sample) approximation; with the
    small n typical here it is wide, and the script says so. Report n alongside.
  * YES/NO parsing is liberal: yes/no, y/n, 1/0, true/false, diverge/same.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path


# --------------------------------------------------------------------------
# Shared: load judge records (type == "text", scored), keyed by `key`
# --------------------------------------------------------------------------
def load_judge_rows(paths):
    rows = {}
    for p in paths:
        p = Path(p)
        if not p.exists():
            sys.exit(f"judge file not found: {p}")
        for line in p.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if r.get("type") != "text":
                continue          # categorical cells are exact-compared, not judged
            if r.get("diverged") is None:
                continue          # unparseable firing; nothing for the judge to agree on
            rows[r["key"]] = r
    return rows


def parse_bool(s):
    if s is None:
        return None
    t = str(s).strip().lower()
    if t in ("yes", "y", "1", "true", "t", "diverge", "diverged", "different"):
        return True
    if t in ("no", "n", "0", "false", "f", "same", "nochange", "no-change"):
        return False
    return None


# --------------------------------------------------------------------------
# Step 1: make a blind coding sheet
# --------------------------------------------------------------------------
def make_sheet(args):
    rows = load_judge_rows(args.judge_files)
    if not rows:
        sys.exit("no judged (type=='text', scored) firings found in the inputs.")

    by_agent = defaultdict(list)
    for key, r in rows.items():
        by_agent[r.get("agent", "?")].append(key)

    rng = random.Random(args.seed)
    for keys in by_agent.values():
        keys.sort()           # determinism before shuffling
        rng.shuffle(keys)

    # Stratified sample: take proportionally from each agent up to --n total,
    # at least 1 per agent where available, capped at availability.
    agents = sorted(by_agent)
    total_avail = sum(len(by_agent[a]) for a in agents)
    n_target = min(args.n, total_avail)
    chosen = []
    if n_target >= len(agents):
        # one guaranteed per agent, then fill the remainder proportionally
        for a in agents:
            chosen.append((a, by_agent[a][0]))
        remaining = n_target - len(agents)
        pool = [(a, k) for a in agents for k in by_agent[a][1:]]
        rng.shuffle(pool)
        chosen.extend(pool[:remaining])
    else:
        # fewer slots than agents: sample agents
        for a in rng.sample(agents, n_target):
            chosen.append((a, by_agent[a][0]))

    chosen.sort(key=lambda ak: (ak[0], ak[1]))
    out = Path(args.out)
    with out.open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["key", "agent", "decision_cell",
                    "output_A", "output_B", "human_diverged"])
        for agent, key in chosen:
            r = rows[key]
            w.writerow([key, agent, r.get("decision_cell", ""),
                        r.get("d_stale", ""), r.get("d_fresh", ""), ""])
    print(f"wrote {out} with {len(chosen)} firings to code "
          f"(agents: {dict(Counter(a for a, _ in chosen))}).")
    print("Have a second coder fill the human_diverged column with YES/NO,")
    print("judging output_A vs output_B WITHOUT seeing the model's verdict, then run:")
    print(f"  python judge_audit.py score {out} " + " ".join(map(str, args.judge_files)))


# --------------------------------------------------------------------------
# Step 2: score the filled sheet vs the judge
# --------------------------------------------------------------------------
def cohen_kappa(a, b, c, d):
    """2x2 counts: a=both YES, b=judge YES/human NO, c=judge NO/human YES,
    d=both NO. Returns (kappa, se, po, pe, n)."""
    n = a + b + c + d
    if n == 0:
        return (float("nan"), float("nan"), float("nan"), float("nan"), 0)
    po = (a + d) / n
    p_judge_yes = (a + b) / n
    p_human_yes = (a + c) / n
    pe = p_judge_yes * p_human_yes + (1 - p_judge_yes) * (1 - p_human_yes)
    if abs(1 - pe) < 1e-12:
        return (float("nan"), float("nan"), po, pe, n)
    kappa = (po - pe) / (1 - pe)
    # standard asymptotic SE (Cohen 1960, large-sample approximation)
    se = math.sqrt(po * (1 - po) / n) / (1 - pe)
    return (kappa, se, po, pe, n)


def score(args):
    judge = load_judge_rows(args.judge_files)
    sheet = Path(args.sheet)
    if not sheet.exists():
        sys.exit(f"sheet not found: {sheet}")

    a = b = c = d = 0          # judge x human contingency
    unlabeled = missing = 0
    rows_used = []
    with sheet.open(encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            key = row.get("key", "").strip()
            hv = parse_bool(row.get("human_diverged"))
            if hv is None:
                unlabeled += 1
                continue
            jr = judge.get(key)
            if jr is None:
                missing += 1
                continue
            jv = bool(jr["diverged"])
            rows_used.append((key, jv, hv))
            if jv and hv:
                a += 1
            elif jv and not hv:
                b += 1
            elif (not jv) and hv:
                c += 1
            else:
                d += 1

    kappa, se, po, pe, n = cohen_kappa(a, b, c, d)
    print("===== LLM-judge vs human audit =====")
    print(f"coded rows used: {n}   unlabeled skipped: {unlabeled}   "
          f"keys not in judge output: {missing}")
    print("contingency (rows=judge, cols=human):")
    print(f"               human YES   human NO")
    print(f"  judge YES      {a:>6}     {b:>6}")
    print(f"  judge NO       {c:>6}     {d:>6}")
    if n == 0:
        print("no usable coded rows; fill human_diverged and re-run.")
        return
    print(f"percent agreement: {100*po:.1f}%  ({a+d}/{n})")
    if math.isnan(kappa):
        print("Cohen's kappa: undefined (one rater used a single category; "
              "report percent agreement and n instead).")
        return
    lo, hi = kappa - 1.96 * se, kappa + 1.96 * se
    print(f"Cohen's kappa: {kappa:.3f}  (approx. 95% CI [{lo:.3f}, {hi:.3f}], n={n})")
    interp = ("slight" if kappa < .2 else "fair" if kappa < .4 else
    "moderate" if kappa < .6 else "substantial" if kappa < .8 else
    "almost perfect")
    print(f"Landis-Koch band: {interp}")
    print()
    print("Paste-ready sentence for Section 5.10:")
    print(f'  "On a blind sample of n={n} judged firings, a second coder agreed '
          f'with the LLM judge on {100*po:.0f}\\% of cases (Cohen\'s '
          f'$\\kappa={kappa:.2f}$, approx. 95\\% CI '
          f'[{lo:.2f}, {hi:.2f}]); the small $n$ keeps the interval wide and we '
          f'report it as corroboration of the categorical separation, not a '
          f'precise reliability estimate."')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    ms = sub.add_parser("make-sheet", help="build a blind human coding sheet")
    ms.add_argument("judge_files", nargs="+", help="cf_trace_*.jsonl from counterfactual_trace.py --judge")
    ms.add_argument("--n", type=int, default=60, help="target sample size")
    ms.add_argument("--seed", type=int, default=1)
    ms.add_argument("--out", default="audit_sheet.csv")
    ms.set_defaults(func=make_sheet)

    sc = sub.add_parser("score", help="score a filled sheet against the judge")
    sc.add_argument("sheet", help="audit_sheet.csv with human_diverged filled")
    sc.add_argument("judge_files", nargs="+", help="the same cf_trace_*.jsonl files")
    sc.set_defaults(func=score)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()