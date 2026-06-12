#!/usr/bin/env python3
"""
audit_agreement.py - Score the blind human audit of the MAST structural
classifier (mast_structural_classifier.py --audit-sample).

WORKFLOW
--------
  1. python audit_agreement.py audit/ --template
       -> writes audit/human_labels.json with empty labels, one entry per
          blind_sheet excerpt, in sheet order.
  2. Read audit/blind_sheet.json excerpts and fill in every "human_label"
     in audit/human_labels.json. Allowed labels (exactly):
          NO_SHARED_STORE   the excerpt shows a conversation / message
                            exchange with no shared-store operation anywhere,
                            including inside embedded code
          CANDIDATE_OPS     you can point at a store operation (file write,
                            memory/state mutation, db/registry op, code-level
                            write or dump)
          UNKNOWN           you cannot tell from the excerpt
     Label from the excerpt alone. DO NOT open answer_key.json first --
     the key's presence in the same directory is a convenience, not an
     invitation; the audit is worthless if the key is consulted.
  3. python audit_agreement.py audit/
       -> raw agreement, Cohen's kappa (3-category) with bootstrap CI,
          per-category cross-tab, every disagreement with the classifier's
          evidence, and the paper-ready clause.

HONESTY NOTES (read before reporting)
-------------------------------------
* The sample is drawn from the non-PARSED pool, which is ~92%
  NO_SHARED_STORE: the marginals are heavily skewed, so kappa is exposed
  to the prevalence paradox (high raw agreement can coexist with modest
  kappa when one category dominates). Report raw agreement AND kappa AND
  the cross-tab; the cross-tab is the defense if kappa looks odd.
* Any case where the human says CANDIDATE_OPS and the classifier said
  NO_SHARED_STORE is a FALSE-IMMUNITY finding: report each such case
  individually in the paper, never averaged into the agreement rate.
* If agreement < ~90%: examine disagreements, fix the classifier, and
  re-audit on a FRESH sample (--audit-sample again). Do not publish a
  count whose own audit failed.
"""
from __future__ import annotations
import argparse
import json
import sys
from collections import Counter
from pathlib import Path

CATS = ("NO_SHARED_STORE", "CANDIDATE_OPS", "UNKNOWN")


def load(p: Path):
    with open(p) as f:
        return json.load(f)


def cohen_kappa(pairs: list[tuple[str, str]]) -> float:
    n = len(pairs)
    po = sum(1 for a, b in pairs if a == b) / n
    ma = Counter(a for a, _ in pairs)
    mb = Counter(b for _, b in pairs)
    pe = sum((ma[c] / n) * (mb[c] / n) for c in CATS)
    if pe >= 1.0 - 1e-12:
        return 1.0 if po >= 1.0 - 1e-12 else 0.0
    return (po - pe) / (1 - pe)


def bootstrap_kappa_ci(pairs, n_boot=10000, alpha=0.05, seed=0):
    import random
    rng = random.Random(seed)
    n = len(pairs)
    vals = []
    for _ in range(n_boot):
        sample = [pairs[rng.randrange(n)] for _ in range(n)]
        vals.append(cohen_kappa(sample))
    vals.sort()
    lo = vals[int(n_boot * alpha / 2)]
    hi = vals[int(n_boot * (1 - alpha / 2)) - 1]
    return lo, hi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("audit_dir", type=Path)
    ap.add_argument("--labels", type=Path, default=None,
                    help="default: <audit_dir>/human_labels.json")
    ap.add_argument("--template", action="store_true",
                    help="generate the empty labels file from blind_sheet.json")
    args = ap.parse_args()
    labels_path = args.labels or (args.audit_dir / "human_labels.json")
    sheet = load(args.audit_dir / "blind_sheet.json")

    if args.template:
        if labels_path.exists():
            print(f"refusing to overwrite existing {labels_path}", file=sys.stderr)
            sys.exit(1)
        labels_path.write_text(json.dumps(
            [{"session": s["session"], "human_label": ""} for s in sheet],
            indent=1))
        print(f"template -> {labels_path} ({len(sheet)} entries); "
              f"fill every human_label, then rerun without --template")
        return

    human = {h["session"]: h.get("human_label", "").strip()
             for h in load(labels_path)}
    key = {k["session"]: k for k in load(args.audit_dir / "answer_key.json")}

    missing = [s["session"] for s in sheet if not human.get(s["session"])]
    bad = [s for s, l in human.items() if l and l not in CATS]
    if missing or bad:
        if missing:
            print(f"FATAL: {len(missing)} unlabeled entries "
                  f"(e.g. {missing[:3]})", file=sys.stderr)
        if bad:
            print(f"FATAL: invalid labels for {bad[:3]} "
                  f"(allowed: {CATS})", file=sys.stderr)
        sys.exit(1)

    pairs, rows = [], []
    for s in sheet:
        sid = s["session"]
        h, c = human[sid], key[sid]["classifier_verdict"]
        pairs.append((h, c))
        rows.append((sid, h, c, key[sid].get("evidence", [])))

    n = len(pairs)
    agree = sum(1 for a, b in pairs if a == b)
    kappa = cohen_kappa(pairs)
    lo, hi = bootstrap_kappa_ci(pairs)

    print(f"n = {n}   raw agreement = {agree}/{n} ({agree / n:.1%})")
    print(f"Cohen's kappa = {kappa:.3f}   95% bootstrap CI [{lo:.3f}, {hi:.3f}]")

    print("\nCross-tab (rows = human, cols = classifier):")
    print(f"  {'':18}" + "".join(f"{c[:12]:>14}" for c in CATS))
    for hcat in CATS:
        line = f"  {hcat:18}"
        for ccat in CATS:
            line += f"{sum(1 for a, b in pairs if a == hcat and b == ccat):>14}"
        print(line)

    dis = [(sid, h, c, ev) for sid, h, c, ev in rows if h != c]
    false_immunity = [(sid, h, c, ev) for sid, h, c, ev in dis
                      if h == "CANDIDATE_OPS" and c == "NO_SHARED_STORE"]
    if dis:
        print(f"\nDisagreements ({len(dis)}):")
        for sid, h, c, ev in dis:
            tag = "  ** FALSE-IMMUNITY **" if (h, c) == ("CANDIDATE_OPS", "NO_SHARED_STORE") else ""
            print(f"  {sid}: human={h} classifier={c}{tag}")
            for e in ev[:2]:
                print(f"      evidence: {e[:110]}")
    if false_immunity:
        print(f"\n** {len(false_immunity)} FALSE-IMMUNITY case(s): report each "
              f"individually in the paper; do not average into agreement. **")

    print("\nPaper-ready clause:")
    print(f'  "A blind human audit of {n} classified traces agreed with the '
          f'classifier on {agree}/{n} ({agree / n:.0%}; Cohen\'s kappa = '
          f'{kappa:.2f}, 95% CI [{lo:.2f}, {hi:.2f}])."')


if __name__ == "__main__":
    main()