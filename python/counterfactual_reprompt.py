#!/usr/bin/env python3
"""
counterfactual_reprompt.py

PURPOSE
-------
The A1 detector fires on a *string mismatch*: a read observed value v_stale on
cell c, and a later committed write put v_fresh != v_stale on c. A reviewer's
central objection is that this string mismatch may have ZERO correlation with
the agent's actual behaviour: maybe the agent's decision would have been the
same regardless. This script MEASURES that correlation directly.

It estimates the OPERATIONAL DISAGREEMENT PROBABILITY:

    p_op = P( agent's decision changes | the shared value changes v_stale->v_fresh )

This is exactly the quantity the paper's probabilistic refinement leaves as an
uninterpreted axiom (disagreement_probability). p_op turns the A1 rate from a
"string artifact of unknown meaning" into a measured operational quantity:
    operationally-material A1 rate  ~=  (string A1 rate) * p_op.

DESIGN (controlled, causal)
---------------------------
For each trial we hold EVERYTHING fixed except the value of the shared cell,
and run the read-generate-write step twice: once with v_stale, once with
v_fresh. The agent must emit a STRUCTURED decision (JSON). Divergence = the
decisions differ. Because only the injected value changes, any divergence is
caused by the value -> this is a clean causal estimate, not a correlation.

Two task families mirror the paper's workloads:
  * triage:      shared cell = ticket severity; decision = priority label
  * edit-review: shared cell = section status;  decision = approve/revise

We report k/N with an EXACT Clopper-Pearson binomial CI (no asymptotics, so no
concentration inequality is assumed -- this is the honest replacement for the
Hoeffding axiom flagged in the paper).

USAGE
-----
  pip install openai scipy
  export OPENAI_API_KEY=sk-...
  python counterfactual_reprompt.py --task triage      --n 200 --out cf_triage.jsonl
  python counterfactual_reprompt.py --task edit_review  --n 200 --out cf_edit.jsonl
  # distributional variant (temperature > 0, majority vote over samples):
  python counterfactual_reprompt.py --task triage --n 200 --temperature 0.7 --samples 5

Cost: ~2*N small calls. At gpt-4o list price, N=200 triage ~ a few US dollars.
Resumable: results are appended to --out as JSONL; re-running with the same
--out and --seed skips trials already present.
"""
from __future__ import annotations
import argparse
import json
import random
import sys
import time
from collections import Counter
from pathlib import Path
import re


try:
    from scipy.stats import binomtest
except Exception:
    print("pip install scipy", file=sys.stderr); raise



TASKS = {
    "triage": {
        "system": (
            "You are an incident triage agent. Read the ticket and assign a "
            "priority. Respond with ONLY a JSON object: "
            '{"priority": one of ["P0","P1","P2","P3"]}. No prose.'
        ),
        "values": ["informational", "minor", "moderate", "major", "critical"],
        "user_template": (
            "Ticket #{tid}\n"
            "Service: checkout-api\n"
            "Reported severity: {value}\n"
            "Symptom: elevated error rate on POST /checkout for ~12 min, "
            "now recovering.\n"
            "Assign the priority based on the reported severity."
        ),
        "decision_key": "priority",
    },
    "edit_review": {
        "system": (
            "You are a document reviewer. Read the section status and decide "
            "whether to approve it for publish or send it back. Respond with "
            'ONLY a JSON object: {"decision": one of ["approve","revise"]}. '
            "No prose."
        ),
        "values": ["draft", "in-review", "changes-requested", "ready", "approved-by-author"],
        "user_template": (
            "Section: 'Methods' (doc {tid})\n"
            "Current status: {value}\n"
            "The section reads coherently and has no open comments.\n"
            "Decide whether to approve for publish or send back for revision."
        ),
        "decision_key": "decision",
    },
}


def build_messages(task: dict, tid: int, value: str) -> list[dict]:
    return [
        {"role": "system", "content": task["system"]},
        {"role": "user", "content": task["user_template"].format(tid=tid, value=value)},
    ]


def parse_decision(text: str, key: str) -> str | None:
    text = text.strip()
    try:
        obj = json.loads(text)
        if isinstance(obj, dict) and key in obj:
            return str(obj[key]).strip().lower()
    except Exception:
        pass
    m = re.search(r'"%s"\s*:\s*"?([A-Za-z0-9_\-]+)"?' % re.escape(key), text)
    return m.group(1).strip().lower() if m else None


def one_decision(client, model, task, tid, value, temperature, samples) -> str | None:
    """Return the (majority) decision for a single value, or None if unparseable."""
    msgs = build_messages(task, tid, value)
    votes = []
    n = max(1, samples) if temperature > 0 else 1
    for _ in range(n):
        for attempt in range(4):
            try:
                resp = client.chat.completions.create(
                    model=model, messages=msgs, temperature=temperature, max_tokens=40,
                )
                d = parse_decision(resp.choices[0].message.content or "", task["decision_key"])
                if d is not None:
                    votes.append(d)
                break
            except Exception as e:
                time.sleep(1.5 * (attempt + 1))
                if attempt == 3:
                    print(f"  api error (skipping sample): {e}", file=sys.stderr)
    if not votes:
        return None
    return Counter(votes).most_common(1)[0][0]


def clopper_pearson(k: int, n: int, alpha: float = 0.05) -> tuple[float, float]:
    """Exact binomial CI via scipy.binomtest (Clopper-Pearson)."""
    ci = binomtest(k, n).proportion_ci(confidence_level=1 - alpha, method="exact")
    return (ci.low, ci.high)


def load_done(path: Path) -> set[int]:
    done = set()
    if path.exists():
        for line in path.read_text().splitlines():
            try:
                done.add(json.loads(line)["trial"])
            except Exception:
                pass
    return done


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", choices=list(TASKS), required=True)
    ap.add_argument("--n", type=int, default=200, help="number of counterfactual pairs")
    ap.add_argument("--model", default="gpt-4o-2024-08-06")
    ap.add_argument("--temperature", type=float, default=0.0)
    ap.add_argument("--samples", type=int, default=1, help="samples per value when temp>0")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    task = TASKS[args.task]
    try:
        from openai import OpenAI
    except Exception:
        print("pip install openai", file=sys.stderr); raise
    client = OpenAI()
    rng = random.Random(args.seed)
    out = args.out or Path(f"cf_{args.task}.jsonl")
    done = load_done(out)
    fh = out.open("a")

    diverged = 0
    counted = 0
    unparsed = 0
    for trial in range(args.n):
        if trial in done:
            continue
        v_stale, v_fresh = rng.sample(task["values"], 2)
        d_stale = one_decision(client, args.model, task, trial, v_stale,
                               args.temperature, args.samples)
        d_fresh = one_decision(client, args.model, task, trial, v_fresh,
                               args.temperature, args.samples)
        if d_stale is None or d_fresh is None:
            unparsed += 1
            rec = {"trial": trial, "v_stale": v_stale, "v_fresh": v_fresh,
                   "d_stale": d_stale, "d_fresh": d_fresh, "diverged": None}
        else:
            div = (d_stale != d_fresh)
            diverged += int(div)
            counted += 1
            rec = {"trial": trial, "v_stale": v_stale, "v_fresh": v_fresh,
                   "d_stale": d_stale, "d_fresh": d_fresh, "diverged": div}
        fh.write(json.dumps(rec) + "\n"); fh.flush()
    fh.close()

    diverged = counted = unparsed = 0
    for line in out.read_text().splitlines():
        r = json.loads(line)
        if r["diverged"] is None:
            unparsed += 1
        else:
            counted += 1
            diverged += int(r["diverged"])

    if counted == 0:
        print("no parseable trials; check API key / model", file=sys.stderr)
        return
    lo, hi = clopper_pearson(diverged, counted)
    print("\n===== counterfactual disagreement (operational A1 anchor) =====")
    print(f"task                : {args.task}")
    print(f"model               : {args.model}  (temp={args.temperature}, samples={args.samples})")
    print(f"counterfactual pairs: {counted} parseable ({unparsed} unparseable, excluded)")
    print(f"decision changed    : {diverged}")
    print(f"p_op (operational disagreement | flagged value mismatch)")
    print(f"                    = {diverged}/{counted} = {100.0*diverged/counted:.1f}%")
    print(f"95% Clopper-Pearson CI: [{100*lo:.1f}%, {100*hi:.1f}%]   (exact, no asymptotics)")
    print("\nInterpretation: the string-mismatch A1 rate overstates the")
    print("operationally-material rate by the factor (1 - p_op). Report")
    print("operationally-material A1 ~= string-A1 * p_op, with this CI.")


if __name__ == "__main__":
    main()