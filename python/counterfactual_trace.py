#!/usr/bin/env python3
"""
counterfactual_trace.py

TRACE-GROUNDED version of counterfactual_reprompt.py.

Instead of synthetic value pairs, this pulls the (v_stale, v_fresh) pairs from
ACTUAL A1 firings in your recorded pilot traces, and re-prompts the deciding
agent using its REAL autogen_pilot.py system prompt. It answers the exact
reviewer question: "of the mismatches your detector flagged in the deployed
workload, what fraction actually change the agent's decision?"

p_op = P( agent's STEP-2 write changes | detector-flagged stale read )

WHY THE PRIMARY NUMBER IS THE TRIAGER'S PRIORITY
------------------------------------------------
The only agent whose decision is a CATEGORICAL label is the triager
(priority in {P0,P1,P2}), read off the `ticket` cell. Categorical -> exact,
objective decision-flip comparison. The editor/reviewer/engineer emit free
text (doc/review/resolution); divergence there is judged by the model under a
strict rubric (--judge) and is reported separately as a softer, secondary
signal. Lead with the triager number; it is the one with no comparator
subjectivity.

INPUT
-----
A directory (or several) of pilot op-record JSONL traces, same schema as
analyze_production.py: each line an event with fields
  agent_id, read_set, read_values{cell:val}, read_time,
  write_set, write_values{cell:val}, write_time
A1 firing on cell c for a reader at time rt with value rv: there exists a later
write (wt>rt) of c with value wv != rv. (v_stale=rv, v_fresh=wv.)

USAGE
-----
  pip install openai scipy
  export OPENAI_API_KEY=...
  # primary (objective): triager priority flips, from real triage traces
  python counterfactual_trace.py ../triage-traces --workload triage \
         --out cf_trace_triage.jsonl
  # secondary (judged): free-text cells from edit-review traces
  python counterfactual_trace.py ../edit-review-traces --workload edit-review \
         --judge --out cf_trace_edit.jsonl

Resumable: appends to --out; re-running skips firings already scored.
"""
from __future__ import annotations
import argparse
import json
import re
import sys
import time
from pathlib import Path

try:
    from scipy.stats import binomtest
except Exception:
    print("pip install scipy", file=sys.stderr); raise


PROMPTS = {
    "edit-review": {
        "editor": (
            "You are a document editor in a strict tool-use protocol.\n"
            "STEP 1: Call read_state(keys=['doc']).\n"
            "STEP 2: Call write_state(updates={'doc': '<one-sentence definition of distributed systems>'}).\n"
            "STEP 3: Reply with exactly DONE.\nNo prose before STEP 3."
        ),
        "reviewer": (
            "You are a reviewer in a strict tool-use protocol.\n"
            "STEP 1: Call read_state(keys=['doc']).\n"
            "STEP 2: Call write_state(updates={'review': '<one-sentence review>'}).\n"
            "STEP 3: Reply with exactly DONE.\nNo prose before STEP 3."
        ),
    },
    "plan-execute": {
        "executor": (
            "You are an executor in a strict tool-use protocol.\n"
            "STEP 1: Call read_state(keys=['plan']).\n"
            "STEP 2: Call write_state(updates={'result': '<execution result based on the plan>'}).\n"
            "STEP 3: Reply with exactly DONE.\nDo not write to any cell other than 'result'."
        ),
    },
    "triage": {
        "triager": (
            "You are a triager in a strict tool-use protocol.\n"
            "STEP 1: Call read_state(keys=['ticket']).\n"
            "STEP 2: Call write_state(updates={'priority': '<P0|P1|P2>'}).\n"
            "STEP 3: Reply with exactly DONE."
        ),
        "engineer": (
            "You are an engineer in a strict tool-use protocol.\n"
            "STEP 1: Call read_state(keys=['ticket', 'priority']).\n"
            "STEP 2: Call write_state(updates={'resolution': '<one-sentence resolution>'}).\n"
            "STEP 3: Reply with exactly DONE."
        ),
    },
}

DECISION = {
    "triage": {
        "triager": {"read": "ticket", "writes": "priority",
                    "type": "categorical", "labels": ["P0", "P1", "P2"]},
        "engineer": {"read": "priority", "writes": "resolution", "type": "text"},
    },
    "edit-review": {
        "editor": {"read": "doc", "writes": "doc", "type": "text"},
        "reviewer": {"read": "doc", "writes": "review", "type": "text"},
    },
    "plan-execute": {
        "executor": {"read": "plan", "writes": "result", "type": "text"},
    },
}


def load_events(path: Path) -> list[dict]:
    out = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            out.append(json.loads(line))
    return out


def agent_of(e: dict) -> str:
    """Raw pilot traces use 'agent'; extracted op-records use 'agent_id'."""
    return e.get("agent", e.get("agent_id", "?"))


def find_firings(events: list[dict], read_cell: str, agent: str):
    """Yield (v_stale, v_fresh) for each A1 firing where `agent` read `read_cell`."""
    writes = []
    for e in events:
        if read_cell in e.get("write_set", []):
            writes.append((e.get("write_time", 0), e.get("write_values", {}).get(read_cell, "")))
    for e in events:
        if agent_of(e) != agent:
            continue
        if read_cell not in e.get("read_set", []):
            continue
        rt = e.get("read_time", 0)
        rv = e.get("read_values", {}).get(read_cell, "")
        later = sorted([(wt, wv) for (wt, wv) in writes if wt > rt and wv != rv])
        if later:
            yield rv, later[0][1], dict(e.get("read_values", {}))


def call_model(client, model, system, user, max_tokens=60, temperature=0.0) -> str | None:
    for attempt in range(4):
        try:
            r = client.chat.completions.create(
                model=model,
                messages=[{"role": "system", "content": system},
                          {"role": "user", "content": user}],
                temperature=temperature, max_tokens=max_tokens)
            return (r.choices[0].message.content or "").strip()
        except Exception as e:
            time.sleep(1.5 * (attempt + 1))
            if attempt == 3:
                print(f"  api error: {e}", file=sys.stderr)
                return None


def _clean_write_value(text: str, cell: str) -> str:
    """Models often echo the tool-call syntax, e.g.
    write_state(updates={'doc': 'X'}) or {'doc': 'X'} or "doc": "X",
    instead of the bare value X. Extract X so the judge compares VALUES,
    not formatting. Falls back to the stripped raw text."""
    if text is None:
        return text
    t = text.strip()
    m = re.search(r'''["']%s["']\s*:\s*["'](.*?)["']\s*[}\)]?\s*$''' % re.escape(cell),
                  t, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r'''["']%s["']\s*:\s*["'](.*)''' % re.escape(cell), t, re.DOTALL)
    if m:
        return m.group(1).strip().rstrip("'\"}) ")
    t = re.sub(r'^\s*write_state\s*\(\s*updates\s*=\s*', '', t)
    return t.strip().strip("{}()").strip()


def decide(client, model, workload, agent, spec, payload) -> str | None:
    """Run the agent's STEP-2 decision given the FULL read payload it saw
    (a dict of cell->value); only the firing cell differs across conditions,
    co-read cells are held at their real values."""
    system = PROMPTS[workload][agent]
    shown = "{" + ", ".join(f"{k!r}: {v!r}" for k, v in payload.items()) + "}"
    if spec["type"] == "categorical":
        user = (f"You executed STEP 1. read_state returned {shown}.\n"
                f"Now perform STEP 2: output ONLY the value you would write for "
                f"'{spec['writes']}', i.e. exactly one of {spec['labels']}. "
                f"No other text.")
        out = call_model(client, model, system, user, max_tokens=8)
        if out is None:
            return None
        for lab in spec["labels"]:
            if lab.lower() in out.lower():
                return lab
        return None
    else:
        user = (f"You executed STEP 1. read_state returned {shown}.\n"
                f"Now perform STEP 2. Output ONLY the raw one-sentence text value "
                f"for '{spec['writes']}'. Do NOT include 'write_state', the cell "
                f"name, braces, or quotes -- just the sentence itself.")
        raw = call_model(client, model, system, user, max_tokens=120)
        if raw is None:
            return None
        return _clean_write_value(raw, spec["writes"])


def judge_text_divergence(client, model, a: str, b: str) -> bool | None:
    """Strict judge: do two free-text outputs reflect a materially different
    decision/content? Used only for non-categorical cells."""
    sys_j = ("You compare two agent outputs produced from two different inputs. "
             "Answer ONLY 'YES' if a downstream user relying on the output would "
             "reach a DIFFERENT decision or take a DIFFERENT action -- for "
             "example, one says the document is empty while the other reviews "
             "real content, or two different priority levels. Answer 'NO' if "
             "they convey the same decision or conclusion even when worded "
             "differently (for example, two valid definitions of the same term, "
             "or two paraphrases with the same substantive content). "
             "Reply with one word: YES or NO.")
    out = call_model(client, model, sys_j, f"OUTPUT A: {a}\nOUTPUT B: {b}", max_tokens=4)
    if out is None:
        return None
    u = out.strip().upper()
    if u.startswith("YES"):
        return True
    if u.startswith("NO"):
        return False
    return None


def clopper_pearson(k: int, n: int, alpha: float = 0.05):
    if n == 0:
        return (0.0, 1.0)
    ci = binomtest(k, n).proportion_ci(confidence_level=1 - alpha, method="exact")
    return (ci.low, ci.high)


def load_done(path: Path) -> set[str]:
    done = set()
    if path.exists():
        for line in path.read_text().splitlines():
            try:
                done.add(json.loads(line)["key"])
            except Exception:
                pass
    return done


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("trace_dirs", nargs="+", type=Path)
    ap.add_argument("--workload", choices=list(DECISION), required=True)
    ap.add_argument("--model", default="gpt-4o-2024-08-06")
    ap.add_argument("--judge", action="store_true",
                    help="use an LLM judge for free-text decision cells")
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    try:
        from openai import OpenAI
    except Exception:
        print("pip install openai", file=sys.stderr); raise
    client = OpenAI()

    out = args.out or Path(f"cf_trace_{args.workload}.jsonl")
    done = load_done(out)
    fh = out.open("a")

    files = []
    for d in args.trace_dirs:
        files += sorted(d.glob("*.jsonl"))
    print(f"trace files: {len(files)}  workload: {args.workload}")

    n_firings = 0
    for path in files:
        events = load_events(path)
        for agent, spec in DECISION[args.workload].items():
            if spec["type"] == "text" and not args.judge:
                continue
            for fi, (v_stale, v_fresh, ctx) in enumerate(find_firings(events, spec["read"], agent)):
                key = f"{path.name}:{agent}:{fi}"
                if key in done:
                    continue
                n_firings += 1
                payload_stale = {**ctx, spec["read"]: v_stale}
                payload_fresh = {**ctx, spec["read"]: v_fresh}
                d_stale = decide(client, args.model, args.workload, agent, spec, payload_stale)
                d_fresh = decide(client, args.model, args.workload, agent, spec, payload_fresh)
                if d_stale is None or d_fresh is None:
                    diverged = None
                elif spec["type"] == "categorical":
                    diverged = (d_stale != d_fresh)
                else:
                    diverged = judge_text_divergence(client, args.model, d_stale, d_fresh)
                rec = {"key": key, "agent": agent, "cell": spec["read"],
                       "decision_cell": spec["writes"], "type": spec["type"],
                       "v_stale": v_stale, "v_fresh": v_fresh,
                       "d_stale": d_stale, "d_fresh": d_fresh, "diverged": diverged}
                fh.write(json.dumps(rec) + "\n"); fh.flush()
    fh.close()

    rows = [json.loads(l) for l in out.read_text().splitlines() if l.strip()]
    def summarize(subset, label):
        sc = [r for r in subset if r["diverged"] is not None]
        k = sum(1 for r in sc if r["diverged"])
        n = len(sc)
        if n == 0:
            print(f"  {label}: no scored firings"); return
        lo, hi = clopper_pearson(k, n)
        print(f"  {label}: p_op = {k}/{n} = {100*k/n:.1f}%  "
              f"95% CP CI [{100*lo:.1f}%, {100*hi:.1f}%]")

    print("\n===== trace-grounded operational disagreement =====")
    print(f"total firings examined: {len(rows)}")
    cat = [r for r in rows if r["type"] == "categorical"]
    txt = [r for r in rows if r["type"] == "text"]
    print("PRIMARY (objective, categorical decision flip):")
    summarize(cat, "triager priority" if args.workload == "triage" else "categorical")
    if args.judge and txt:
        print("SECONDARY (LLM-judged, free-text cells -- softer signal):")
        summarize(txt, "free-text (judged)")
    agents = sorted({r["agent"] for r in rows})
    if len(agents) > 1:
        print("BY AGENT (report this split, not a blended number):")
        for a in agents:
            summarize([r for r in rows if r["agent"] == a], a)
    print("\nReport the categorical number as the headline; judged/by-agent")
    print("numbers carry comparator subjectivity and should be labelled as such.")


if __name__ == "__main__":
    main()