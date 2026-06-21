#!/usr/bin/env python3
"""
L3 live A6-prevention harness (mirror of the L2 live A3 run).

Reuses the validated ModelClient from prevalence_dynamic_run.py. Each session
fires `width` concurrent agent calls against a shared channel; the order the
calls RETURN is the real, latency-driven reorder source (this is the in-the-wild
cause of A6, not a synthetic shuffle). A6 fires iff the externalized commit
order (co) differs from the intended issuance order (io). Baseline externalizes
in completion order; the L3 sequencer re-serializes to issuance order.

Run from the same dir as prevalence_dynamic_run.py:
  uv run python l3_live_a6.py --n 40 --width 4
"""
from __future__ import annotations
import argparse, json
from concurrent.futures import ThreadPoolExecutor, as_completed

# reuse YOUR validated client (same folder)
from prevalence_dynamic_run import ModelClient

SYS = "Multi-agent workflow node. Reply with only a short value."

def l3_sequence(io_order, completion_order):
    """L3 commit-order sequencer: buffer, emit a prefix in issuance order as each
    effect completes (port of l3_sequencer.rs Mode::Sequenced). Always == io_order."""
    w = len(io_order); done = [False] * w; out, nxt = [], 0
    for fin in completion_order:
        done[fin] = True
        while nxt < w and done[nxt]:
            out.append(io_order[nxt]); nxt += 1
    return out

def a6_fires(io, co):
    return len(io) >= 2 and len(io) == len(co) and io != co

def run_session(client: ModelClient, width: int):
    io = list(range(width))
    def agent_call(aid: int) -> int:
        user = (f"You are agent {aid} of {width} writing tool effect {aid} to the "
                f"shared channel. Output only a short token.")
        try:
            client.complete(SYS, user, max_tokens=16)
        except Exception:
            pass
        return aid
    completion_order = []
    with ThreadPoolExecutor(max_workers=width) as ex:
        futs = [ex.submit(agent_call, a) for a in range(width)]
        for fut in as_completed(futs):
            completion_order.append(fut.result())   # real return order = co source
    co_base = completion_order[:]                    # baseline: externalize as completed
    co_seq  = l3_sequence(io, completion_order)      # L3: re-serialize to issuance order
    return a6_fires(io, co_base), a6_fires(io, co_seq), io, co_base, co_seq

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=40, help="sessions per model")
    ap.add_argument("--width", type=int, default=4, help="concurrent agents per session")
    ap.add_argument("--out", default="l3_live_a6.jsonl")
    args = ap.parse_args()

    # three model families, mirroring your L2 run. Ollama via its OpenAI-compatible
    # endpoint; drop/edit any row you don't want to run.
    models = [
        ("openai",    "gpt-4o-mini",       None),
        ("anthropic", "claude-haiku-4-5",  None),
        ("openai",    "llama3.2",          "http://localhost:11434/v1"),  # Ollama
    ]

    rows = []
    print(f"L3 live A6 prevention  (n={args.n}, width={args.width})")
    for provider, model, base_url in models:
        try:
            client = ModelClient(provider, model, base_url=base_url) if base_url \
                     else ModelClient(provider, model)
        except Exception as e:
            print(f"  {model:18} SKIP ({e})"); continue
        base_fire = seq_fire = 0
        for s in range(args.n):
            b, q, io, cob, coq = run_session(client, args.width)
            base_fire += int(b); seq_fire += int(q)
            rows.append({"model": model, "session": s, "io": io,
                         "co_baseline": cob, "co_l3": coq,
                         "a6_baseline": b, "a6_l3": q})
        print(f"  {model:18} baseline A6 = {base_fire}/{args.n}   "
              f"L3 sequencer A6 = {seq_fire}/{args.n}")
    with open(args.out, "w") as f:
        for r in rows: f.write(json.dumps(r) + "\n")
    print(f"\nwrote {args.out}. Report baseline A6 = X/N vs L3 = 0/N per family "
          f"(the L3 analogue of your L2 120-session A3 row).")

if __name__ == "__main__":
    main()