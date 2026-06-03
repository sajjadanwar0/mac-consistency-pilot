"""
wallclock_cost_study.py - Within-model wall-clock cost comparison
across three runtime strategies (vanilla, pessimistic, SSI) on the
SAME model. Closes R2's concern that the cross-model cost analysis
is confounded by tokenization, pricing, and serialisation
differences between providers.

USAGE
  export OPENAI_API_KEY="sk-..."
  python wallclock_cost_study.py \\
      --model gpt-4o \\
      --workload edit_review \\
      --strategies vanilla,pessimistic,ssi \\
      --n 30 \\
      --out wallclock_results.json

  # Then for the other workloads:
  python wallclock_cost_study.py --workload plan_execute ...
  python wallclock_cost_study.py --workload triage ...

OUTPUT
  JSON with per-strategy per-session metrics:
    - wall_clock_seconds: end-to-end session time (best metric for
      "real cost" since it captures aborted-generation waste)
    - prompt_tokens, completion_tokens (for comparison with v5_3
      analysis)
    - tool_calls_made: count of tool calls (operations count)
    - aborts: count of abort events
  Plus aggregated mean / 95% bootstrap CI per (strategy, workload).

DESIGN
  This script REPLACES the existing autogen_pilot.py's token-only
  measurement with explicit wall-clock measurement around each
  session's run(). The wall-clock includes:
    - LLM inference time for every call (including those whose
      commits later abort)
    - Tool execution time
    - Network / retry latencies
  It does NOT include:
    - Process startup overhead (we measure within an established
      session loop)
    - Trace serialisation time

  The within-model comparison fixes one model (e.g., gpt-4o) and
  varies the runtime strategy. This isolates the runtime-overhead
  question that the cross-model comparison in v5_3 confounded.

  Estimated cost: with N=30 sessions per (strategy, workload) and
  3 strategies x 3 workloads = 270 sessions total. At roughly
  $0.05 per session for gpt-4o, total ~$15. Wall-clock duration
  approximately 4-6 hours depending on tool latency.
"""

from __future__ import annotations
import argparse
import asyncio
import functools
import inspect
import json
import os
import random
import statistics
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any


# ---------------------------------------------------------------------
# Workload definitions (mirror the v5_3 paper's three workloads but
# use deterministic mock tools so we measure only LLM and runtime
# overhead, not external service latency)
# ---------------------------------------------------------------------

def make_edit_review_tools(seed: int):
    """Edit-review workload: edit_doc + review_doc tools sharing a doc cell."""
    state = {"doc": "Initial document draft."}

    def read_doc() -> str:
        return state["doc"]

    def edit_doc(new_content: str) -> str:
        state["doc"] = new_content
        return f"OK: doc updated to length {len(new_content)}"

    def submit_review(approved: bool) -> str:
        return f"Review submitted: approved={approved}"

    return {
        "read_doc": read_doc,
        "edit_doc": edit_doc,
        "submit_review": submit_review,
    }


def make_plan_execute_tools(seed: int):
    """Plan-execute workload: planner writes a plan, executor reads it."""
    state = {"plan": "EMPTY"}

    def read_plan() -> str:
        return state["plan"]

    def write_plan(plan: str) -> str:
        state["plan"] = plan
        return f"OK: plan length {len(plan)}"

    def execute_step(step: str) -> str:
        return f"Executed: {step[:60]}"

    return {
        "read_plan": read_plan,
        "write_plan": write_plan,
        "execute_step": execute_step,
    }


def make_triage_tools(seed: int):
    """Triage workload: shared classification + specialist response."""
    state = {"classification": "UNKNOWN", "response": "EMPTY"}

    def classify_ticket(category: str) -> str:
        state["classification"] = category
        return f"OK: classified as {category}"

    def read_classification() -> str:
        return state["classification"]

    def write_response(content: str) -> str:
        state["response"] = content
        return f"OK: response of length {len(content)} stored"

    return {
        "classify_ticket": classify_ticket,
        "read_classification": read_classification,
        "write_response": write_response,
    }


WORKLOADS = {
    "edit_review": {
        "tool_factory": make_edit_review_tools,
        "agents": [
            ("editor",
             "Read the doc with read_doc, then call edit_doc with a "
             "revised version. Reply 'HANDOFF' when done. Max 2 tool calls."),
            ("reviewer",
             "Read the doc with read_doc, then call submit_review. "
             "Reply 'DONE'. Max 2 tool calls."),
        ],
        "task": "Improve the draft document.",
        "max_turns": 6,
    },
    "plan_execute": {
        "tool_factory": make_plan_execute_tools,
        "agents": [
            ("planner",
             "Call write_plan with a 2-sentence plan, then reply 'HANDOFF'."),
            ("executor",
             "Call read_plan, then call execute_step with the first step, "
             "then reply 'DONE'."),
        ],
        "task": "Plan and execute organizing a desk.",
        "max_turns": 6,
    },
    "triage": {
        "tool_factory": make_triage_tools,
        "agents": [
            ("triager",
             "Call classify_ticket with 'billing' or 'technical', reply 'HANDOFF'."),
            ("specialist",
             "Call read_classification, then write_response, reply 'DONE'."),
        ],
        "task": "Customer ticket: 'My subscription was charged twice.'",
        "max_turns": 6,
    },
}


# ---------------------------------------------------------------------
# Strategy-specific session executors. The strategy is the
# concurrency-control discipline applied to tool-call commits.
# ---------------------------------------------------------------------

async def run_session(workload: str, strategy: str, model: str,
                      seed: int) -> dict:
    """Run one session and return metrics."""
    from autogen_agentchat.agents import AssistantAgent
    from autogen_agentchat.teams import RoundRobinGroupChat
    from autogen_agentchat.conditions import (
        MaxMessageTermination, TextMentionTermination,
    )
    from autogen_ext.models.openai import OpenAIChatCompletionClient

    wl = WORKLOADS[workload]
    tools = wl["tool_factory"](seed)

    # Abort counter as a mutable container so wrappers can increment it
    # without `nonlocal` crossing the make_wrapped boundary.
    abort_box = [0]

    def wrap_for_abort(orig, name, prob, rng, reason):
        """Return a wrapper that aborts with probability `prob`, but
        preserves the original function's signature, name, docstring,
        and annotations so AutoGen can still build a tool schema from
        it. The previous version used `def wrapped(*args, **kw)`, whose
        empty schema caused AutoGen to reject the tool at registration
        time -- which silently skipped every pessimistic/ssi session."""
        @functools.wraps(orig)
        def wrapped(*args, **kw):
            if rng.random() < prob:
                abort_box[0] += 1
                return f"ABORT: {reason} on {name}"
            return orig(*args, **kw)
        # Critical: copy the real signature so inspect.signature(wrapped)
        # returns the original typed parameters, not (*args, **kw).
        try:
            wrapped.__signature__ = inspect.signature(orig)
        except (ValueError, TypeError):
            pass
        return wrapped

    if strategy == "pessimistic":
        # Pessimistic: each write may fail on conflict (20%), forcing a
        # retry that the agent must handle. Aborts count the rejections.
        rng = random.Random(seed)
        for name, fn in list(tools.items()):
            if name.startswith(("edit_", "write_", "classify_")):
                tools[name] = wrap_for_abort(fn, name, 0.20, rng,
                                             "lock conflict")

    elif strategy == "ssi":
        # SSI: writes succeed but commit-time validation may abort (5%).
        rng = random.Random(seed + 1)
        for name, fn in list(tools.items()):
            if name.startswith(("edit_", "write_", "classify_")):
                tools[name] = wrap_for_abort(fn, name, 0.05, rng,
                                             "SSI validation failed")
    # vanilla: no wrapping, no aborts

    inner = OpenAIChatCompletionClient(model=model)
    agents = []
    for name, sysmsg in wl["agents"]:
        agents.append(AssistantAgent(
            name=name,
            model_client=inner,
            tools=list(tools.values()),
            system_message=sysmsg,
            reflect_on_tool_use=False,
        ))

    termination = (
            TextMentionTermination("DONE")
            | MaxMessageTermination(max_messages=wl["max_turns"])
    )
    team = RoundRobinGroupChat(agents, termination_condition=termination)

    # Measure wall clock
    start = time.monotonic()
    result = await team.run(task=wl["task"])
    elapsed = time.monotonic() - start

    # Token usage (best-effort extraction from autogen result)
    prompt_tokens = 0
    completion_tokens = 0
    tool_calls_made = 0
    if hasattr(result, "messages"):
        for m in result.messages:
            usage = getattr(m, "models_usage", None)
            if usage is not None:
                prompt_tokens += getattr(usage, "prompt_tokens", 0) or 0
                completion_tokens += getattr(usage, "completion_tokens", 0) or 0
            content = getattr(m, "content", None)
            if isinstance(content, list):
                for item in content:
                    if hasattr(item, "name") and getattr(item, "name", None):
                        tool_calls_made += 1

    return {
        "workload": workload,
        "strategy": strategy,
        "seed": seed,
        "wall_clock_seconds": elapsed,
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "tool_calls_made": tool_calls_made,
        "aborts": abort_box[0],
    }


# ---------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------

def bootstrap_mean_ci(values: list[float], n: int = 1000) -> tuple[float, float, float]:
    if not values:
        return (0.0, 0.0, 0.0)
    rng = random.Random(42)
    means = []
    k = len(values)
    for _ in range(n):
        sample = [values[rng.randint(0, k - 1)] for _ in range(k)]
        means.append(sum(sample) / k)
    means.sort()
    return (statistics.mean(values), means[int(n * 0.025)], means[int(n * 0.975)])


async def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", default="gpt-4o")
    parser.add_argument("--workload",
                        choices=list(WORKLOADS.keys()) + ["all"],
                        default="all")
    parser.add_argument("--strategies", default="vanilla,pessimistic,ssi")
    parser.add_argument("--n", type=int, default=30,
                        help="sessions per (strategy, workload) cell")
    parser.add_argument("--out", type=Path,
                        default=Path("wallclock_results.json"))
    args = parser.parse_args()

    if not os.environ.get("OPENAI_API_KEY"):
        raise SystemExit("OPENAI_API_KEY not set")

    workloads = ([args.workload] if args.workload != "all"
                 else list(WORKLOADS.keys()))
    strategies = args.strategies.split(",")

    results = []
    for wl in workloads:
        for strat in strategies:
            print(f"\n=== {wl} | {strat} ===")
            for i in range(args.n):
                try:
                    r = await run_session(wl, strat, args.model, seed=i)
                    results.append(r)
                    if (i + 1) % 5 == 0:
                        print(f"  {i+1}/{args.n}  wall_clock="
                              f"{r['wall_clock_seconds']:.1f}s  "
                              f"aborts={r['aborts']}")
                except Exception as e:
                    print(f"  {i}: ERROR {type(e).__name__}: {e}")

    args.out.write_text(json.dumps(results, indent=2))
    print(f"\nWrote {len(results)} records to {args.out}")

    # Per-cell summary
    print("\n=== Summary (mean wall-clock, 95% CI) ===")
    print(f"{'workload':16} {'strategy':12} {'n':>4} "
          f"{'wall_clock_s':>15} {'95% CI':>20} {'tokens':>10}")
    cells: dict[tuple[str, str], list[dict]] = {}
    for r in results:
        cells.setdefault((r["workload"], r["strategy"]), []).append(r)
    for (wl, strat), rs in sorted(cells.items()):
        wcs = [r["wall_clock_seconds"] for r in rs]
        toks = [r["prompt_tokens"] + r["completion_tokens"] for r in rs]
        mean_wc, lo, hi = bootstrap_mean_ci(wcs)
        mean_tok = statistics.mean(toks) if toks else 0
        print(f"{wl:16} {strat:12} {len(rs):>4} "
              f"{mean_wc:>14.2f} [{lo:>5.2f}, {hi:>5.2f}] "
              f"{mean_tok:>10.0f}")


if __name__ == "__main__":
    asyncio.run(main())