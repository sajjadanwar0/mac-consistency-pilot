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

  # Open-weights replication via Ollama (OpenAI-compatible API):
  ollama serve &                 # if not already running
  ollama pull llama3.2
  python wallclock_cost_study.py --provider ollama --model llama3.2 \\
      --workload all --n 30 --out wallclock_llama32.json
  # (no OPENAI_API_KEY needed; dollar cost is ~0, wall-clock is the metric)

  # Smoke-test the harness with no LLM at all:
  python wallclock_cost_study.py --provider mock --workload all --n 20

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



def build_model_client(provider: str, model: str, base_url: str,
                       api_key: str):
    """Construct an AutoGen model client for the chosen provider.

    openai  -> default OpenAIChatCompletionClient (reads OPENAI_API_KEY)
    ollama  -> same client pointed at Ollama's OpenAI-compatible endpoint
               (http://localhost:11434/v1). Ollama ignores the api_key, but
               AutoGen requires model_info for non-OpenAI model strings, so we
               declare function_calling=True (llama3.2 supports tools).
    """
    from autogen_ext.models.openai import OpenAIChatCompletionClient
    if provider == "ollama":
        return OpenAIChatCompletionClient(
            model=model,
            base_url=(base_url or "http://localhost:11434/v1"),
            api_key=(api_key or "ollama"),
            model_info={
                "vision": False,
                "function_calling": True,
                "json_output": False,
                "family": "unknown",
                "structured_output": False,
            },
        )
    return OpenAIChatCompletionClient(model=model)


async def run_session_mock(workload: str, strategy: str, seed: int) -> dict:
    """No-LLM dry run: simulate the per-session call/abort structure so the
    metrics pipeline can be exercised without any provider. NOT for paper
    numbers -- wall-clock here is synthetic latency, not model inference."""
    wl = WORKLOADS[workload]
    rng = random.Random(seed)
    prob = {"vanilla": 0.0, "pessimistic": 0.20, "ssi": 0.05}.get(strategy, 0.0)
    calls = 0
    aborts = 0
    start = time.monotonic()
    for _name, _sysmsg in wl["agents"]:
        for kind in ("read", "write"):
            calls += 1
            await asyncio.sleep(rng.uniform(0.002, 0.008))
            if kind == "write" and rng.random() < prob:
                aborts += 1
                calls += 1
                await asyncio.sleep(rng.uniform(0.002, 0.008))
    return {
        "workload": workload,
        "strategy": strategy,
        "seed": seed,
        "wall_clock_seconds": time.monotonic() - start,
        "prompt_tokens": 0,
        "completion_tokens": 0,
        "tool_calls_made": calls,
        "aborts": aborts,
    }


async def run_session(workload: str, strategy: str, model: str,
                      seed: int, provider: str = "openai",
                      base_url: str = "", api_key: str = "") -> dict:
    """Run one session and return metrics."""
    from autogen_agentchat.agents import AssistantAgent
    from autogen_agentchat.teams import RoundRobinGroupChat
    from autogen_agentchat.conditions import (
        MaxMessageTermination, TextMentionTermination,
    )
    wl = WORKLOADS[workload]
    tools = wl["tool_factory"](seed)

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
        try:
            wrapped.__signature__ = inspect.signature(orig)
        except (ValueError, TypeError):
            pass
        return wrapped

    if strategy == "pessimistic":
        rng = random.Random(seed)
        for name, fn in list(tools.items()):
            if name.startswith(("edit_", "write_", "classify_")):
                tools[name] = wrap_for_abort(fn, name, 0.20, rng,
                                             "lock conflict")

    elif strategy == "ssi":
        rng = random.Random(seed + 1)
        for name, fn in list(tools.items()):
            if name.startswith(("edit_", "write_", "classify_")):
                tools[name] = wrap_for_abort(fn, name, 0.05, rng,
                                             "SSI validation failed")

    inner = build_model_client(provider, model, base_url, api_key)
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

    start = time.monotonic()
    result = await team.run(task=wl["task"])
    elapsed = time.monotonic() - start

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
    parser.add_argument("--provider", choices=["openai", "ollama", "mock"],
                        default="openai")
    parser.add_argument("--base-url", default="",
                        help="override base URL (ollama default "
                             "http://localhost:11434/v1)")
    parser.add_argument("--api-key", default="",
                        help="override API key (ollama ignores it)")
    parser.add_argument("--workload",
                        choices=list(WORKLOADS.keys()) + ["all"],
                        default="all")
    parser.add_argument("--strategies", default="vanilla,pessimistic,ssi")
    parser.add_argument("--n", type=int, default=30,
                        help="sessions per (strategy, workload) cell")
    parser.add_argument("--out", type=Path,
                        default=Path("wallclock_results.json"))
    args = parser.parse_args()

    if args.provider == "openai" and not os.environ.get("OPENAI_API_KEY"):
        raise SystemExit("OPENAI_API_KEY not set")
    if args.provider == "ollama" and args.model == "gpt-4o":
        args.model = "llama3.2"

    workloads = ([args.workload] if args.workload != "all"
                 else list(WORKLOADS.keys()))
    strategies = args.strategies.split(",")

    results = []
    for wl in workloads:
        for strat in strategies:
            print(f"\n=== {wl} | {strat} ===")
            for i in range(args.n):
                try:
                    if args.provider == "mock":
                        r = await run_session_mock(wl, strat, seed=i)
                    else:
                        r = await run_session(
                            wl, strat, args.model, seed=i,
                            provider=args.provider,
                            base_url=args.base_url, api_key=args.api_key)
                    results.append(r)
                    if (i + 1) % 5 == 0:
                        print(f"  {i+1}/{args.n}  wall_clock="
                              f"{r['wall_clock_seconds']:.1f}s  "
                              f"aborts={r['aborts']}")
                except Exception as e:
                    print(f"  {i}: ERROR {type(e).__name__}: {e}")

    args.out.write_text(json.dumps(results, indent=2))
    print(f"\nWrote {len(results)} records to {args.out}")

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