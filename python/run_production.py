"""
run_production.py - Orchestration harness for production-trace cookbook runs.

USAGE
  uv run python run_production.py --scenario research_collab --n 100 \\
      --provider openai --output ../production_traces/

  uv run python run_production.py --scenario all --n 100 \\
      --provider openai --output ../production_traces/

Each session produces one JSONL file under the output directory:
  <scenario>-<provider>-<NNNN>.jsonl

The JSONL files match the format consumed by analyze_production.py and
by the existing verified detector pipeline.

DESIGN NOTES
  - Framework code (autogen) is unmodified.
  - The LLM client is wrapped in ProductionExtractor, which records
    each `.create(...)` call as an OpRecord.
  - All scenario tools are deterministic mocks (no external API hits)
    so the per-session cost is just the LLM token cost.
  - Provider defaults: openai/gpt-4o or anthropic/claude-sonnet-4-5-20250929.
"""

from __future__ import annotations
import argparse
import asyncio
import os
import sys
from pathlib import Path

from autogen_agentchat.agents import AssistantAgent
from autogen_agentchat.teams import RoundRobinGroupChat
from autogen_agentchat.conditions import (
    MaxMessageTermination,
    TextMentionTermination,
)

from production_extractor import ProductionExtractor, OpRecorder
from production_scenarios import SCENARIOS

DEFAULT_MODEL = {
    "openai": "gpt-4o",
    "anthropic": "claude-sonnet-4-5-20250929",
}


def _make_inner_client(provider: str, model: str):
    if provider == "anthropic":
        from autogen_ext.models.anthropic import AnthropicChatCompletionClient
        return AnthropicChatCompletionClient(model=model)
    from autogen_ext.models.openai import OpenAIChatCompletionClient
    return OpenAIChatCompletionClient(model=model)


def _check_api_key(provider: str) -> None:
    if provider == "openai" and not os.environ.get("OPENAI_API_KEY"):
        raise SystemExit("OPENAI_API_KEY not set")
    if provider == "anthropic" and not os.environ.get("ANTHROPIC_API_KEY"):
        raise SystemExit("ANTHROPIC_API_KEY not set")


async def run_one_session(scenario_fn, session_idx: int,
                          provider: str, model: str,
                          output_dir: Path) -> Path:
    scenario = scenario_fn(seed=session_idx)
    sid = f"{session_idx:04d}"
    trace_path = output_dir / f"{scenario['name']}-{provider}-{sid}.jsonl"
    rec = OpRecorder(
        trace_path, scenario["name"], sid,
        stateful_tools=scenario.get("stateful_tools", {}),
    )
    rec.open()

    try:
        # Build wrapped clients (one per agent, sharing the recorder)
        agents = []
        for name, sysmsg in scenario["agents"]:
            inner = _make_inner_client(provider, model)
            wrapped = ProductionExtractor(inner, rec, agent_name=name)
            agents.append(AssistantAgent(
                name=name,
                model_client=wrapped,
                tools=list(scenario["tools"].values()),
                system_message=sysmsg,
                reflect_on_tool_use=False,
            ))

        termination = (
                TextMentionTermination("DONE")
                | TextMentionTermination("APPROVED")
                | MaxMessageTermination(max_messages=scenario["max_turns"])
        )
        team = RoundRobinGroupChat(agents, termination_condition=termination)
        await team.run(task=scenario["task"])
    finally:
        rec.close()

    return trace_path


async def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scenario", default="all",
                        help="scenario name or 'all'")
    parser.add_argument("--n", type=int, default=100,
                        help="sessions per scenario")
    parser.add_argument("--start", type=int, default=0,
                        help="starting session index (for resume)")
    parser.add_argument("--provider", choices=["openai", "anthropic"],
                        default="openai")
    parser.add_argument("--model", default=None)
    parser.add_argument("--output", type=Path,
                        default=Path("../production_traces"))
    args = parser.parse_args()

    _check_api_key(args.provider)
    model = args.model or DEFAULT_MODEL[args.provider]
    args.output.mkdir(parents=True, exist_ok=True)

    scenarios_to_run = (list(SCENARIOS.keys())
                        if args.scenario == "all"
                        else [args.scenario])
    if args.scenario != "all" and args.scenario not in SCENARIOS:
        raise SystemExit(f"Unknown scenario {args.scenario!r}. "
                         f"Available: {list(SCENARIOS.keys())}")

    print(f"provider={args.provider} model={model}")
    print(f"scenarios={scenarios_to_run} n={args.n} start={args.start}")
    print(f"output -> {args.output.resolve()}")
    print()

    end = args.start + args.n
    for scenario_name in scenarios_to_run:
        scenario_fn = SCENARIOS[scenario_name]
        print(f"=== {scenario_name} ===")
        for i in range(args.start, end):
            try:
                out = await run_one_session(scenario_fn, i, args.provider,
                                            model, args.output)
            except Exception as e:
                print(f"  {i}: ERROR {type(e).__name__}: {e}")
                continue
            done = i - args.start + 1
            if done % 10 == 0 or i == end - 1:
                events = out.read_text().count("\n")
                print(f"  {done}/{args.n}  idx={i}  last_events={events}")
        print()


if __name__ == "__main__":
    asyncio.run(main())