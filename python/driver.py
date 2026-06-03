"""
driver.py — runs N scenarios and writes one JSONL trace per scenario.

Each scenario in prompts.json has an `agents`, `tools`, and `phases` list.
Each phase is one of:
  {"action": "begin",       "agent": ..., "read": [...], "tool": ...}
  {"action": "commit",      "agent": ..., "write": {...}, "tool": ...}
  {"action": "atomic",      "agent": ..., "read": [...], "write": {...}, "tool": ...}
  {"action": "remove_tool", "tool": ...}
  {"action": "add_tool",    "tool": ...}

The driver supports interleaved begin/commit phases so scenarios can
surface A_1 (Stale-Generation) and A_2 (Phantom-Tool) reproducibly.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

from instrument import make_scenario


def run_phases(scenario: dict, output_path: Path) -> None:
    agent_ids = scenario["agents"]
    tool_ids = scenario.get("tools", [])
    store, tools, recorder, agents = make_scenario(
        output_path, agent_ids=agent_ids, tool_ids=tool_ids
    )

    for phase in scenario["phases"]:
        action = phase["action"]
        if action == "begin":
            agents[phase["agent"]].begin(
                read_keys=phase.get("read", []),
                planned_tool=phase.get("tool"),
            )
        elif action == "commit":
            agents[phase["agent"]].commit(
                write_kv=phase.get("write"),
                tool_used=phase.get("tool"),
            )
        elif action == "atomic":
            agents[phase["agent"]].op(
                read_keys=phase.get("read", []),
                write_kv=phase.get("write"),
                planned_tool=phase.get("tool"),
                tool_used=phase.get("tool"),
            )
        elif action == "raw_emit":
            from instrument import emit_raw
            emit_raw(recorder, phase["event"])
        elif action == "remove_tool":
            tools.remove(phase["tool"])
        elif action == "add_tool":
            tools.add(phase["tool"])
        else:
            raise ValueError(f"unknown phase action: {action}")

    recorder.close()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=10, help="Number of scenarios to run")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("../traces"),
        help="Output directory",
    )
    parser.add_argument(
        "--prompts",
        type=Path,
        default=Path(__file__).parent / "prompts.json",
        help="Path to prompts.json",
    )
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument(
        "--scenario",
        type=str,
        default=None,
        help="Run only this named scenario (otherwise random sampling)",
    )
    args = parser.parse_args()

    random.seed(args.seed)
    args.output.mkdir(parents=True, exist_ok=True)
    prompts = json.loads(args.prompts.read_text())
    print(f"Loaded {len(prompts)} prompt scenarios")

    if args.scenario:
        prompts = [p for p in prompts if p["name"] == args.scenario]
        if not prompts:
            raise SystemExit(f"no scenario named {args.scenario!r}")

    for i in range(args.n):
        scenario = random.choice(prompts)
        out = args.output / f"trace-{i:04d}.jsonl"
        run_phases(scenario, out)
        if (i + 1) % 10 == 0 or i == args.n - 1:
            print(f"  {i + 1}/{args.n}  (last: {scenario['name']})")
    print(f"Traces written to {args.output}/")


if __name__ == "__main__":
    main()