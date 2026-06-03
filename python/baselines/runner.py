"""
Synthetic baseline runner.

For each runtime in {vanilla, pessimistic, snapshot_isolation}:
  For each random scenario draw (--n times, seeded):
    Execute the scenario through that runtime.
    Emit a JSONL trace.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

# Make sibling modules importable.
HERE = Path(__file__).parent.resolve()
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "mac-consistency-pilot" / "python"))

import instrument as vanilla
from runtimes import pessimistic, snapshot_isolation


RUNTIMES = {
    "vanilla": vanilla.make_scenario,
    "pessimistic": pessimistic.make_scenario_pessimistic,
    "snapshot_isolation": snapshot_isolation.make_scenario_si,
}


def run_scenario(make_fn, scenario: dict, output_path: Path) -> dict:
    agent_ids = scenario["agents"]
    tool_ids = scenario.get("tools", [])
    store, tools, recorder, agents = make_fn(output_path, agent_ids, tool_ids)

    aborts = 0
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
        elif action == "remove_tool":
            tools.remove(phase["tool"])
        elif action == "add_tool":
            tools.add(phase["tool"])
        else:
            raise ValueError(f"unknown phase action: {action}")

    if hasattr(recorder, "aborts"):
        aborts = recorder.aborts

    recorder.close()
    return {"aborts": aborts}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=100)
    parser.add_argument(
        "--prompts",
        type=Path,
        default=HERE.parent / "mac-consistency-pilot" / "python" / "prompts.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=HERE / "synthetic_traces",
    )
    parser.add_argument("--seed", type=int, default=42)
    args = parser.parse_args()

    prompts = json.loads(args.prompts.read_text())
    print(f"Loaded {len(prompts)} prompt scenarios")

    for runtime_name, make_fn in RUNTIMES.items():
        random.seed(args.seed)
        out = args.output / runtime_name
        out.mkdir(parents=True, exist_ok=True)
        print(f"\n=== {runtime_name} ===")

        total_aborts = 0
        for i in range(args.n):
            scenario = random.choice(prompts)
            stats = run_scenario(make_fn, scenario, out / f"trace-{i:04d}.jsonl")
            total_aborts += stats.get("aborts", 0)
            if (i + 1) % 100 == 0 or i == args.n - 1:
                print(f"  {i + 1}/{args.n}  (last: {scenario['name']}, total aborts: {total_aborts})")

        # Write metadata.
        (out / "_metadata.json").write_text(
            json.dumps(
                {
                    "runtime": runtime_name,
                    "n": args.n,
                    "seed": args.seed,
                    "total_aborts": total_aborts,
                },
                indent=2,
            )
        )

    print(f"\nAll runtimes done. Output: {args.output}/")


if __name__ == "__main__":
    main()
