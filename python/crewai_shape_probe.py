#!/usr/bin/env python3
"""crewai_shape_probe.py -- can CrewAI even express the A1 window?

Section 6.3 lists "further frameworks that pin rather than refresh" as the
follow-up. For CrewAI the answer is not a rate: the framework REFUSES AT
CONSTRUCTION TIME to build the graph shape the window needs. No model calls
and no API key -- the question is about what the framework will accept.

Three cells, each discriminating:

  two async tasks, B.context = [A], trailing sync   REJECTED (async-context rule)
  two async tasks, no context edge, trailing sync   CONSTRUCTED
  async, SYNC between, async with context           CONSTRUCTED

So it is not a blanket ban on concurrency: two async tasks that share
nothing are legal, and a synchronous task between them is the documented
escape. What is rejected is precisely one concurrent task taking another
concurrent task's output as its context -- a concurrent read of a
concurrently-produced value, which is the precondition Definition 1 needs.

CrewAI's memory is also not a keyed mutable cell. Its surface is
MemoryRecord / MemoryMatch / MemorySlice with embed_text and
compute_composite_score: retrieval over records, not read-modify-write of a
named cell, so there is nothing for a second agent to overwrite mid-window.

    python3 crewai_shape_probe.py
    python3 crewai_shape_probe.py --json results.json
"""
import argparse, json, os, sys

os.environ.setdefault("OPENAI_API_KEY", "sk-probe-not-used")  # never called

try:
    from crewai import Agent, Task, Crew, Process
    import importlib.metadata as _md
    CV = _md.version("crewai")
except Exception as e:  # noqa: BLE001
    print(f"crewai not importable: {e}", file=sys.stderr)
    sys.exit(2)


def agents():
    return (Agent(role="flight", goal="g", backstory="b", llm="gpt-4o-mini"),
            Agent(role="date", goal="g", backstory="b", llm="gpt-4o-mini"))


def attempt(tasks, ags):
    try:
        Crew(agents=ags, tasks=tasks, process=Process.sequential)
        return "CONSTRUCTED", None
    except Exception as e:  # noqa: BLE001
        t = str(e)
        kind = ("async_task_count" if "async_task_count" in t else
                "async-context rule" if "cannot include other sequential asynchronous" in t else
                "future-task rule" if "future" in t.lower() else "other")
        return "REJECTED", kind


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--json"); a = ap.parse_args()
    out = {"crewai": CV, "cells": {}}

    a1, a2 = agents()
    tA = Task(description="read+book", expected_output="o", agent=a1, async_execution=True)
    tB = Task(description="revise", expected_output="o", agent=a2, async_execution=True, context=[tA])
    tE = Task(description="finish", expected_output="o", agent=a1)
    out["cells"]["async_context_async"] = attempt([tA, tB, tE], [a1, a2])

    a1, a2 = agents()
    tA2 = Task(description="read+book", expected_output="o", agent=a1, async_execution=True)
    tB2 = Task(description="revise", expected_output="o", agent=a2, async_execution=True)
    tE2 = Task(description="finish", expected_output="o", agent=a1)
    out["cells"]["async_async_no_edge"] = attempt([tA2, tB2, tE2], [a1, a2])

    a1, a2 = agents()
    tA3 = Task(description="read+book", expected_output="o", agent=a1, async_execution=True)
    tS = Task(description="checkpoint", expected_output="o", agent=a1)
    tB3 = Task(description="revise", expected_output="o", agent=a2, async_execution=True, context=[tA3])
    tE3 = Task(description="finish", expected_output="o", agent=a1)
    out["cells"]["async_sync_async_context"] = attempt([tA3, tS, tB3, tE3], [a1, a2])

    import crewai.memory as M
    surface = sorted(n for n in dir(M) if not n.startswith("_"))
    out["memory_surface"] = surface
    out["keyed_mutable_cell"] = any(n.lower() in {"get", "set", "put", "update"} for n in surface)

    print(f"crewai {CV}\n")
    for k, (verdict, kind) in out["cells"].items():
        print(f"  {k:28s} {verdict}{'' if kind is None else f'  ({kind})'}")
    print(f"\n  memory surface: {surface[:8]}")
    print(f"  keyed mutable cell present: {out['keyed_mutable_cell']}")
    print("\n  VERDICT: the A1 window is not expressible -- the concurrent-read shape is")
    print("           rejected at construction, and memory is retrieval, not a keyed cell.")

    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)
        print(f"\n  wrote {a.json}")

    assert out["cells"]["async_context_async"][0] == "REJECTED", "CrewAI now accepts the concurrent-read shape"
    assert out["cells"]["async_context_async"][1] == "async-context rule", "rejected, but by a different rule than recorded"
    assert out["cells"]["async_async_no_edge"][0] == "CONSTRUCTED", "CrewAI now bans concurrency outright -- the finding is weaker than recorded"
    assert out["cells"]["async_sync_async_context"][0] == "CONSTRUCTED", "the sync-separated escape no longer works"
    assert not out["keyed_mutable_cell"], "a keyed mutable cell has appeared in crewai.memory"


if __name__ == "__main__":
    main()
