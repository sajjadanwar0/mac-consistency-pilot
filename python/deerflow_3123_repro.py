#!/usr/bin/env python3
"""
In-the-wild reproduction of a SILENT coordination anomaly in a major
third-party LangGraph application: bytedance/deer-flow issue #3123
("todos visible during streaming but disappear after the run finishes",
opened 2026-05-21, status: open).

Root cause (from deer-flow's own regression test docstring): a downstream
node's partial state update with `todos=None` overwrites the previously
accumulated `todos` value under LangGraph's default last-write-wins channel
semantics. No error is raised -- the accumulated list silently vanishes.

This is the SILENT variant of the lattice's L0 unsynchronized-shared-state
anomaly class (a lost-update / stale-overwrite: the surviving state is stale
with respect to the accumulated value). It needs no parallelism and no LLM --
it is a property of the default channel semantics.

We reproduce it on real LangGraph using deer-flow's ACTUAL reducer
(`merge_todos`, copied verbatim from
backend/packages/harness/deerflow/agents/thread_state.py, the #3180 fix):

  (L0 default)  todos: bare key, no reducer
                -> downstream {"todos": None} overwrites -> SILENT loss (#3123)

  (L1 reducer)  todos: Annotated[list, merge_todos]   (deer-flow's fix #3180)
                -> None preserves the accumulated value -> no loss

Honest note on the fix (#3199): adding the reducer then conflicted with
LangChain's TodoListMiddleware, which declares the `todos` channel with a
different type ("Channel 'todos' already exists with a different type"); the
resolution is a single consistent channel contract. The L0->L1 ascent is real
but requires agreement on the channel's reducer across components.

Run:  python3 deerflow_3123_repro.py
"""

from typing import Annotated, NotRequired, TypedDict
from langgraph.graph import StateGraph, START, END


def merge_todos(existing: list | None, new: list | None) -> list | None:
    """Reducer for ThreadState.todos - keeps the last non-None value."""
    if new is None:
        return existing
    return new


SEED_TODOS = [{"id": 1, "text": "research topic", "done": False},
              {"id": 2, "text": "draft report", "done": False}]


def seed(state):
    return {"todos": list(SEED_TODOS)}

def finalise(state):
    return {"todos": None, "done": True}


class StateBare(TypedDict):
    todos: NotRequired[list]
    done: NotRequired[bool]

def build_bare():
    g = StateGraph(StateBare)
    g.add_node("seed", seed)
    g.add_node("finalise", finalise)
    g.add_edge(START, "seed")
    g.add_edge("seed", "finalise")
    g.add_edge("finalise", END)
    return g.compile()


class StateReduced(TypedDict):
    todos: Annotated[list, merge_todos]
    done: NotRequired[bool]

def build_reduced():
    g = StateGraph(StateReduced)
    g.add_node("seed", seed)
    g.add_node("finalise", finalise)
    g.add_edge(START, "seed")
    g.add_edge("seed", "finalise")
    g.add_edge("finalise", END)
    return g.compile()


if __name__ == "__main__":
    try:
        from importlib.metadata import version as _ver
        lgv = _ver("langgraph")
    except Exception:
        lgv = "?"
    print(f"LangGraph version: {lgv}")
    print("Reproducing bytedance/deer-flow issue #3123 (silent todos loss)")
    print("=" * 72)

    print("\n[L0 default] todos: bare key, no reducer")
    final = build_bare().invoke({})
    n = len(final.get("todos") or [])
    print(f"  seeded {len(SEED_TODOS)} todos; after a downstream "
          f"partial-update todos=None ...")
    print(f"  committed todos: {final.get('todos')!r}")
    print(f"  -> {n} todos survive. framework error: none (SILENT).")
    print(f"  -> the accumulated list vanished == deer-flow #3123.")

    print("\n[L1 reducer] todos: Annotated[list, merge_todos]  (deer-flow #3180 fix)")
    final = build_reduced().invoke({})
    n = len(final.get("todos") or [])
    print(f"  committed todos: {[t['text'] for t in final.get('todos') or []]}")
    print(f"  -> {n} todos survive. the reducer keeps the last non-None value.")

    print("\n" + "=" * 72)
    print("A downstream None partial-update silently clobbers accumulated shared")
    print("state under LangGraph's default last-write-wins channel (L0); the")
    print("documented reducer (L1) prevents it. This is a real, open, silent")
    print("coordination anomaly in a major third-party agent framework -- the")
    print("L0->L1 ascent the lattice formalises, observed in the wild.")