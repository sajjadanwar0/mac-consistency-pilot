#!/usr/bin/env python3
"""langgraph_interrupt_probe.py -- does interrupt() leave the A1 window open?

Section 6.3 predicted it would: "the human-in-the-loop interrupt, where the
pinned interval is minutes rather than seconds" was named as the sharp
follow-up, on the reasoning that a gate lasting minutes must swamp every
latency term and make stale-generation structural rather than a race.

This probe tests that prediction. It needs no API key and no model: the
question is about the framework's resumption semantics, not about what an
agent writes.

Result: the prediction is WRONG. interrupt() resumes by re-executing the
node from the top -- the docstring says so, "The graph resumes from the
start of the node, re-executing all logic" -- so a read taken before the
gate is re-taken after it, and the window is closed. Both where the value
lives in graph state and where it lives in a BaseStore.

The mechanism that closes the window opens a different hazard, which the
same probe measures: an irreversible external effect issued before the gate
is emitted TWICE, and if the shared value was revised during the gate the
two emissions carry DIFFERENT arguments. That is duplication, not the
reordering A6 formalizes, and the catalog of Section 3 has no predicate for
it -- our operational model assumes at-most-once externalization without
ever saying so.

Four cells, each discriminating:

    effect BEFORE the gate      runs=2  effects=2  arguments DIVERGE
    effect AFTER the gate       runs=2  effects=1  (the documented mitigation)
    no revision at all          runs=2  effects=2  arguments identical
    no interrupt at all         each node runs once

    python3 langgraph_interrupt_probe.py
    python3 langgraph_interrupt_probe.py --json results.json
"""
import argparse, json, sys, uuid
from typing import TypedDict

try:
    from langgraph.graph import StateGraph, START, END
    from langgraph.checkpoint.memory import InMemorySaver
    from langgraph.types import interrupt, Command
    from langgraph.store.memory import InMemoryStore
    import importlib.metadata as _md
    LG = _md.version("langgraph")
except Exception as e:  # noqa: BLE001
    print(f"langgraph not importable: {e}", file=sys.stderr)
    sys.exit(2)


class S(TypedDict):
    date: str
    booking: str


def read_survives_state():
    """Does a read from graph STATE survive the gate?"""
    def flight(state: S):
        observed = state["date"]
        interrupt({"confirm": observed})
        return {"booking": f"BOOKED {observed}"}
    g = StateGraph(S); g.add_node("flight", flight)
    g.add_edge(START, "flight"); g.add_edge("flight", END)
    app = g.compile(checkpointer=InMemorySaver())
    cfg = {"configurable": {"thread_id": str(uuid.uuid4())}}
    app.invoke({"date": "14 June", "booking": ""}, cfg)
    app.update_state(cfg, {"date": "21 June"})
    res = app.invoke(Command(resume="yes"), cfg)
    return "14 June" in res["booking"], res["booking"]


def read_survives_store():
    """Does a read from a BaseStore survive the gate?"""
    store = InMemoryStore()
    store.put(("trip",), "date", {"v": "14 June"})

    def flight(state: S, *, store):
        observed = store.get(("trip",), "date").value["v"]
        interrupt({"confirm": observed})
        return {"booking": f"BOOKED {observed}"}

    g = StateGraph(S); g.add_node("flight", flight)
    g.add_edge(START, "flight"); g.add_edge("flight", END)
    app = g.compile(checkpointer=InMemorySaver(), store=store)
    cfg = {"configurable": {"thread_id": str(uuid.uuid4())}}
    app.invoke({"date": "", "booking": ""}, cfg)
    store.put(("trip",), "date", {"v": "21 June"})
    res = app.invoke(Command(resume="yes"), cfg)
    return "14 June" in res["booking"], res["booking"]


def effect_cell(effect_before: bool, revise: bool):
    runs, effects = [], []

    def flight(state: S):
        runs.append(state["date"])
        if effect_before:
            effects.append(f"EMAIL {state['date']}")
        ans = interrupt({"confirm": state["date"]})
        if not effect_before:
            effects.append(f"EMAIL {state['date']}")
        return {"booking": f"BOOKED {state['date']} ({ans})"}

    g = StateGraph(S); g.add_node("flight", flight)
    g.add_edge(START, "flight"); g.add_edge("flight", END)
    app = g.compile(checkpointer=InMemorySaver())
    cfg = {"configurable": {"thread_id": str(uuid.uuid4())}}
    app.invoke({"date": "14 June", "booking": ""}, cfg)
    if revise:
        app.update_state(cfg, {"date": "21 June"})
    app.invoke(Command(resume="yes"), cfg)
    return len(runs), effects


def no_interrupt_control():
    runs = []

    def a(state: S):
        runs.append("a"); return {"date": state["date"]}

    def b(state: S):
        runs.append("b"); return {"booking": f"BOOKED {state['date']}"}

    g = StateGraph(S); g.add_node("a", a); g.add_node("b", b)
    g.add_edge(START, "a"); g.add_edge("a", "b"); g.add_edge("b", END)
    app = g.compile(checkpointer=InMemorySaver())
    app.invoke({"date": "14 June", "booking": ""},
               {"configurable": {"thread_id": str(uuid.uuid4())}})
    return runs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="write results here")
    a = ap.parse_args()

    stale_state, bk_state = read_survives_state()
    stale_store, bk_store = read_survives_store()
    r_before, e_before = effect_cell(True, True)
    r_after, e_after = effect_cell(False, True)
    r_norev, e_norev = effect_cell(True, False)
    plain = no_interrupt_control()

    print(f"langgraph {LG}\n")
    print("  A1 window across interrupt()")
    print(f"    value in graph state : booked {bk_state!r:26s} -> "
          f"{'STALE, window OPEN' if stale_state else 'refreshed, window CLOSED'}")
    print(f"    value in BaseStore   : booked {bk_store!r:26s} -> "
          f"{'STALE, window OPEN' if stale_store else 'refreshed, window CLOSED'}")
    print()
    print("  external effects around the gate")
    print(f"    effect BEFORE, revised   runs={r_before} effects={len(e_before)} {e_before}")
    print(f"    effect AFTER,  revised   runs={r_after} effects={len(e_after)} {e_after}")
    print(f"    effect BEFORE, no revision runs={r_norev} effects={len(e_norev)} {e_norev}")
    print(f"    no interrupt (control)   runs={plain}")
    print()
    diverge = len(set(e_before)) > 1
    print(f"  VERDICT window : {'OPEN' if (stale_state or stale_store) else 'CLOSED by node re-execution'}")
    print(f"  VERDICT effects: {'DUPLICATED' if len(e_before) > 1 else 'once'}"
          f"{', with DIVERGENT arguments' if diverge else ''}")

    if a.json:
        json.dump({
            "langgraph": LG,
            "window_open_graph_state": stale_state,
            "window_open_basestore": stale_store,
            "runs_effect_before": r_before, "effects_before": e_before,
            "runs_effect_after": r_after, "effects_after": e_after,
            "runs_no_revision": r_norev, "effects_no_revision": e_norev,
            "no_interrupt_runs": plain,
            "effects_diverge": diverge,
        }, open(a.json, "w"), indent=1)
        print(f"\n  wrote {a.json}")

    # The probe asserts what it found, so a change in framework semantics
    # fails it rather than being reported as if it were the old result.
    assert not stale_state and not stale_store, "window is OPEN -- Section 6.3's prediction would be right"
    assert r_before == 2 and len(e_before) == 2, "node no longer re-executes on resume"
    assert len(e_after) == 1, "placing the effect after the gate no longer avoids duplication"
    assert plain == ["a", "b"], "nodes re-run without an interrupt"


if __name__ == "__main__":
    main()
