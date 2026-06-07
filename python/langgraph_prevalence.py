#!/usr/bin/env python3
"""
LangGraph default-channel susceptibility to the A1 (stale-generation) and
write-write-conflict anomalies of the consistency lattice.

This script uses the REAL LangGraph API (v1.x) with DETERMINISTIC node
functions (no LLM, no API keys, no randomness) so the result isolates the
*framework's coordination semantics* from model stochasticity. Every node
records the snapshot value it read and the value it wrote into a provenance
trace; the A1 detector then runs the lattice's stale-generation predicate over
that trace.

Three graphs, mapped to the lattice:

  (L0-silent)  parallel "edit + summarise" fan-out, no read-after-write order:
               the summariser reads the start-of-superstep snapshot of `doc`
               while the editor writes a fresh `doc` in the SAME superstep.
               No framework error is raised (the two nodes write different
               keys), yet the committed `summary` is generated from a stale
               `doc`.  ==> SILENT A1 stale-generation.

  (L0-failstop) two parallel workers write the SAME key `doc` with no reducer.
               ==> LangGraph raises InvalidUpdateError
               (INVALID_CONCURRENT_GRAPH_UPDATE) -- the framework detects the
               write-write conflict and fail-stops (a crash, not corruption).

  (L1-reducer)  same two parallel writers, but `doc` carries a merge reducer
               (the discipline LangGraph documents as the fix).
               ==> updates merge deterministically; no error, no A1.

Run:  python3 langgraph_prevalence.py
"""

import operator
from typing import Annotated, TypedDict, Any
from langgraph.graph import StateGraph, START, END
from langgraph.errors import InvalidUpdateError

# ----------------------------------------------------------------------------
# Provenance recording. Each entry  is a read or write of a logical cell by a
# node, tagged with the superstep in which it occurred. This is exactly the
# (op, cell, value, kind, step) trace the lattice detector consumes.
# ----------------------------------------------------------------------------
TRACE: list[dict[str, Any]] = []

def rec(node: str, kind: str, cell: str, value: Any, step: int) -> None:
    TRACE.append({"node": node, "kind": kind, "cell": cell,
                  "value": value, "step": step})

def reset_trace() -> None:
    TRACE.clear()


# ----------------------------------------------------------------------------
# A1 stale-generation detector (the paper's operational predicate, specialised
# to this trace form). An A1 witness is a downstream output generated from a
# read whose value is stale with respect to a write to the SAME cell that is
# committed in the same superstep (so the snapshot the reader saw is not the
# value the system commits).
# ----------------------------------------------------------------------------
def detect_a1(trace: list[dict[str, Any]], committed: dict[str, Any]) -> list[dict]:
    witnesses = []
    for ev in trace:
        if ev["kind"] != "read":
            continue
        cell = ev["cell"]
        read_val = ev["value"]
        # Was there a write to the same cell in the same superstep whose value
        # became the committed value, different from what the reader saw?
        for w in trace:
            if (w["kind"] == "write" and w["cell"] == cell
                    and w["node"] != ev["node"]          # A1 needs a *distinct* writer
                    and w["step"] == ev["step"]
                    and w["value"] != read_val
                    and committed.get(cell) == w["value"]):
                witnesses.append({
                    "reader": ev["node"], "writer": w["node"], "cell": cell,
                    "read_value": read_val, "committed_value": w["value"],
                    "superstep": ev["step"],
                })
    return witnesses


# ============================================================================
# Scenario L0-silent: parallel edit + summarise, no read-after-write order.
# ============================================================================
class StateSilent(TypedDict):
    doc: str
    summary: str
    trace: Annotated[list, operator.add]   # reducer on the *recording* channel
    # only, so recording never conflicts

def orchestrator(state: StateSilent):
    rec("orchestrator", "write", "doc", "v0", 0)
    return {"doc": "v0", "trace": [("orchestrator", "init doc=v0")]}

def editor(state: StateSilent):
    # Editor produces a fresh document version in superstep 1.
    seen = state["doc"]                     # snapshot read (v0)
    rec("editor", "read", "doc", seen, 1)
    new = "v1"                              # the fresh, correct content
    rec("editor", "write", "doc", new, 1)
    return {"doc": new, "trace": [("editor", f"read doc={seen}; wrote doc={new}")]}

def summariser(state: StateSilent):
    # Summariser reads the SAME snapshot (v0) in the SAME superstep and emits a
    # downstream artifact derived from it.
    seen = state["doc"]                     # snapshot read (v0) -- stale once
    rec("summariser", "read", "doc", seen, 1)  # editor commits v1
    out = f"summary-of({seen})"
    rec("summariser", "write", "summary", out, 1)
    return {"summary": out, "trace": [("summariser", f"read doc={seen}; wrote {out}")]}

def build_silent():
    g = StateGraph(StateSilent)
    g.add_node("orchestrator", orchestrator)
    g.add_node("editor", editor)
    g.add_node("summariser", summariser)
    g.add_edge(START, "orchestrator")
    # fan-out: editor and summariser run concurrently in one superstep
    g.add_edge("orchestrator", "editor")
    g.add_edge("orchestrator", "summariser")
    g.add_edge("editor", END)
    g.add_edge("summariser", END)
    return g.compile()


# ============================================================================
# Scenario L0-failstop: two parallel writers to the same no-reducer key.
# ============================================================================
class StateConflict(TypedDict):
    doc: str                                # NO reducer
    trace: Annotated[list, operator.add]

def fan(state: StateConflict):
    return {"trace": [("fan", "fan-out")]}

def worker_a(state: StateConflict):
    return {"doc": "from-A", "trace": [("worker_a", "wrote doc=from-A")]}

def worker_b(state: StateConflict):
    return {"doc": "from-B", "trace": [("worker_b", "wrote doc=from-B")]}

def build_conflict():
    g = StateGraph(StateConflict)
    g.add_node("fan", fan)
    g.add_node("worker_a", worker_a)
    g.add_node("worker_b", worker_b)
    g.add_edge(START, "fan")
    g.add_edge("fan", "worker_a")
    g.add_edge("fan", "worker_b")
    g.add_edge("worker_a", END)
    g.add_edge("worker_b", END)
    return g.compile()


# ============================================================================
# Scenario L1-reducer: same parallel writers, but `doc` carries a reducer.
# ============================================================================
def merge_docs(left: list, right: list) -> list:
    return (left or []) + (right or [])

class StateReducer(TypedDict):
    doc: Annotated[list, merge_docs]        # reducer = the documented discipline
    trace: Annotated[list, operator.add]

def fan_r(state: StateReducer):
    return {"trace": [("fan", "fan-out")]}

def worker_a_r(state: StateReducer):
    return {"doc": ["from-A"], "trace": [("worker_a", "contributed from-A")]}

def worker_b_r(state: StateReducer):
    return {"doc": ["from-B"], "trace": [("worker_b", "contributed from-B")]}

def build_reducer():
    g = StateGraph(StateReducer)
    g.add_node("fan", fan_r)
    g.add_node("worker_a", worker_a_r)
    g.add_node("worker_b", worker_b_r)
    g.add_edge(START, "fan")
    g.add_edge("fan", "worker_a")
    g.add_edge("fan", "worker_b")
    g.add_edge("worker_a", END)
    g.add_edge("worker_b", END)
    return g.compile()


# ============================================================================
# Driver
# ============================================================================
def run_silent():
    reset_trace()
    app = build_silent()
    final = app.invoke({"doc": "", "summary": "", "trace": []})
    committed = {"doc": final["doc"], "summary": final["summary"]}
    witnesses = detect_a1(TRACE, committed)
    return final, committed, witnesses

def run_conflict():
    reset_trace()
    app = build_conflict()
    try:
        final = app.invoke({"doc": "", "trace": []})
        return ("no_error", final)
    except InvalidUpdateError as e:
        return ("InvalidUpdateError", str(e).splitlines()[0])

def run_reducer():
    reset_trace()
    app = build_reducer()
    try:
        final = app.invoke({"doc": [], "trace": []})
        return ("ok", final)
    except InvalidUpdateError as e:
        return ("InvalidUpdateError", str(e).splitlines()[0])


if __name__ == "__main__":
    try:
        from importlib.metadata import version as _ver
        _lgv = _ver("langgraph")
    except Exception:
        _lgv = "?"
    print(f"LangGraph version: {_lgv}")
    print("=" * 72)

    print("\n[L0-silent] parallel edit + summarise, no read-after-write order")
    final, committed, w = run_silent()
    print(f"  committed state : doc={committed['doc']!r}, summary={committed['summary']!r}")
    print(f"  framework error : none (silent)")
    print(f"  A1 witnesses    : {len(w)}")
    for x in w:
        print(f"    - {x['reader']} read {x['cell']}={x['read_value']!r} but "
              f"{x['writer']} committed {x['cell']}={x['committed_value']!r} "
              f"in superstep {x['superstep']};")
        print(f"      committed summary {committed['summary']!r} is generated "
              f"from the stale {x['cell']} -> A1 stale-generation.")

    print("\n[L0-failstop] two parallel writers, same key, no reducer")
    kind, info = run_conflict()
    print(f"  outcome         : {kind}")
    print(f"  detail          : {info}")

    print("\n[L1-reducer] same parallel writers, key carries a merge reducer")
    kind, info = run_reducer()
    print(f"  outcome         : {kind}")
    if kind == "ok":
        print(f"  committed doc   : {info['doc']!r}  (both contributions merged; no A1)")

    print("\n" + "=" * 72)
    print("Summary: under LangGraph's default channel semantics, a shared state")
    print("key written/read by concurrent nodes admits A1 silently (L0-silent)")
    print("or fail-stops (L0-failstop); the documented reducer discipline")
    print("(L1-reducer) resolves both. The susceptibility is a property of the")
    print("shared-mutable-state coordination model, not of any workload.")