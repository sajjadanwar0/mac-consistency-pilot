#!/usr/bin/env python3
"""langgraph_extract.py -- build a prevalence_static.Topology from a REAL
compiled LangGraph StateGraph, and report what that costs in precision.

WHY THIS EXISTS
  prevalence_static.py scores hand-encoded topologies: someone reads the
  framework's documentation and types in each node's read and write channel
  sets. That is fine for a catalogue of canonical patterns and it is how the
  k-of-N bound in the appendix was produced. It is not an instrument you can
  point at somebody else's graph, and the k-of-N number is only as good as
  the encoding it was given.

  This module points the same predicate at a compiled StateGraph and reports
  the verdict at the precision the FRAMEWORK actually exposes.

WHAT LANGGRAPH 1.2 EXPOSES, AND WHAT IT DOES NOT
  free and sound:
    layers      from builder.edges (+ the compiled nodes' triggers)
    read set    compiled_node.channels -- for a TypedDict state this is the
                FULL state schema, because a node body receives the whole
                state object and the framework cannot know which keys it
                touches
    reducer     type(builder.channels[c]) -- BinaryOperatorAggregate means an
                Annotated[..., reducer] channel, LastValue means overwrite
  NOT exposed:
    write set   ChannelWrite carries ChannelWriteTupleEntry(mapper=_get_updates,
                static=None). `static=None` is literal: the channels a node
                writes are whatever dict its body returns at run time. There
                is no per-node output schema in this version.

  So a sound extractor must over-approximate the write set, and the only
  sound over-approximation available is "any channel in the schema".

THE CONSEQUENCE, WHICH IS THE POINT OF THIS FILE
  The structural predicate is `same layer /\\ distinct agents /\\
  reads(reader) INTERSECT writes(writer) /= {}`. Under extraction the read
  set is the whole schema, so the intersection is non-empty whenever two
  co-layer nodes exist at all, and the predicate degenerates: it flags every
  concurrent graph. The hand-encoded precision that produces the k-of-N split
  is strictly finer than anything derivable from the object.

  A second rule IS derivable and IS sound, using the one piece of information
  the framework does expose: flag a co-layer shared channel only when it is
  LastValue (overwrite) rather than BinaryOperatorAggregate (merge). That is
  not the same predicate -- it is a lost-update criterion, not a relaxation
  of Definition 1 -- and this module reports both rather than conflating them.

    python3 python/langgraph_extract.py            # the demonstration corpus
    python3 python/langgraph_extract.py --json out.json
"""
import argparse
import json
import sys

START = "__start__"
END = "__end__"


# --------------------------------------------------------------------------
# extraction
# --------------------------------------------------------------------------
def extract(builder, compiled, name, agents=None, source="compiled StateGraph"):
    """Return (edges, reads, writes, reducer_channels, schema) from a graph.

    `builder` is the StateGraph, `compiled` its .compile() result.
    """
    schema = [c for c in builder.channels]
    reducer = set()
    for c, ch in builder.channels.items():
        if type(ch).__name__ == "BinaryOperatorAggregate":
            reducer.add(c)

    nodes = [n for n in builder.nodes]
    edges = []
    for a, b in builder.edges:
        edges.append((a, b))

    # read set: what the framework says the node is handed
    reads = {}
    for n in nodes:
        ch = getattr(compiled.nodes.get(n), "channels", None)
        if isinstance(ch, list):
            reads[n] = set(ch)
        elif isinstance(ch, str):
            reads[n] = {ch}
        else:
            reads[n] = set(schema)

    # write set: not exposed. Record that fact rather than guess.
    writes_known = {}
    for n in nodes:
        node = compiled.nodes.get(n)
        static_seen = []
        for w in getattr(node, "writers", []) or []:
            for entry in getattr(w, "writes", []) or []:
                static_seen.append(getattr(entry, "static", "ABSENT"))
        writes_known[n] = static_seen
    write_set_is_static = all(
        all(s is not None and s != [] for s in v) and v
        for v in writes_known.values()
    )
    return {
        "name": name, "source": source, "schema": schema,
        "edges": edges, "nodes": nodes, "reads": reads,
        "reducer_channels": sorted(reducer),
        "write_set_is_static": write_set_is_static,
        "write_static_entries": {k: [str(s) for s in v] for k, v in writes_known.items()},
        "agents": agents or {n: n for n in nodes},
    }


# --------------------------------------------------------------------------
# scoring
# --------------------------------------------------------------------------
def layers(edges, nodes):
    """Longest-path depth from START; equal depth means one superstep."""
    succ, indeg = {}, {n: 0 for n in nodes}
    alln = set(nodes) | {START, END}
    for a, b in edges:
        succ.setdefault(a, []).append(b)
        indeg[b] = indeg.get(b, 0) + 1
        indeg.setdefault(a, indeg.get(a, 0))
    depth = {n: 0 for n in alln}
    order, q = [], [n for n in alln if indeg.get(n, 0) == 0]
    seen = set(q)
    while q:
        n = q.pop(0)
        order.append(n)
        for m in succ.get(n, []):
            depth[m] = max(depth.get(m, 0), depth[n] + 1)
            if m not in seen:
                seen.add(m)
                q.append(m)
    base = {n: depth[n] for n in nodes}
    if base:
        lo = min(base.values())
        base = {n: v - lo for n, v in base.items()}
    return base


def susceptible(g, reads, writes):
    """Structural relaxation of Definition 1: same layer, distinct agents,
    reader's read set meets writer's write set."""
    lay = layers(g["edges"], g["nodes"])
    by = {}
    for n, l in lay.items():
        by.setdefault(l, []).append(n)
    hits = []
    for l, ns in by.items():
        for r in ns:
            for w in ns:
                if r == w or g["agents"].get(r, r) == g["agents"].get(w, w):
                    continue
                for c in sorted(reads.get(r, set()) & writes.get(w, set())):
                    hits.append({"layer": l, "reader": r, "writer": w, "cell": c})
    return hits


def lastvalue_shared(g, writes):
    """The rule that IS derivable from the object: two co-layer nodes write a
    channel that overwrites rather than merges."""
    lay = layers(g["edges"], g["nodes"])
    by = {}
    for n, l in lay.items():
        by.setdefault(l, []).append(n)
    red = set(g["reducer_channels"])
    hits = []
    for l, ns in by.items():
        for i, a in enumerate(ns):
            for b in ns[i + 1:]:
                if g["agents"].get(a, a) == g["agents"].get(b, b):
                    continue
                for c in sorted((writes.get(a, set()) & writes.get(b, set())) - red):
                    hits.append({"layer": l, "a": a, "b": b, "cell": c})
    return hits


# --------------------------------------------------------------------------
# demonstration corpus: the discriminating pair from the appendix, built as
# real LangGraph graphs rather than typed in as channel sets
# --------------------------------------------------------------------------
_STATE_CLASSES_BUILT = {}


def _state_classes():
    """State schemas must live at module scope: LangGraph resolves them with
    typing.get_type_hints, which cannot see a class defined inside a function."""
    if _STATE_CLASSES_BUILT:
        return _STATE_CLASSES_BUILT
    import operator
    from typing import Annotated, TypedDict
    ns = {"operator": operator, "Annotated": Annotated, "list": list, "str": str}
    src = (
        "from typing import Annotated, TypedDict\n"
        "import operator\n"
        "class RS(TypedDict):\n"
        "    plan: str\n"
        "    acc: Annotated[list, operator.add]\n"
        "    summary: str\n"
        "class AS(TypedDict):\n"
        "    plan: str\n"
        "    accumulator: str\n"
        "    summary: str\n"
        "class DS(TypedDict):\n"
        "    plan: str\n"
        "    out_a: str\n"
        "    out_b: str\n"
        "    summary: str\n"
        "class SS(TypedDict):\n"
        "    plan: str\n"
        "    result: str\n"
    )
    mod = {"__name__": "lgx_states"}
    exec(compile(src, "<lgx_states>", "exec"), mod)
    import sys as _s
    import types as _t
    m = _t.ModuleType("lgx_states")
    for k, v in mod.items():
        setattr(m, k, v)
    _s.modules["lgx_states"] = m
    for k in ("RS", "AS", "DS", "SS"):
        _STATE_CLASSES_BUILT[k] = getattr(m, k)
    return _STATE_CLASSES_BUILT


def corpus():
    from langgraph.graph import StateGraph, START as S, END as E
    C = _state_classes()
    RS, AS, DS, SS = C["RS"], C["AS"], C["DS"], C["SS"]

    built = []

    def add(name, state_cls, nodes, edges, declared_writes, init,
            agents=None, note=""):
        g = StateGraph(state_cls)
        for n, fn in nodes.items():
            g.add_node(n, fn)
        for a, b in edges:
            g.add_edge(a, b)
        app = g.compile()
        rec = extract(g, app, name, agents=agents)
        rec["declared_writes"] = {k: set(v) for k, v in declared_writes.items()}
        rec["note"] = note
        rec["spec"] = {"name": name, "state": state_cls, "fns": nodes,
                       "edges": edges, "init": init}
        built.append(rec)


    add("map_reduce_reducer_channel", RS,
        {"plan": lambda s: {"plan": "p"},
         "worker_a": lambda s: {"acc": ["a"]},
         "worker_b": lambda s: {"acc": ["b"]},
         "reducer": lambda s: {"summary": "s"}},
        [(S, "plan"), ("plan", "worker_a"), ("plan", "worker_b"),
         ("worker_a", "reducer"), ("worker_b", "reducer"), ("reducer", E)],
        {"plan": ["plan"], "worker_a": ["acc"], "worker_b": ["acc"],
         "reducer": ["summary"]},
        {"plan": "", "acc": [], "summary": ""},
        note="the appendix's immune half of the discriminating pair")


    add("map_reduce_no_reducer_accumulator", AS,
        {"plan": lambda s: {"plan": "p"},
         "worker_a": lambda s: {"accumulator": s.get("accumulator", "") + "a"},
         "worker_b": lambda s: {"accumulator": s.get("accumulator", "") + "b"},
         "reducer": lambda s: {"summary": "s"}},
        [(S, "plan"), ("plan", "worker_a"), ("plan", "worker_b"),
         ("worker_a", "reducer"), ("worker_b", "reducer"), ("reducer", E)],
        {"plan": ["plan"], "worker_a": ["accumulator"],
         "worker_b": ["accumulator"], "reducer": ["summary"]},
        {"plan": "", "accumulator": "", "summary": ""},
        note="the appendix's susceptible half; same workload, no reducer")


    add("supervisor_fanout_disjoint", DS,
        {"supervisor": lambda s: {"plan": "p"},
         "worker_a": lambda s: {"out_a": "a"},
         "worker_b": lambda s: {"out_b": "b"},
         "join": lambda s: {"summary": "s"}},
        [(S, "supervisor"), ("supervisor", "worker_a"), ("supervisor", "worker_b"),
         ("worker_a", "join"), ("worker_b", "join"), ("join", E)],
        {"supervisor": ["plan"], "worker_a": ["out_a"], "worker_b": ["out_b"],
         "join": ["summary"]},
        {"plan": "", "out_a": "", "out_b": "", "summary": ""},
        note="immune by disjoint result channels")


    add("sequential_pipeline", SS,
        {"a": lambda s: {"plan": "p"}, "b": lambda s: {"result": "r"}},
        [(S, "a"), ("a", "b"), ("b", E)],
        {"a": ["plan"], "b": ["result"]},
        {"plan": "", "result": ""},
        note="negative control: no two nodes share a layer")

    return built


def execute_and_observe(g_spec):
    """Run the graph with instrument_layered and return (runnable, observed
    write sets, error).

    This closes the gap the precision matrix leaves open. The write set is the
    input static extraction cannot supply, and it is exactly what one
    instrumented execution observes: a node's update dict IS its write set.
    """
    import tempfile, os as _os
    from langgraph.graph import StateGraph
    from langgraph.errors import InvalidUpdateError
    from prevalence_harness import SessionRecorder, instrument_layered

    d = tempfile.mkdtemp()
    rec = SessionRecorder(_os.path.join(d, "s.jsonl"), framework="langgraph",
                          model="stub", scenario=g_spec["name"]).open()
    try:
        wrapped = instrument_layered(rec, g_spec["fns"], g_spec["edges"])
        g = StateGraph(g_spec["state"])
        for n, f in wrapped.items():
            g.add_node(n, f)
        for a, b in g_spec["edges"]:
            g.add_edge(a, b)
        g.compile().invoke(g_spec["init"])
        runnable, err = True, None
    except InvalidUpdateError as e:
        runnable, err = False, str(e).splitlines()[0]
    except Exception as e:  # noqa: BLE001
        runnable, err = False, f"{type(e).__name__}: {e}"
    finally:
        rec.close()

    observed = {}
    for r in rec.records:
        observed.setdefault(r.agent_id, set()).update(r.write_set)
    return runnable, observed, err


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    a = ap.parse_args()

    try:
        gs = corpus()
    except ImportError as e:
        print(f"langgraph not importable: {e}", file=sys.stderr)
        return 2

    print(f"  langgraph write sets statically available: "
          f"{any(g['write_set_is_static'] for g in gs)}")
    ex = gs[0]
    print(f"  e.g. {ex['name']}: ChannelWrite static entries -> "
          f"{sorted({s for v in ex['write_static_entries'].values() for s in v})}")
    print()
    print("  precision matrix: R=reads W=writes, d=declared by the author, "
          "e=extracted from the object")
    hdr = (f"  {'topology':36s} {'RdWd':>9s} {'RdWe':>9s} {'ReWd':>9s} {'ReWe':>9s} "
           f"{'lv/declared':>11s} {'lv/extracted':>12s} {'langgraph':>9s} "
           f"{'observed':>8s}  reducer channels")
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))

    rows = []
    for g in gs:
        schema_all = {n: set(g["schema"]) for n in g["nodes"]}
        dr = {n: set(r) for n, r in _declared_reads(g).items()}
        dw = g["declared_writes"]
        er, ew = g["reads"], schema_all
        cells = {
            "RdWd": bool(susceptible(g, dr, dw)),   # both declared  (the appendix)
            "RdWe": bool(susceptible(g, dr, ew)),   # reads precise, writes not
            "ReWd": bool(susceptible(g, er, dw)),   # writes precise, reads not
            "ReWe": bool(susceptible(g, er, ew)),   # neither (what extraction gives)
        }
        lv = {"declared": bool(lastvalue_shared(g, dw)),
              "extracted": bool(lastvalue_shared(g, ew))}
        rows.append({"name": g["name"], "precision_matrix": cells,
                     "lastvalue_rule": lv,
                     "reducer_channels": g["reducer_channels"],
                     "schema": g["schema"], "note": g["note"]})
        runnable, observed, err = execute_and_observe(g["spec"])
        obs_exact = (runnable and
                     {k: set(v) for k, v in observed.items()} ==
                     {k: set(v) for k, v in g["declared_writes"].items()})
        rows[-1].update({"runnable": runnable, "run_error": err,
                         "observed_writes": {k: sorted(v) for k, v in observed.items()},
                         "observed_matches_declared": obs_exact})
        f = lambda b: "SUSC" if b else "immune"
        print(f"  {g['name']:36s} {f(cells['RdWd']):>9s} {f(cells['RdWe']):>9s} "
              f"{f(cells['ReWd']):>9s} {f(cells['ReWe']):>9s} "
              f"{f(lv['declared']):>11s} {f(lv['extracted']):>12s} "
              f"{('runs' if runnable else 'REFUSED'):>9s} "
              f"{('exact' if obs_exact else ('-' if not runnable else 'differs')):>8s}"
              f"  {g['reducer_channels']}")

    n = len(rows)
    print()
    for k, lab in (("RdWd", "reads declared, writes declared (the appendix)"),
                   ("RdWe", "reads declared, writes extracted"),
                   ("ReWd", "reads extracted, writes declared"),
                   ("ReWe", "reads extracted, writes extracted (a real front end)")):
        print(f"  {lab:52s} {sum(r['precision_matrix'][k] for r in rows)} of {n} susceptible")
    print(f"  {'last-value rule, declared writes':52s} "
          f"{sum(r['lastvalue_rule']['declared'] for r in rows)} of {n}")
    print(f"  {'last-value rule, extracted writes':52s} "
          f"{sum(r['lastvalue_rule']['extracted'] for r in rows)} of {n}")
    print()
    print("  RdWd is the appendix's encoding. Losing precision on EITHER side collapses")
    print("  the distinction, so both are load-bearing. LangGraph 1.2 supplies neither by")
    print("  default, but the two are not alike: a per-node input_schema on add_node DOES")
    print("  narrow the read set (verified: a node so annotated reports only its declared")
    print("  channels), while there is no per-node output schema and ChannelWrite carries")
    print("  static=None, so the write set is not recoverable at any annotation effort.")
    print("  The reducer bit is the one discriminating fact the object exposes; the")
    print("  last-value columns show it rescues the split only when write sets are")
    print("  already known, so it is not an escape from the same missing input.")
    print()
    nr = [r for r in rows if not r["runnable"]]
    ok = [r for r in rows if r.get("observed_matches_declared")]
    print(f"  langgraph column: {len(rows)-len(nr)} of {len(rows)} topologies actually EXECUTE.")
    for r in nr:
        print(f"    REFUSED {r['name']}: {r['run_error']}")
    print(f"  observed column: one instrumented run recovers the write set exactly in")
    print(f"    {len(ok)} of the {len(rows)-len(nr)} runnable topologies. The write set is the")
    print("    input static extraction cannot supply and dynamic observation can: a")
    print("    node's update dict IS its write set. That is the method the corpus")
    print("    study needs, and why prevalence_corpus.py wraps nodes rather than")
    print("    reading the compiled object.")

    if a.json:
        with open(a.json, "w") as fh:
            json.dump({"rows": rows,
                       "write_set_statically_available": False}, fh, indent=2)
        print(f"\n  wrote {a.json}")
    return 0


def _declared_reads(g):
    """The appendix's per-node read sets for the demonstration corpus: a node
    reads the channels its body actually consults. Kept alongside the extracted
    read sets so the two precisions can be compared on the same graphs."""
    name = g["name"]
    table = {
        "map_reduce_reducer_channel": {
            "plan": ["plan"], "worker_a": ["plan"], "worker_b": ["plan"],
            "reducer": ["acc"]},
        "map_reduce_no_reducer_accumulator": {
            "plan": ["plan"], "worker_a": ["plan", "accumulator"],
            "worker_b": ["plan", "accumulator"], "reducer": ["accumulator"]},
        "supervisor_fanout_disjoint": {
            "supervisor": ["plan"], "worker_a": ["plan"], "worker_b": ["plan"],
            "join": ["out_a", "out_b"]},
        "sequential_pipeline": {"a": ["plan"], "b": ["plan"]},
    }
    return {k: set(v) for k, v in table[name].items()}


if __name__ == "__main__":
    sys.exit(main())
