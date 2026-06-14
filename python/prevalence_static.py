#!/usr/bin/env python3
"""
prevalence_static.py

STATIC structural susceptibility analysis for cross-agent A_1
(stale generation) over a corpus of multi-agent graph TOPOLOGIES.

WHY STATIC (and how it relates to the dynamic harness)
  prevalence_harness.a1_firings fires only when, at runtime, an op reads a
  cell value v in a superstep while a different agent in the SAME superstep
  commits v' != v. The first half -- same superstep, cross-agent, one agent
  READS a cell another WRITES -- is purely TOPOLOGICAL: it depends on the
  graph's layers and per-node read/write channels, not on any model output.
  Dropping the value-inequality and keeping the topological condition yields a
  SOUND OVER-APPROXIMATION:

        structural susceptibility  >=  dynamic A_1 prevalence

  an UPPER BOUND. A topology found NOT susceptible CANNOT exhibit cross-agent
  A_1 at runtime for any model on any input. A topology found susceptible MAY
  exhibit it (runtime values decide). This is the honest companion to the
  dynamic 0/600 lower bound: together they bracket and CHARACTERISE which
  structures admit A_1.

DETECTOR ALIGNMENT
  The predicate is lib_l2_safety.rs::a1_witness with the value comparison
  existentially relaxed: same superstep (== topological layer, via
  prevalence_harness.compute_layers), distinct agents, read_set(reader)
  intersect write_set(writer) nonempty. Nothing looser.

THE CORPUS
  Canonical, publicly documented topologies (LangGraph architecture/workflow
  docs, CrewAI process modes, the classic blackboard architecture). Each
  carries a checkable `source` and explicit read/write channel sets, encoded
  CONSERVATIVELY (a channel goes in read_set if the node might read it ->
  biased TOWARD flagging). The safe/susceptible split is produced by ONE
  uniform rule -- concurrent agents sharing a mutable cell -- not per-graph
  curation; map_reduce_reducer_channel vs map_reduce_no_reducer_accumulator
  (same workload, opposite verdicts) demonstrates the rule drives the outcome.
  Report as "N canonical documented topologies", not a production sample; add
  your own with add_topology().

CONDITIONAL ROUTING CAVEAT
  compute_layers uses STATIC edges; conditional routers run one branch per
  step at runtime but appear same-layer statically. The analysis therefore
  OVER-approximates concurrency there (flagged routing="conditional"), which
  only inflates susceptibility and preserves the upper bound.

USAGE
  python prevalence_static.py
  python prevalence_static.py --json out.json
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass, field

from prevalence_harness import compute_layers

START = "__start__"
END = "__end__"


@dataclass
class Topology:
    name: str
    edges: list[tuple[str, str]]
    reads: dict[str, set]
    writes: dict[str, set]
    source: str
    routing: str = "static"
    agents: dict[str, str] = field(default_factory=dict)
    note: str = ""
    is_control: bool = False

    def agent_of(self, node: str) -> str:
        return self.agents.get(node, node)


_CORPUS: list[Topology] = []


def add_topology(t: Topology) -> None:
    _CORPUS.append(t)


def susceptibilities(t: Topology) -> list[dict]:
    """Every structurally susceptible (superstep, reader, writer, cell): a
    same-layer, cross-agent pair where reader's read_set meets writer's
    write_set. Sound over-approximation of a1_firings."""
    layers = compute_layers(t.edges, START, END)
    by_layer: dict[int, list[str]] = {}
    for node, lyr in layers.items():
        by_layer.setdefault(lyr, []).append(node)
    out = []
    for lyr, nodes in by_layer.items():
        for reader in nodes:
            for writer in nodes:
                if reader == writer:
                    continue
                if t.agent_of(reader) == t.agent_of(writer):
                    continue
                shared = t.reads.get(reader, set()) & t.writes.get(writer, set())
                for cell in sorted(shared):
                    out.append({
                        "superstep": lyr,
                        "reader": reader, "reader_agent": t.agent_of(reader),
                        "writer": writer, "writer_agent": t.agent_of(writer),
                        "cell": cell,
                    })
    return out


def _build_corpus() -> None:
    add_topology(Topology(
        name="sequential_pipeline",
        edges=[(START, "plan"), ("plan", "exec"), ("exec", "summarise"),
               ("summarise", END)],
        reads={"plan": {"task"}, "exec": {"plan"}, "summarise": {"result"}},
        writes={"plan": {"plan"}, "exec": {"result"}, "summarise": {"summary"}},
        source="LangGraph prompt-chaining workflow.",
        is_control=True,
        note="Distinct layers => SAFE (negative control).",
    ))
    add_topology(Topology(
        name="racy_shared_cell",
        edges=[(START, "producer"), (START, "consumer"),
               ("producer", END), ("consumer", END)],
        reads={"producer": {"task"}, "consumer": {"plan"}},
        writes={"producer": {"plan"}, "consumer": {"answer"}},
        source="Constructed positive control.",
        is_control=True,
        note="consumer reads `plan` while producer writes it same superstep => "
             "SUSCEPTIBLE (positive control).",
    ))

    add_topology(Topology(
        name="supervisor_fanout_disjoint",
        edges=[(START, "supervisor"), ("supervisor", "worker_a"),
               ("supervisor", "worker_b"), ("worker_a", "reducer"),
               ("worker_b", "reducer"), ("reducer", END)],
        reads={"supervisor": {"task"}, "worker_a": {"plan"},
               "worker_b": {"plan"}, "reducer": {"out_a", "out_b"}},
        writes={"supervisor": {"plan"}, "worker_a": {"out_a"},
                "worker_b": {"out_b"}, "reducer": {"summary"}},
        source="LangGraph supervisor, parallel workers writing disjoint channels.",
        note="Workers read `plan`, write DISJOINT channels => SAFE.",
    ))
    add_topology(Topology(
        name="map_reduce_reducer_channel",
        edges=[(START, "mapper"), ("mapper", "w0"), ("mapper", "w1"),
               ("mapper", "w2"), ("w0", "aggregate"), ("w1", "aggregate"),
               ("w2", "aggregate"), ("aggregate", END)],
        reads={"mapper": {"items"}, "w0": {"items"}, "w1": {"items"},
               "w2": {"items"}, "aggregate": {"results"}},
        writes={"mapper": {"items"}, "w0": {"results"}, "w1": {"results"},
                "w2": {"results"}, "aggregate": {"final"}},
        source="LangGraph map-reduce, Send + Annotated[list, operator.add].",
        note="Workers append `results` via ADDITIVE reducer; none read it "
             "in-layer => SAFE.",
    ))
    add_topology(Topology(
        name="orchestrator_workers_send",
        edges=[(START, "orchestrator"), ("orchestrator", "sec0"),
               ("orchestrator", "sec1"), ("sec0", "synthesizer"),
               ("sec1", "synthesizer"), ("synthesizer", END)],
        reads={"orchestrator": {"report_topic"}, "sec0": {"section_spec"},
               "sec1": {"section_spec"}, "synthesizer": {"completed_sections"}},
        writes={"orchestrator": {"section_spec"}, "sec0": {"completed_sections"},
                "sec1": {"completed_sections"}, "synthesizer": {"final_report"}},
        source="LangGraph orchestrator-worker report generator.",
        note="Section workers append via reducer, do not read it in-layer => SAFE.",
    ))
    add_topology(Topology(
        name="parallel_tool_calls_reducer",
        edges=[(START, "agent"), ("agent", "tool0"), ("agent", "tool1"),
               ("tool0", "merge"), ("tool1", "merge"), ("merge", END)],
        reads={"agent": {"query"}, "tool0": {"query"}, "tool1": {"query"},
               "merge": {"tool_results"}},
        writes={"agent": {"query"}, "tool0": {"tool_results"},
                "tool1": {"tool_results"}, "merge": {"answer"}},
        agents={"tool0": "agent", "tool1": "agent", "merge": "agent",
                "agent": "agent"},
        source="LangGraph parallel tool execution, single agent.",
        note="Single agent => cross-agent predicate vacuous; reducer append => SAFE.",
    ))
    add_topology(Topology(
        name="router_single_dispatch",
        edges=[(START, "router"), ("router", "billing"), ("router", "tech"),
               ("router", "general"), ("billing", END), ("tech", END),
               ("general", END)],
        reads={"router": {"query"}, "billing": {"query"}, "tech": {"query"},
               "general": {"query"}},
        writes={"router": {"route"}, "billing": {"reply"}, "tech": {"reply"},
                "general": {"reply"}},
        source="LangGraph routing workflow; one handler per request.",
        routing="conditional",
        note="Handlers read `query` only and write `reply` without reading it => "
             "no overlap => SAFE even under conservative same-layer treatment.",
    ))
    add_topology(Topology(
        name="reflection_generator_critic",
        edges=[(START, "generate"), ("generate", "reflect"),
               ("reflect", "generate"), ("reflect", END)],
        reads={"generate": {"draft", "critique"}, "reflect": {"draft"}},
        writes={"generate": {"draft"}, "reflect": {"critique"}},
        source="LangGraph reflection / Reflexion.",
        routing="conditional",
        note="Generator/critic alternate across supersteps => SAFE.",
    ))
    add_topology(Topology(
        name="evaluator_optimizer",
        edges=[(START, "optimizer"), ("optimizer", "evaluator"),
               ("evaluator", "optimizer"), ("evaluator", END)],
        reads={"optimizer": {"task", "feedback"}, "evaluator": {"solution"}},
        writes={"optimizer": {"solution"}, "evaluator": {"feedback", "grade"}},
        source="LangGraph evaluator-optimizer workflow.",
        routing="conditional",
        note="Alternating supersteps => SAFE.",
    ))
    add_topology(Topology(
        name="plan_and_execute",
        edges=[(START, "planner"), ("planner", "executor"),
               ("executor", "replan"), ("replan", "executor"), ("replan", END)],
        reads={"planner": {"input"}, "executor": {"plan", "past_steps"},
               "replan": {"plan", "past_steps"}},
        writes={"planner": {"plan"}, "executor": {"past_steps"},
                "replan": {"plan"}},
        source="LangGraph plan-and-execute.",
        routing="conditional",
        note="Strictly sequential loop => SAFE.",
    ))
    add_topology(Topology(
        name="sequential_shared_context",
        edges=[(START, "a1"), ("a1", "a2"), ("a2", "a3"), ("a3", END)],
        reads={"a1": {"context"}, "a2": {"context"}, "a3": {"context"}},
        writes={"a1": {"context"}, "a2": {"context"}, "a3": {"context"}},
        source="CrewAI sequential process; shared scratchpad passed agent-to-agent.",
        note="Agents SHARE `context` read-write but in DISTINCT layers => SAFE. "
             "Sharing alone is not the hazard; CONCURRENT sharing is.",
    ))
    add_topology(Topology(
        name="memory_chatbot",
        edges=[(START, "retrieve"), ("retrieve", "respond"),
               ("respond", "writeback"), ("writeback", END)],
        reads={"retrieve": {"memory", "query"}, "respond": {"context", "query"},
               "writeback": {"response"}},
        writes={"retrieve": {"context"}, "respond": {"response"},
                "writeback": {"memory"}},
        agents={"retrieve": "bot", "respond": "bot", "writeback": "bot"},
        source="LangGraph long-term-memory chatbot.",
        note="Single agent, sequential memory read/write => SAFE.",
    ))

    add_topology(Topology(
        name="hierarchical_teams",
        edges=[(START, "top"), ("top", "team1_lead"), ("top", "team2_lead"),
               ("team1_lead", "join"), ("team2_lead", "join"), ("join", END)],
        reads={"top": {"task"}, "team1_lead": {"task", "shared_scratch"},
               "team2_lead": {"task", "shared_scratch"},
               "join": {"team1_out", "team2_out"}},
        writes={"top": {"task"}, "team1_lead": {"team1_out", "shared_scratch"},
                "team2_lead": {"team2_out", "shared_scratch"},
                "join": {"final"}},
        source="LangGraph hierarchical agent teams, modelled with a shared "
               "scratchpad channel.",
        note="Both leads read AND write `shared_scratch` in one layer => "
             "SUSCEPTIBLE.",
    ))
    add_topology(Topology(
        name="collaboration_shared_messages",
        edges=[(START, "agent_x"), (START, "agent_y"),
               ("agent_x", "route"), ("agent_y", "route"), ("route", END)],
        reads={"agent_x": {"messages"}, "agent_y": {"messages"},
               "route": {"messages"}},
        writes={"agent_x": {"messages"}, "agent_y": {"messages"},
                "route": {"next"}},
        routing="conditional",
        source="LangGraph multi-agent collaboration, shared `messages`.",
        note="Two agents concurrently read/write `messages` => SUSCEPTIBLE; "
             "one-agent-per-turn routing lowers the dynamic rate.",
    ))
    add_topology(Topology(
        name="network_swarm",
        edges=[(START, "alice"), (START, "bob"), ("alice", "handoff"),
               ("bob", "handoff"), ("handoff", END)],
        reads={"alice": {"messages", "active_agent"},
               "bob": {"messages", "active_agent"}, "handoff": {"messages"}},
        writes={"alice": {"messages", "active_agent"},
                "bob": {"messages", "active_agent"}, "handoff": {"result"}},
        routing="conditional",
        source="LangGraph swarm / network multi-agent, shared `messages` + "
               "`active_agent`.",
        note="Peers share `messages`/`active_agent` read-write => SUSCEPTIBLE; "
             "handoff routing lowers the dynamic rate.",
    ))
    add_topology(Topology(
        name="blackboard_multiwriter",
        edges=[(START, "ks1"), (START, "ks2"), (START, "ks3"),
               ("ks1", "control"), ("ks2", "control"), ("ks3", "control"),
               ("control", END)],
        reads={"ks1": {"blackboard"}, "ks2": {"blackboard"},
               "ks3": {"blackboard"}, "control": {"blackboard"}},
        writes={"ks1": {"blackboard"}, "ks2": {"blackboard"},
                "ks3": {"blackboard"}, "control": {"decision"}},
        source="Classic blackboard architecture (Hayes-Roth 1985).",
        note="All knowledge sources read AND write the shared `blackboard` "
             "concurrently => SUSCEPTIBLE.",
    ))
    add_topology(Topology(
        name="competing_agents_consensus",
        edges=[(START, "proposer_a"), (START, "proposer_b"),
               ("proposer_a", "decide"), ("proposer_b", "decide"),
               ("decide", END)],
        reads={"proposer_a": {"proposals"}, "proposer_b": {"proposals"},
               "decide": {"proposals"}},
        writes={"proposer_a": {"proposals"}, "proposer_b": {"proposals"},
                "decide": {"decision"}},
        source="Multi-agent debate / consensus round (Du et al. 2023).",
        note="Proposers read shared `proposals` while concurrently writing it "
             "=> SUSCEPTIBLE.",
    ))
    add_topology(Topology(
        name="map_reduce_no_reducer_accumulator",
        edges=[(START, "split"), ("split", "m0"), ("split", "m1"),
               ("split", "m2"), ("m0", "done"), ("m1", "done"),
               ("m2", "done"), ("done", END)],
        reads={"split": {"items"}, "m0": {"accumulator"}, "m1": {"accumulator"},
               "m2": {"accumulator"}, "done": {"accumulator"}},
        writes={"split": {"items"}, "m0": {"accumulator"},
                "m1": {"accumulator"}, "m2": {"accumulator"},
                "done": {"final"}},
        source="Map-reduce WITHOUT a reducer: read-modify-write a shared "
               "`accumulator` (lost-update antipattern).",
        note="Same workload as map_reduce_reducer_channel but workers read AND "
             "write a shared `accumulator` => SUSCEPTIBLE. The reducer, not the "
             "workload, is what makes the reducer variant safe.",
    ))


def run(as_json: str | None) -> dict:
    _build_corpus()
    rows = [(t, susceptibilities(t)) for t in _CORPUS]
    canonical = [(t, s) for (t, s) in rows if not t.is_control]
    controls = [(t, s) for (t, s) in rows if t.is_control]
    k = sum(1 for (t, s) in canonical if s)
    n = len(canonical)

    print(f"{'topology':34}{'routing':12}{'susceptible':>12}{'#pairs':>8}  cells")
    print("-" * 92)
    for (t, s) in canonical:
        cells = sorted({d["cell"] for d in s})
        print(f"{t.name:34}{t.routing:12}"
              f"{('YES' if s else 'no'):>12}{len(s):>8}  {','.join(cells)}")
    print("-" * 92)
    for (t, s) in controls:
        tag = "CTRL+" if "racy" in t.name else "CTRL-"
        ok = (bool(s) == ("racy" in t.name))
        cells = sorted({d["cell"] for d in s})
        status = "[OK]" if ok else "[FAILED]"
        print(f"{t.name:28}{tag:6}{t.routing:12}"
              f"{('YES' if s else 'no'):>12}{len(s):>8}  {status} {','.join(cells)}")

    print()
    print("Structural A_1 susceptibility (UPPER BOUND on dynamic prevalence):")
    print(f"  {k} of {n} canonical documented topologies are structurally "
          f"susceptible to cross-agent A_1.")
    susceptible_names = [t.name for (t, s) in canonical if s]
    print(f"  Susceptible: {', '.join(susceptible_names)}")
    print("  All and only the topologies in which concurrent agents share a "
          "mutable cell within a superstep.")
    cflag = all((bool(s) == ("racy" in t.name)) for (t, s) in controls)
    print(f"  Controls: {'PASS' if cflag else 'FAIL'} (positive fires, negative silent).")

    report = {
        "k_susceptible": k, "n_canonical": n,
        "susceptible_names": susceptible_names, "controls_pass": cflag,
        "topologies": [
            {"name": t.name, "routing": t.routing, "is_control": t.is_control,
             "source": t.source, "note": t.note,
             "susceptible": bool(s), "pairs": s}
            for (t, s) in rows
        ],
    }
    if as_json:
        json.dump(report, open(as_json, "w"), indent=2)
        print(f"\nwrote {as_json}")
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    run(args.json)


if __name__ == "__main__":
    main()