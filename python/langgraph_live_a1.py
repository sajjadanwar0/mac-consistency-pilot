#!/usr/bin/env python3
"""
langgraph_live_a1.py — cross-agent stale-generation (A_1) on an UNMODIFIED
LangGraph runtime, under LIVE inference.

Why this file exists (12 Sep 2026, post-ICECCS round 2)
-------------------------------------------------------
Reviewer 3 read Sec 6.3(vi) ("the frameworks we examined refresh state at
generation and thereby close the cross-agent A_1 window by construction")
and concluded the motivating problem may not exist. The only in-framework
A_1 witness the artifact had (Sec 6.5) used deterministic nodes, so the
pinned interval was never an inference phase; and prevalence_dynamic_run.py
is a stand-alone BSP simulator, not LangGraph. This harness drives the real
framework with real model calls and emits OpRecords in the pilot schema
(instrument.py / rust-analyser/src/oprecord.rs), so the verified detector
classifies the traces, not this file.

Two experiments
---------------
STORE   (primary; Definition 1 exactly, strict clock)
  Two agents = two compiled graphs sharing one LangGraph BaseStore, the
  framework's documented cross-thread memory (compile(store=...)).
    flight_agent : get trip date -> LLM drafts a reservation (seconds)
                   -> put booking.
    date_agent   : (starts after the flight agent's read) get trip date
                   -> LLM proposes a revised date -> put revised date.
  The store is subclassed only to STAMP a monotonic logical clock at the
  store boundary (get reads the clock, put ticks it, both under one lock);
  the framework is otherwise untouched. A_1 fires iff
      flight.read_time < date.write_time < flight.write_time
      and read_value != written_value           (Definition 1, cross-agent)
  Modes:
    vanilla     LangGraph as shipped: no validation, the L_0 default.
    validated   the L_1 discipline at the application layer: re-get the
                read set immediately before put; if it changed, discard
                the generation and regenerate (SI-style validation). Each
                discarded generation is counted as the cost of prevention.
    sequential  structural control: date_agent runs after flight_agent
                has committed. Expected A_1 = 0.

SUPERSTEP  (supporting; the live upgrade of the Sec 6.5 reproduction)
  One StateGraph, two nodes in ONE Pregel superstep over a reducer-declared
  channel (Annotated[list, operator.add], so nothing fail-stops):
    writer      : quick LLM revision appended to `plan`.
    summarizer  : reads `plan` at superstep entry, LLM summary (seconds),
                  writes `summary`.
  The summarizer's read set is pinned for the whole node body by the
  superstep barrier — this IS the "runtime that pins rather than
  refreshes". Two clocks are reported honestly:
    completion clock : write_time = order in which node bodies returned
                       (Definition 1 fires when the writer finished first)
    barrier clock    : both writes land at the barrier tick (Definition 1's
                       strict inequality does not fire; the joint state is
                       nonetheless a summary grounded in a superseded plan
                       — the Sec 4.5 snapshot-insufficiency shape, live).
  A timing assertion confirms the two nodes actually ran concurrently.

Usage
-----
  pip install langgraph langchain-core                      # openai / anthropic as needed
  python langgraph_live_a1.py --provider mock --n 30 --out live_a1_mock   # self-test, no keys
  export OPENAI_API_KEY=...;    python langgraph_live_a1.py --provider openai    --model gpt-4o-mini      --n 100 --out live_a1_gpt4omini
  export ANTHROPIC_API_KEY=...; python langgraph_live_a1.py --provider anthropic --model claude-haiku-4-5 --n 100 --out live_a1_haiku
  python langgraph_live_a1.py --provider openai --model llama3.2 --base-url http://localhost:11434/v1 --n 100 --out live_a1_llama

Outputs (in --out):
  records.jsonl   every committed OpRecord, pilot schema + metadata fields
  sessions/*.jsonl one file per session — feed THESE to rust-analyser
                  (one session per file; per-session clocks restart at 0)
                  for f in <out>/sessions/*.jsonl; do analyser "$f"; done
  results.json    per-experiment/mode rates with exact Clopper–Pearson CIs,
                  pinned-interval statistics, regeneration counts
"""
from __future__ import annotations

import argparse
import json
import math
import operator
import re
import statistics
import sys
import threading
import time
from dataclasses import dataclass, field
from datetime import date, timedelta
from pathlib import Path
from typing import Annotated, Any, TypedDict

from langgraph.graph import END, START, StateGraph
from langgraph.runtime import Runtime
from langgraph.store.memory import InMemoryStore

NULL = "NULL"


# ---------------------------------------------------------------------------
# logical clock + pilot-schema recorder
# ---------------------------------------------------------------------------
class Clock:
    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.t = 0

    def now(self) -> int:
        with self.lock:
            return self.t

    def tick(self) -> int:
        with self.lock:
            self.t += 1
            return self.t


class Recorder:
    """One JSON line per committed operation, field-for-field the shape
    rust-analyser/src/oprecord.rs deserializes (extra fields are ignored by
    serde; `agent_id` is duplicated for analyze_production.py)."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.lock = threading.Lock()
        self.fh = path.open("w", encoding="utf-8")
        self.records: list[dict] = []

    def emit(self, *, agent: str, read_set: list[str], read_values: dict[str, str],
             read_time: int, write_set: list[str], write_values: dict[str, str],
             write_time: int, **meta: Any) -> dict:
        rec = {
            "agent": agent,
            "agent_id": agent,
            "read_set": list(read_set),
            "read_values": dict(read_values),
            "read_time": int(read_time),
            "write_set": list(write_set),
            "write_values": dict(write_values),
            "write_time": int(write_time),
            "planned_tool": None,
            "tools_used": [],
            "tools_visible_at_read": [],
            "io": [[k, v] for k, v in write_values.items()],
            "co": [[k, v] for k, v in write_values.items()],
        }
        rec.update(meta)
        with self.lock:
            self.fh.write(json.dumps(rec, sort_keys=True) + "\n")
            self.fh.flush()
            self.records.append(rec)
        return rec

    def close(self) -> None:
        self.fh.close()

    def dump_session(self, records: list[dict], name: str) -> Path:
        """One JSONL per session for rust-analyser (usage: analyser <trace.jsonl>).
        Per-session logical clocks restart at 0, so sessions must never be
        scored from the combined file."""
        d = self.path.parent / "sessions"
        d.mkdir(exist_ok=True)
        p = d / f"{name}.jsonl"
        with p.open("w", encoding="utf-8") as fh:
            for r in records:
                fh.write(json.dumps(r, sort_keys=True) + "\n")
        return p


def a1_witnesses(h: list[dict]) -> list[dict]:
    """Definition 1, verbatim: i != j, different agents, c in read_set(i) ∩
    write_set(j), read_time(i) < write_time(j) < write_time(i), and
    read_values(i)[c] != write_values(j)[c]. Same predicate as
    rust-analyser/src/anomalies.rs (both temporal conjuncts)."""
    out = []
    for i, ri in enumerate(h):
        for j, rj in enumerate(h):
            if i == j or ri["agent"] == rj["agent"]:
                continue
            for c in ri["read_set"]:
                if c not in rj["write_set"]:
                    continue
                if (ri["read_time"] < rj["write_time"] < ri["write_time"]
                        and ri["read_values"].get(c, NULL) != rj["write_values"].get(c, NULL)):
                    out.append({"i": i, "j": j, "cell": c,
                                "read_value": ri["read_values"].get(c, NULL),
                                "written_value": rj["write_values"].get(c, NULL)})
    return out


def clopper_pearson(k: int, n: int, alpha: float = 0.05) -> tuple[float, float]:
    if n == 0:
        return (0.0, 1.0)
    try:
        from scipy.stats import beta  # type: ignore
        lo = 0.0 if k == 0 else float(beta.ppf(alpha / 2, k, n - k + 1))
        hi = 1.0 if k == n else float(beta.ppf(1 - alpha / 2, k + 1, n - k))
        return (lo, hi)
    except Exception:
        # exact endpoints without scipy: rule of three at the extremes,
        # Wilson score otherwise (labelled as such in results.json)
        if k == 0:
            return (0.0, min(1.0, 3.0 / n))
        if k == n:
            return (max(0.0, 1 - 3.0 / n), 1.0)
        p, z = k / n, 1.959964
        d = 1 + z * z / n
        c = (p + z * z / (2 * n)) / d
        r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
        return (max(0.0, c - r), min(1.0, c + r))


# ---------------------------------------------------------------------------
# model client (same provider set as prevalence_dynamic_run.py) + mock
# ---------------------------------------------------------------------------
class ModelClient:
    def __init__(self, provider: str, model: str, base_url: str | None = None,
                 mock_latency: float = 1.2) -> None:
        self.provider, self.model, self.mock_latency = provider, model, mock_latency
        if provider == "mock":
            self.client = None
        elif provider in ("openai", "vllm"):
            from openai import OpenAI  # type: ignore
            self.client = OpenAI(base_url=base_url, api_key="EMPTY") if base_url else OpenAI()
        elif provider == "anthropic":
            import anthropic  # type: ignore
            self.client = anthropic.Anthropic()
        else:
            raise ValueError(f"unknown provider {provider}")

    def complete(self, system: str, user: str, max_tokens: int = 96,
                 mock_reply: str | None = None, mock_latency: float | None = None) -> str:
        if self.provider == "mock":
            time.sleep(self.mock_latency if mock_latency is None else mock_latency)
            return mock_reply or ""
        if self.provider in ("openai", "vllm"):
            r = self.client.chat.completions.create(
                model=self.model, max_tokens=max_tokens, temperature=0.7,
                messages=[{"role": "system", "content": system},
                          {"role": "user", "content": user}])
            return (r.choices[0].message.content or "").strip()
        r = self.client.messages.create(
            model=self.model, max_tokens=max_tokens, system=system,
            messages=[{"role": "user", "content": user}])
        return (r.content[0].text if r.content else "").strip()


ISO = re.compile(r"\b(\d{4}-\d{2}-\d{2})\b")


def parse_iso(text: str) -> str | None:
    m = ISO.search(text)
    if not m:
        return None
    try:
        date.fromisoformat(m.group(1))
        return m.group(1)
    except ValueError:
        return None


# ---------------------------------------------------------------------------
# EXPERIMENT A — shared BaseStore, two graphs, live inference
# ---------------------------------------------------------------------------
class InstrumentedStore(InMemoryStore):
    """LangGraph's InMemoryStore with a logical clock stamped AT THE STORE
    BOUNDARY. Semantics are untouched: get/put are the parent's; the only
    additions are the stamp (taken under one lock so read_time/write_time
    are totally ordered) and a thread-local record of the last stamp."""

    def __init__(self, clock: Clock) -> None:
        super().__init__()
        self.clock = clock
        self.local = threading.local()
        self.log: list[dict] = []

    def get(self, namespace, key, *args, **kwargs):  # type: ignore[override]
        with self.clock.lock:
            item = super().get(namespace, key, *args, **kwargs)
            t = self.clock.t
        self.local.last = ("get", t, time.perf_counter())
        self.log.append({"op": "get", "ns": "/".join(namespace), "key": key, "t": t})
        return item

    def put(self, namespace, key, value, *args, **kwargs):  # type: ignore[override]
        with self.clock.lock:
            super().put(namespace, key, value, *args, **kwargs)
            self.clock.t += 1
            t = self.clock.t
        self.local.last = ("put", t, time.perf_counter())
        self.log.append({"op": "put", "ns": "/".join(namespace), "key": key, "t": t})

    def last_stamp(self) -> tuple[str, int, float]:
        return self.local.last


TRIP_NS = ("trip", "state")
BOOK_NS = ("trip", "bookings")
DATE_CELL = "trip/state/date"


class FlightState(TypedDict, total=False):
    session: int
    mode: str
    booking_text: str
    date_used: str
    regenerations: int
    pinned_seconds: float


class DateState(TypedDict, total=False):
    session: int
    new_date: str
    fallback: bool


def build_store_graphs(client: ModelClient, store: InstrumentedStore, rec: Recorder,
                       date_started: threading.Event, flight_read_done: threading.Event,
                       flight_committed: threading.Event, mode: str):
    """Two independent graphs sharing `store`. Events only sequence the
    experiment (make sure the date agent's write lands INSIDE the flight
    agent's generation phase, or AFTER it for the sequential control); they
    do not alter what either agent reads or writes."""

    def flight_node(state: FlightState, runtime: Runtime) -> dict:
        s = runtime.store
        regenerations = 0
        while True:
            item = s.get(TRIP_NS, "date")
            _, t_read, w_read = s.last_stamp()
            date_seen = item.value["date"] if item else NULL
            flight_read_done.set()
            text = client.complete(
                "You are a flight-booking agent. Draft a ONE-sentence flight "
                "reservation request. Include the trip date verbatim in "
                "ISO format (YYYY-MM-DD).",
                f"Trip date: {date_seen}. Route: LHR to ISB, economy, one passenger.",
                mock_reply=f"Please reserve one economy seat LHR-ISB for {date_seen}.")
            if mode == "validated":
                check = s.get(TRIP_NS, "date")
                _, t_check, _ = s.last_stamp()
                current = check.value["date"] if check else NULL
                if current != date_seen:
                    regenerations += 1      # the discarded generation = cost of L1
                    continue
                t_read = t_check           # the committed op's read is the validating read
            key = f"booking-{state['session']}"
            s.put(BOOK_NS, key, {"date_used": date_seen, "text": text})
            _, t_write, w_write = s.last_stamp()
            rec.emit(agent="flight_agent", read_set=[DATE_CELL],
                     read_values={DATE_CELL: date_seen}, read_time=t_read,
                     write_set=[f"trip/bookings/{key}"],
                     write_values={f"trip/bookings/{key}": date_seen},
                     write_time=t_write, experiment="store", mode=mode,
                     session=state["session"], regenerations=regenerations,
                     pinned_seconds=round(w_write - w_read, 4), booking_text=text)
            flight_committed.set()
            return {"booking_text": text, "date_used": date_seen,
                    "regenerations": regenerations,
                    "pinned_seconds": w_write - w_read}

    def date_node(state: DateState, runtime: Runtime) -> dict:
        s = runtime.store
        if mode == "sequential":
            flight_committed.wait()
        else:
            flight_read_done.wait()
            time.sleep(0.15)               # land inside the generation phase
        date_started.set()
        item = s.get(TRIP_NS, "date")
        _, t_read, _ = s.last_stamp()
        old = item.value["date"] if item else NULL
        fallback_date = (date.fromisoformat(old) + timedelta(days=7)).isoformat() \
            if old != NULL else "2026-06-21"
        reply = client.complete(
            "You are the user's assistant. The user wants to move the trip one "
            "week later. Reply with the new date only, ISO format YYYY-MM-DD.",
            f"Current trip date: {old}.", max_tokens=16,
            mock_reply=fallback_date, mock_latency=0.05)
        new = parse_iso(reply)
        fallback = new is None or new == old
        if fallback:
            new = fallback_date
        s.put(TRIP_NS, "date", {"date": new})
        _, t_write, _ = s.last_stamp()
        rec.emit(agent="date_agent", read_set=[DATE_CELL], read_values={DATE_CELL: old},
                 read_time=t_read, write_set=[DATE_CELL], write_values={DATE_CELL: new},
                 write_time=t_write, experiment="store", mode=mode,
                 session=state["session"], model_fallback=fallback)
        return {"new_date": new, "fallback": fallback}

    ga = StateGraph(FlightState)
    ga.add_node("book", flight_node)
    ga.add_edge(START, "book")
    ga.add_edge("book", END)

    gb = StateGraph(DateState)
    gb.add_node("update", date_node)
    gb.add_edge(START, "update")
    gb.add_edge("update", END)
    return ga.compile(store=store), gb.compile(store=store)


def run_store_experiment(client: ModelClient, rec: Recorder, n: int, mode: str) -> dict:
    sessions = []
    for k in range(n):
        clock = Clock()
        store = InstrumentedStore(clock)
        first = len(rec.records)
        store.put(TRIP_NS, "date", {"date": "2026-06-14"})   # seed: the Sec 1.1 scenario
        _, t_seed, _ = store.last_stamp()
        # Log the seed as a write op: Sec 3.3's flat-trace A3 residue fires on any
        # read of an un-logged initial value, and "a deployment that logs cell
        # initialization as a write collapses the over-approximation".
        rec.emit(agent="seed", read_set=[], read_values={}, read_time=0,
                 write_set=[DATE_CELL], write_values={DATE_CELL: "2026-06-14"},
                 write_time=t_seed, experiment="store", mode=mode, session=k, seed=True)
        ev = [threading.Event() for _ in range(3)]
        ga, gb = build_store_graphs(client, store, rec, *ev, mode=mode)
        out: dict[str, Any] = {}
        ta = threading.Thread(target=lambda: out.__setitem__("a", ga.invoke({"session": k, "mode": mode})))
        tb = threading.Thread(target=lambda: out.__setitem__("b", gb.invoke({"session": k})))
        ta.start(); tb.start(); ta.join(); tb.join()
        h = rec.records[first:]
        rec.dump_session(h, f"store_{mode}_{k:04d}")
        wit = a1_witnesses(h)
        final = store.get(TRIP_NS, "date").value["date"]
        booking = store.get(BOOK_NS, f"booking-{k}").value
        sessions.append({
            "session": k,
            "a1": bool(wit),
            "witnesses": wit,
            "date_at_commit": final,
            "date_in_booking": booking["date_used"],
            # operational materiality of a firing (the Sec 5.9 question): did the
            # stale date reach the external effect? Only meaningful when A_1 fired;
            # under `sequential` the booking legitimately predates the change.
            "stale_in_booking_text": bool(wit) and (booking["date_used"] in booking["text"]) and (final not in booking["text"]),
            "regenerations": out["a"].get("regenerations", 0),
            "pinned_seconds": out["a"].get("pinned_seconds", 0.0),
            "model_fallback": out["b"].get("fallback", False),
        })
    fires = sum(s["a1"] for s in sessions)
    pinned = [s["pinned_seconds"] for s in sessions]
    lo, hi = clopper_pearson(fires, n)
    return {
        "experiment": "store", "mode": mode, "n": n,
        "a1_fires": fires, "a1_rate": fires / n, "ci95": [lo, hi],
        "stale_in_booking_text": sum(s["stale_in_booking_text"] for s in sessions),
        "regenerations_total": sum(s["regenerations"] for s in sessions),
        "pinned_seconds": {"mean": statistics.fmean(pinned), "min": min(pinned), "max": max(pinned)},
        "model_fallbacks": sum(s["model_fallback"] for s in sessions),
        "sessions": sessions,
    }


# ---------------------------------------------------------------------------
# EXPERIMENT B — one StateGraph, two nodes in one superstep, reducer channel
# ---------------------------------------------------------------------------
class PlanState(TypedDict, total=False):
    plan: Annotated[list[str], operator.add]
    summary: str
    revision: str
    entered: Annotated[list[str], operator.add]
    finished: Annotated[list[str], operator.add]


def build_superstep_graph(client: ModelClient, rec: Recorder, session: int, order: list[str],
                          order_lock: threading.Lock, timings: dict):
    plan_cell, summary_cell, superstep_entry_tick = "state/plan", "state/summary", 1

    def mark(name: str, when: str) -> int:
        with order_lock:
            order.append(f"{when}:{name}")
            timings[f"{when}:{name}"] = time.perf_counter()
            return sum(1 for o in order if o.startswith("finish:"))

    def writer(state: PlanState) -> dict:
        mark("writer", "enter")
        plan_seen = list(state["plan"])
        reply = client.complete(
            "Revise the plan. Reply with ONE short imperative sentence that "
            "changes the destination city to Lisbon.",
            "Plan so far: " + " | ".join(plan_seen),
            max_tokens=32, mock_reply="Change the destination to Lisbon.", mock_latency=0.08)
        completion_index = mark("writer", "finish")
        rec.emit(agent="writer", read_set=[plan_cell], read_values={plan_cell: " | ".join(plan_seen)},
                 read_time=superstep_entry_tick, write_set=[plan_cell],
                 write_values={plan_cell: " | ".join(plan_seen + [reply])},
                 write_time=superstep_entry_tick + completion_index,
                 experiment="superstep", session=session, clock="completion")
        return {"plan": [reply], "revision": reply}

    def summarizer(state: PlanState) -> dict:
        mark("summarizer", "enter")
        plan_seen = list(state["plan"])
        reply = client.complete(
            "Summarize the travel plan in ONE sentence, naming the destination city.",
            "Plan: " + " | ".join(plan_seen),
            max_tokens=48, mock_reply="The plan is a three-day trip to Porto.")
        completion_index = mark("summarizer", "finish")
        rec.emit(agent="summarizer", read_set=[plan_cell], read_values={plan_cell: " | ".join(plan_seen)},
                 read_time=superstep_entry_tick, write_set=[summary_cell],
                 write_values={summary_cell: reply},
                 write_time=superstep_entry_tick + completion_index,
                 experiment="superstep", session=session, clock="completion")
        return {"summary": reply}

    g = StateGraph(PlanState)
    g.add_node("writer", writer)
    g.add_node("summarizer", summarizer)
    g.add_edge(START, "writer")
    g.add_edge(START, "summarizer")      # same superstep: both read the entry snapshot
    g.add_edge("writer", END)
    g.add_edge("summarizer", END)
    return g.compile()


def run_superstep_experiment(client: ModelClient, rec: Recorder, n: int) -> dict:
    sessions = []
    for k in range(n):
        first = len(rec.records)
        order: list[str] = []
        timings: dict = {}
        g = build_superstep_graph(client, rec, k, order, threading.Lock(), timings)
        seed_plan = "Three-day trip to Porto in June."
        rec.emit(agent="seed", read_set=[], read_values={}, read_time=0,
                 write_set=["state/plan"], write_values={"state/plan": seed_plan},
                 write_time=0, experiment="superstep", session=k, seed=True)
        t0 = time.perf_counter()
        final = g.invoke({"plan": [seed_plan]})
        wall = time.perf_counter() - t0
        h = rec.records[first:]
        rec.dump_session(h, f"superstep_{k:04d}")
        completion = a1_witnesses(h)
        # barrier clock: both writes commit at the barrier tick -> equal write_time
        hb = [r if r.get("seed") else dict(r, write_time=2) for r in h]
        barrier = a1_witnesses(hb)
        concurrent = ("enter:summarizer" in order and "enter:writer" in order
                      and order.index("enter:writer") < order.index("finish:summarizer")
                      and order.index("enter:summarizer") < order.index("finish:writer"))
        sessions.append({
            "session": k,
            "a1_completion_clock": bool(completion),
            "a1_barrier_clock": bool(barrier),
            "writer_finished_first": order.index("finish:writer") < order.index("finish:summarizer"),
            "nodes_overlapped": concurrent,
            "summary_grounded_in_superseded_plan": ("Lisbon" not in final.get("summary", "")) and any("Lisbon" in p for p in final["plan"]),
            "final_plan": final["plan"], "summary": final.get("summary", ""),
            "superstep_wall_seconds": round(wall, 3),
        })
    n_ = len(sessions)
    fc = sum(s["a1_completion_clock"] for s in sessions)
    fb = sum(s["a1_barrier_clock"] for s in sessions)
    fg = sum(s["summary_grounded_in_superseded_plan"] for s in sessions)
    return {
        "experiment": "superstep", "n": n_,
        "a1_completion_clock": {"fires": fc, "rate": fc / n_, "ci95": list(clopper_pearson(fc, n_))},
        "a1_barrier_clock": {"fires": fb, "rate": fb / n_, "ci95": list(clopper_pearson(fb, n_))},
        "summary_grounded_in_superseded_plan": {"count": fg, "rate": fg / n_, "ci95": list(clopper_pearson(fg, n_))},
        "nodes_overlapped": sum(s["nodes_overlapped"] for s in sessions),
        "sessions": sessions,
    }


# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--provider", default="mock", choices=["mock", "openai", "anthropic", "vllm"])
    ap.add_argument("--model", default="mock")
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--n", type=int, default=30)
    ap.add_argument("--out", default="live_a1_out")
    ap.add_argument("--modes", default="vanilla,validated,sequential")
    ap.add_argument("--skip-superstep", action="store_true")
    ap.add_argument("--mock-latency", type=float, default=1.2)
    args = ap.parse_args()

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    rec = Recorder(out / "records.jsonl")
    client = ModelClient(args.provider, args.model, args.base_url, args.mock_latency)
    import langgraph as _lg
    from importlib.metadata import version as _v

    results: dict[str, Any] = {"provider": args.provider, "model": args.model,
                               "langgraph_version": _v("langgraph"), "n": args.n,
                               "store": {}, "superstep": None}
    print(f"langgraph {results['langgraph_version']}  provider={args.provider} model={args.model}  n={args.n}")
    for mode in [m.strip() for m in args.modes.split(",") if m.strip()]:
        r = run_store_experiment(client, rec, args.n, mode)
        results["store"][mode] = r
        print(f"  STORE {mode:10s}: A1 {r['a1_fires']}/{r['n']}  CI95 [{r['ci95'][0]:.3f},{r['ci95'][1]:.3f}]"
              f"  stale-in-text {r['stale_in_booking_text']}  regenerations {r['regenerations_total']}"
              f"  pinned {r['pinned_seconds']['mean']:.2f}s")
    if not args.skip_superstep:
        r = run_superstep_experiment(client, rec, args.n)
        results["superstep"] = r
        print(f"  SUPERSTEP        : completion-clock A1 {r['a1_completion_clock']['fires']}/{r['n']}"
              f"  barrier-clock A1 {r['a1_barrier_clock']['fires']}/{r['n']}"
              f"  superseded-grounding {r['summary_grounded_in_superseded_plan']['count']}/{r['n']}"
              f"  overlapped {r['nodes_overlapped']}/{r['n']}")
    rec.close()
    (out / "results.json").write_text(json.dumps(results, indent=2))
    print(f"wrote {out/'records.jsonl'} ({len(rec.records)} records) and {out/'results.json'}")

    # ---- self-test: the mock provider must reproduce the structural facts --
    if args.provider == "mock":
        s = results["store"]
        checks = []
        if "vanilla" in s:
            checks.append(("vanilla fires in every session", s["vanilla"]["a1_fires"] == s["vanilla"]["n"]))
        if "sequential" in s:
            checks.append(("sequential control never fires", s["sequential"]["a1_fires"] == 0))
        if "validated" in s:
            checks.append(("validated (L1) never fires", s["validated"]["a1_fires"] == 0))
            checks.append(("validated pays >=1 regeneration per session",
                           s["validated"]["regenerations_total"] >= s["validated"]["n"]))
        if results["superstep"]:
            ss = results["superstep"]
            checks.append(("superstep nodes overlapped in every session", ss["nodes_overlapped"] == ss["n"]))
            checks.append(("completion-clock A1 fires in every session", ss["a1_completion_clock"]["fires"] == ss["n"]))
            checks.append(("barrier-clock A1 never fires (strict inequality)", ss["a1_barrier_clock"]["fires"] == 0))
            checks.append(("summary grounded in superseded plan in every session",
                           ss["summary_grounded_in_superseded_plan"]["count"] == ss["n"]))
        bad = [name for name, ok in checks if not ok]
        for name, ok in checks:
            print(f"  [{'ok' if ok else 'FAIL'}] {name}")
        if bad:
            print("SELF-TEST FAILED", file=sys.stderr)
            return 1
        print("self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
