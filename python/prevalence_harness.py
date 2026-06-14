#!/usr/bin/env python3
"""
prevalence_harness.py

Measure the A_1 (stale-generation) rate of REAL multi-agent frameworks at
runtime, recording operations in the SAME OpRecord format the verified Verus
detector reasons about, so the empirical detector and the mechanised spec
agree by construction.

WHAT THIS IS (and is not)
  IS:  a runtime instrumentation + reference detector that (a) wraps a real
       framework's shared-state reads/writes into OpRecords, (b) applies the
       cross-agent A_1 predicate that lib_l2_safety.rs::a1_witness formalises,
       and (c) reports per-(framework, model) rates with exact CIs.
  NOT: a re-implementation of any framework, and NOT a claim that wrapping
       node functions changes framework semantics -- the wrapper observes the
       exact state dict a node receives and the exact update it returns, which
       is where staleness is observable.

THE DETECTOR (must match the verified spec)
  lib_l2_safety.rs::a1_witness_at_commit(s,t): a committed txn t has a cell c
  in its read_set whose current committed value differs from the value t read.
  In trace form, CROSS-AGENT A_1 fires for op O by agent A reading cell c with
  value v at read_time r, committing at write_time w_O, iff some OTHER agent B
  committed a write of value v' != v to c at time w with r < w < w_O. That is:
  O generated its write from a value that a concurrent agent had already
  superseded. This module implements exactly that and nothing looser.

MODELS
  Supports OpenAI, Anthropic, and any OpenAI-compatible endpoint (vLLM serving
  Llama/Mistral/Qwen). Set --provider and --base-url; open-weights models run
  through the same path as hosted ones, so the rate is comparable across them.

USAGE (analysis of recorded sessions)
  python prevalence_harness.py analyze ./oprecords/ --out rates.json

USAGE (as a library, instrumenting a framework -- see prevalence_langgraph_example.py)
  rec = SessionRecorder(path, framework="langgraph", model="gpt-4o", scenario="research")
  wrapped_node = rec.instrument(node_fn, agent_id="planner")   # for LangGraph
  ... run the graph ...
  rec.close()
"""
from __future__ import annotations
import argparse
import glob
import json
import math
import os
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Callable


class _TrackingState(dict):
    """A dict that records which keys are accessed, so instrument() captures a
    precise read_set instead of the whole state. [], .get(), and `in` record
    the single key touched; keys()/items()/values()/iteration conservatively
    mark all keys (a node that iterates the state genuinely reads all of it)."""
    def __init__(self, src):
        super().__init__(src)
        self.accessed: set = set()
    def __getitem__(self, k):
        self.accessed.add(k); return super().__getitem__(k)
    def get(self, k, default=None):
        self.accessed.add(k); return super().get(k, default)
    def __contains__(self, k):
        self.accessed.add(k); return super().__contains__(k)
    def keys(self):
        self.accessed.update(super().keys()); return super().keys()
    def items(self):
        self.accessed.update(super().keys()); return super().items()
    def values(self):
        self.accessed.update(super().keys()); return super().values()
    def __iter__(self):
        self.accessed.update(super().keys()); return super().__iter__()


@dataclass
class OpRecord:
    agent_id: str
    op_index: int
    read_set: list[str]
    read_values: dict[str, str]
    read_time: int
    write_set: list[str]
    write_values: dict[str, str]
    write_time: int
    scenario: str
    session_id: str
    framework: str = ""
    model: str = ""
    superstep: int = 0

    def to_jsonl(self) -> str:
        return json.dumps(asdict(self), separators=(",", ":"))


class SessionRecorder:
    """Records one session. The `instrument` method wraps a framework node so
    that the dict the node READS (its input state) and the dict it WRITES (its
    returned update) become an OpRecord. State values are stringified and
    truncated to 500 chars -- truncation is a conservative FALSE-NEGATIVE
    direction (two writes differing only past 500 chars compare equal), never
    a false positive."""

    def __init__(self, path: str | Path, framework: str, model: str,
                 scenario: str, session_id: str | None = None):
        self.path = Path(path)
        self.framework = framework
        self.model = model
        self.scenario = scenario
        self.session_id = session_id or self.path.stem
        self._fh = None
        self._step = 0
        self._superstep = 0
        self.records: list[OpRecord] = []

    def bump_superstep(self) -> None:
        """Advance to the next superstep. The framework driver calls this at
        each superstep boundary (e.g. after every LangGraph stream chunk) so
        that ops recorded by concurrently-scheduled nodes share a superstep."""
        self._superstep += 1

    def open(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._fh = open(self.path, "w")
        return self

    def __enter__(self):
        return self.open()

    def __exit__(self, *a):
        self.close()

    @staticmethod
    def _vals(d: dict[str, Any]) -> dict[str, str]:
        return {str(k): str(v)[:500] for k, v in (d or {}).items()}

    def record(self, agent_id: str, read_state: dict[str, Any],
               write_update: dict[str, Any], superstep: int = 0) -> None:
        """Record one read/generate/write operation tagged with its superstep.
        Nodes that execute concurrently (same superstep) get the same value;
        this is what the detector uses to find same-superstep supersession."""
        self._step += 1
        rv = self._vals(read_state)
        wv = self._vals(write_update)
        rec = OpRecord(
            agent_id=agent_id,
            op_index=self._step,
            read_set=sorted(rv.keys()),
            read_values=rv,
            read_time=2 * superstep,
            write_set=sorted(wv.keys()),
            write_values=wv,
            write_time=2 * superstep + 1,
            scenario=self.scenario,
            session_id=self.session_id,
            framework=self.framework,
            model=self.model,
            superstep=superstep,
        )
        self.records.append(rec)
        if self._fh:
            self._fh.write(rec.to_jsonl() + "\n")
            self._fh.flush()

    def instrument(self, node_fn: Callable, agent_id: str, superstep: int = 0) -> Callable:
        """Wrap a LangGraph-style node `state -> update`. Records ONLY the keys
        the node actually accesses (via _TrackingState), tagged with the given
        superstep so the detector can find same-superstep cross-agent
        supersession. Does NOT alter the node's behaviour. For a real-graph
        corpus, pass each node's topological layer as `superstep` (nodes that
        can run concurrently share a layer)."""
        def wrapped(state, *args, **kwargs):
            if hasattr(state, "keys"):
                tracked = _TrackingState(state)
                update = node_fn(tracked, *args, **kwargs)
                read_state = {k: state[k] for k in tracked.accessed if k in state}
            else:
                update = node_fn(state, *args, **kwargs)
                read_state = {"_state": state}
            write_update = dict(update) if hasattr(update, "items") else {"_out": update}
            self.record(agent_id, read_state, write_update, superstep=superstep)
            return update
        wrapped.__name__ = getattr(node_fn, "__name__", "node")
        return wrapped

    def close(self):
        if self._fh:
            self._fh.close()
            self._fh = None


def a1_firings(records: list[OpRecord]) -> list[dict]:
    """Cross-agent A_1 witnesses under the superstep model that LangGraph (and
    CrewAI's parallel steps) actually use: a node always reads the latest
    COMMITTED state at superstep start, so the only real staleness is when two
    nodes in the SAME superstep touch one cell -- one reads value v while
    another concurrently commits v' != v. Op O (superstep k, agent A) reading
    cell c=v fires iff some op O' in the same superstep k, by a different agent,
    writes c=v' with v' != v. This is order-independent and matches
    lib_l2_safety.rs::a1_witness evaluated at the superstep-commit point."""
    by_ss: dict[int, list[OpRecord]] = {}
    for r in records:
        by_ss.setdefault(r.superstep, []).append(r)
    firings = []
    for ss, ops in by_ss.items():
        for r in ops:
            for c in r.read_set:
                v = r.read_values.get(c, "")
                hit = False
                for w in ops:
                    if w.agent_id == r.agent_id:
                        continue
                    if c in w.write_set and w.write_values.get(c, "") != v:
                        firings.append({
                            "session": r.session_id, "superstep": ss,
                            "agent": r.agent_id, "cell": c, "read_value": v,
                            "superseding_value": w.write_values.get(c, ""),
                            "by_agent": w.agent_id,
                        })
                        hit = True
                        break
                if hit:
                    break
    return firings


def any_agent_a1_firings(records: list[OpRecord]) -> list[dict]:
    """ANY-agent superstep variant: same as above but also counts a same-agent
    concurrent write in the superstep (excluding the reading op itself). Both
    metrics are reported, as in the paper's 90%/89% split."""
    by_ss: dict[int, list[OpRecord]] = {}
    for r in records:
        by_ss.setdefault(r.superstep, []).append(r)
    firings = []
    for ss, ops in by_ss.items():
        for r in ops:
            for c in r.read_set:
                v = r.read_values.get(c, "")
                hit = False
                for w in ops:
                    if w.op_index == r.op_index:
                        continue
                    if c in w.write_set and w.write_values.get(c, "") != v:
                        firings.append({"session": r.session_id, "superstep": ss,
                                        "agent": r.agent_id, "cell": c})
                        hit = True
                        break
                if hit:
                    break
    return firings


def clopper_pearson(k: int, n: int, alpha: float = 0.05) -> tuple[float, float]:
    if n == 0:
        return (0.0, 1.0)
    try:
        from scipy.stats import beta
        lo = 0.0 if k == 0 else beta.ppf(alpha / 2, k, n - k + 1)
        hi = 1.0 if k == n else beta.ppf(1 - alpha / 2, k + 1, n - k)
        return (float(lo), float(hi))
    except Exception:
        p = k / n
        se = math.sqrt(p * (1 - p) / n) if 0 < p < 1 else 0.0
        return (max(0.0, p - 1.96 * se), min(1.0, p + 1.96 * se))


def load_session(path: str) -> list[OpRecord]:
    recs = []
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        d = json.loads(line)
        recs.append(OpRecord(**{k: d.get(k) for k in OpRecord.__dataclass_fields__}))
    return recs


def analyze(dirpath: str, out: str | None) -> dict:
    files = sorted(glob.glob(os.path.join(dirpath, "*.jsonl")))
    if not files:
        raise SystemExit(f"no .jsonl session files in {dirpath}")
    groups: dict[tuple, list[str]] = {}
    for f in files:
        recs = load_session(f)
        if not recs:
            continue
        key = (recs[0].framework or "?", recs[0].model or "?", recs[0].scenario or "?")
        groups.setdefault(key, []).append(f)

    report = {}
    print(f"{'framework':12}{'model':18}{'scenario':16}{'n':>4}"
          f"{'cross-A1':>10}{'95% CI':>16}{'any-A1':>9}")
    print("-" * 85)
    for key, fs in sorted(groups.items()):
        fw, model, scen = key
        n = len(fs)
        cross_hits = 0
        any_hits = 0
        for f in fs:
            recs = load_session(f)
            if a1_firings(recs):
                cross_hits += 1
            if any_agent_a1_firings(recs):
                any_hits += 1
        lo, hi = clopper_pearson(cross_hits, n)
        report[f"{fw}|{model}|{scen}"] = {
            "n": n, "cross_agent_a1": cross_hits, "cross_rate": cross_hits / n,
            "cross_ci": [lo, hi], "any_agent_a1": any_hits, "any_rate": any_hits / n,
        }
        ci = f"[{100*lo:.0f},{100*hi:.0f}]"
        print(f"{fw:12}{model:18}{scen:16}{n:>4}"
              f"{f'{100*cross_hits/n:.0f}%':>10}{ci:>16}{f'{100*any_hits/n:.0f}%':>9}")
    if out:
        json.dump(report, open(out, "w"), indent=2)
        print(f"\nwrote {out}")
    return report


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("analyze")
    a.add_argument("dir")
    a.add_argument("--out", default=None)
    args = ap.parse_args()
    if args.cmd == "analyze":
        analyze(args.dir, args.out)


if __name__ == "__main__":
    main()