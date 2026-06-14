"""
instrument.py — emit one JSONL event per agent operation.

Two API levels:

  1. Two-phase: agent.begin(read_keys) ... agent.commit(write_kv)
     Use this when you want to interleave reads and writes across
     agents — the canonical pattern for surfacing A_1 (Stale-Generation).

  2. Atomic one-shot: agent.op(read_keys, write_kv)
     Convenience wrapper. Read snapshot and commit happen back-to-back;
     no interleaving with other agents possible.

Each emitted OpRecord has BOTH read fields and write fields, with
read_time < write_time. This is the shape the analyser and the TLA+
Anomalies.tla expect.
"""

from __future__ import annotations

import json
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


class SharedStore:
    """Thread-safe key-value store with monotonic clock."""

    def __init__(self) -> None:
        self._data: dict[str, str] = {}
        self._lock = threading.Lock()
        self._clock = 0

    def now(self) -> int:
        with self._lock:
            return self._clock

    def tick(self) -> int:
        """Advance the clock by 1 without changing data."""
        with self._lock:
            self._clock += 1
            return self._clock

    def read(self, keys: list[str]) -> tuple[dict[str, str], int]:
        with self._lock:
            return ({k: self._data.get(k, "NULL") for k in keys}, self._clock)

    def write(self, kv: dict[str, str]) -> int:
        with self._lock:
            self._clock += 1
            self._data.update(kv)
            return self._clock


class ToolRegistry:
    def __init__(self, initial: list[str]) -> None:
        self._tools: set[str] = set(initial)
        self._lock = threading.Lock()

    def visible(self) -> list[str]:
        with self._lock:
            return sorted(self._tools)

    def remove(self, tool: str) -> None:
        with self._lock:
            self._tools.discard(tool)

    def add(self, tool: str) -> None:
        with self._lock:
            self._tools.add(tool)


@dataclass
class Recorder:
    output_path: Path
    _file: Any = field(init=False, default=None)
    _lock: threading.Lock = field(init=False, default_factory=threading.Lock)

    def open(self) -> None:
        self.output_path.parent.mkdir(parents=True, exist_ok=True)
        self._file = self.output_path.open("w")

    def emit(self, event: dict[str, Any]) -> None:
        with self._lock:
            assert self._file is not None, "Recorder not opened"
            self._file.write(json.dumps(event, sort_keys=True) + "\n")
            self._file.flush()

    def close(self) -> None:
        if self._file is not None:
            self._file.close()


class InstrumentedAgent:
    def __init__(
            self,
            agent_id: str,
            store: SharedStore,
            tools: ToolRegistry,
            recorder: Recorder,
    ) -> None:
        self.agent_id = agent_id
        self.store = store
        self.tools = tools
        self.recorder = recorder
        self._pending: dict[str, Any] | None = None

    def begin(self, read_keys: list[str], planned_tool: str | None = None) -> None:
        """Snapshot read state. No clock advance, no commit yet."""
        if self._pending is not None:
            raise RuntimeError(
                f"agent {self.agent_id}: begin() called while another op is pending"
            )
        read_values, read_time = self.store.read(read_keys)
        self._pending = {
            "read_set": list(read_keys),
            "read_values": read_values,
            "read_time": read_time,
            "tools_visible_at_read": self.tools.visible(),
            "planned_tool": planned_tool,
        }

    def commit(
            self,
            write_kv: dict[str, str] | None = None,
            tool_used: str | None = None,
    ) -> None:
        """Commit writes (if any) and emit one OpRecord. Always ticks clock."""
        if self._pending is None:
            raise RuntimeError(
                f"agent {self.agent_id}: commit() called without prior begin()"
            )
        p = self._pending
        self._pending = None

        if write_kv:
            write_time = self.store.write(write_kv)
        else:
            write_time = self.store.tick()

        tools_used: list[str] = []
        chosen_tool = tool_used or p["planned_tool"]
        if chosen_tool and chosen_tool in self.tools.visible():
            tools_used.append(chosen_tool)

        write_set = list(write_kv.keys()) if write_kv else []
        write_values = dict(write_kv) if write_kv else {}
        io = [[k, v] for k, v in (write_kv or {}).items()]
        co = io.copy()

        event = {
            "agent": self.agent_id,
            "read_set": p["read_set"],
            "read_values": p["read_values"],
            "read_time": p["read_time"],
            "write_set": write_set,
            "write_values": write_values,
            "write_time": write_time,
            "planned_tool": p["planned_tool"],
            "tools_used": tools_used,
            "tools_visible_at_read": p["tools_visible_at_read"],
            "io": io,
            "co": co,
        }
        self.recorder.emit(event)

    def op(
            self,
            read_keys: list[str],
            write_kv: dict[str, str] | None = None,
            planned_tool: str | None = None,
            tool_used: str | None = None,
    ) -> None:
        """Atomic read-then-commit. No interleaving with other agents."""
        self.begin(read_keys, planned_tool=planned_tool)
        time.sleep(0.001)
        self.commit(write_kv=write_kv, tool_used=tool_used)


def make_scenario(output_path: Path, agent_ids: list[str], tool_ids: list[str]):
    store = SharedStore()
    tools = ToolRegistry(tool_ids)
    recorder = Recorder(output_path)
    recorder.open()
    agents = {
        aid: InstrumentedAgent(aid, store, tools, recorder)
        for aid in agent_ids
    }
    return store, tools, recorder, agents


if __name__ == "__main__":
    out = Path("/tmp/instrument-smoke-test.jsonl")
    store, tools, recorder, agents = make_scenario(out, ["a1", "a2"], ["t1", "t2"])

    agents["a1"].begin(["c1"], planned_tool="t1")
    agents["a2"].begin(["c1"], planned_tool="t2")
    agents["a2"].commit({"c1": "v2"}, tool_used="t2")
    agents["a1"].commit({"c1": "v1"}, tool_used="t1")

    recorder.close()
    print(f"Wrote {out}")
    print(out.read_text())

def emit_raw(recorder: Recorder, event: dict) -> None:
    """
    Emit a fully-formed OpRecord directly. Used to inject A_3 / A_6
    witnesses that the well-behaved SharedStore cannot produce on its
    own. Caller is responsible for the full event shape.
    """
    required = {
        "agent", "read_set", "read_values", "read_time",
        "write_set", "write_values", "write_time",
        "io", "co",
    }
    missing = required - event.keys()
    if missing:
        raise ValueError(f"emit_raw missing fields: {missing}")
    event.setdefault("planned_tool", None)
    event.setdefault("tools_used", [])
    event.setdefault("tools_visible_at_read", [])
    recorder.emit(event)
