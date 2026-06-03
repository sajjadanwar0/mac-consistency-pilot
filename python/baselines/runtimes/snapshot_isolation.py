"""
Snapshot-isolation baseline runtime.

MVCC store: each cell is a chain of (version, value, commit_time) tuples.
Reads return the latest version with commit_time <= read_time.
Commits validate that no cell in read_set was modified between read_time and commit_time.
On validation failure, the commit is REJECTED and no OpRecord is emitted.

A separate counter tracks rejected commits per scenario for the analysis tables.

Expected behaviour against the four anomalies:
  A_1 (stale-generation):       PREVENTED. Validation aborts on concurrent write.
  A_2 (phantom-tool):           NOT PREVENTED. SI does not address tool registry.
  A_3 (causal-cascade):         PREVENTED. SI's read-stability implies all reads are
                                from prior committed writes.
  A_6 (tool-effect-reorder):    NOT PREVENTED. SI is a memory protocol, not a tool one.

Note: the rejected-commit count IS reported separately. A high rejection rate is
itself a real cost of SI in the agent setting because each abort means a re-do
of a long-running LLM inference.
"""

from __future__ import annotations

import json
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


class MVCCStore:
    """Cell-versioned key-value store.

    Each cell maps to a list of (commit_time, value) tuples in commit-time order.
    Snapshot reads return the last value with commit_time <= snapshot_time.
    """

    def __init__(self) -> None:
        # cell -> list of (commit_time, value), in monotonic commit_time order.
        self._versions: dict[str, list[tuple[int, str]]] = {}
        self._lock = threading.Lock()
        self._clock = 0
        # Tracks rejected (validation-failed) commits for telemetry.
        self.rejected_commits = 0

    def now(self) -> int:
        with self._lock:
            return self._clock

    def tick(self) -> int:
        with self._lock:
            self._clock += 1
            return self._clock

    def snapshot_read(self, keys: list[str]) -> tuple[dict[str, str], int]:
        """Read snapshot at current clock; return values and the read_time."""
        with self._lock:
            t = self._clock
            result: dict[str, str] = {}
            for k in keys:
                versions = self._versions.get(k, [])
                # Find latest version with commit_time <= t.
                value = "NULL"
                for ct, v in versions:
                    if ct <= t:
                        value = v
                    else:
                        break
                result[k] = value
            return result, t

    def validate_and_commit(
        self,
        read_set: list[str],
        read_time: int,
        write_kv: dict[str, str],
    ) -> int | None:
        """Atomic validate-then-commit. Returns commit_time on success, None on abort.

        Validation: no cell in read_set has any version with commit_time > read_time.
        """
        with self._lock:
            for c in read_set:
                versions = self._versions.get(c, [])
                for ct, _ in versions:
                    if ct > read_time:
                        # Concurrent write happened. Abort.
                        self.rejected_commits += 1
                        return None
            # Validation passed. Commit.
            self._clock += 1
            commit_time = self._clock
            for k, v in write_kv.items():
                self._versions.setdefault(k, []).append((commit_time, v))
            return commit_time

    def commit_no_writes(self) -> int:
        """Tick clock for a write-set-empty op (no validation needed)."""
        return self.tick()


class SIToolRegistry:
    """Plain tool registry (SI does not lock tools)."""

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
class SIRecorder:
    output_path: Path
    _file: Any = field(init=False, default=None)
    _lock: threading.Lock = field(init=False, default_factory=threading.Lock)
    aborts: int = 0

    def open(self) -> None:
        self.output_path.parent.mkdir(parents=True, exist_ok=True)
        self._file = self.output_path.open("w")

    def emit(self, event: dict[str, Any]) -> None:
        with self._lock:
            assert self._file is not None
            self._file.write(json.dumps(event, sort_keys=True) + "\n")
            self._file.flush()

    def record_abort(self) -> None:
        with self._lock:
            self.aborts += 1

    def close(self) -> None:
        if self._file is not None:
            self._file.close()


class SIAgent:
    """Agent operating under snapshot isolation: snapshot read + validated commit.

    A commit that fails validation is RECORDED in the abort counter but does not
    emit an OpRecord. The detector therefore sees only successful records.
    """

    def __init__(
        self,
        agent_id: str,
        store: MVCCStore,
        tools: SIToolRegistry,
        recorder: SIRecorder,
    ) -> None:
        self.agent_id = agent_id
        self.store = store
        self.tools = tools
        self.recorder = recorder
        self._pending: dict[str, Any] | None = None

    def begin(self, read_keys: list[str], planned_tool: str | None = None) -> None:
        if self._pending is not None:
            raise RuntimeError(f"agent {self.agent_id}: begin during pending op")
        read_values, read_time = self.store.snapshot_read(read_keys)
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
        if self._pending is None:
            raise RuntimeError(f"agent {self.agent_id}: commit without begin")

        p = self._pending
        self._pending = None

        write_kv = write_kv or {}
        if write_kv:
            commit_time = self.store.validate_and_commit(
                p["read_set"], p["read_time"], write_kv
            )
            if commit_time is None:
                self.recorder.record_abort()
                return  # silently drop
        else:
            commit_time = self.store.commit_no_writes()

        tools_used: list[str] = []
        chosen_tool = tool_used or p["planned_tool"]
        if chosen_tool and chosen_tool in self.tools.visible():
            tools_used.append(chosen_tool)

        write_set = list(write_kv.keys())
        write_values = dict(write_kv)
        io = [[k, v] for k, v in write_kv.items()]
        co = io.copy()

        event = {
            "agent": self.agent_id,
            "read_set": p["read_set"],
            "read_values": p["read_values"],
            "read_time": p["read_time"],
            "write_set": write_set,
            "write_values": write_values,
            "write_time": commit_time,
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
        self.begin(read_keys, planned_tool=planned_tool)
        time.sleep(0.001)
        self.commit(write_kv=write_kv, tool_used=tool_used)


def make_scenario_si(
    output_path: Path,
    agent_ids: list[str],
    tool_ids: list[str],
):
    store = MVCCStore()
    tools = SIToolRegistry(tool_ids)
    recorder = SIRecorder(output_path)
    recorder.open()
    agents = {aid: SIAgent(aid, store, tools, recorder) for aid in agent_ids}
    return store, tools, recorder, agents
