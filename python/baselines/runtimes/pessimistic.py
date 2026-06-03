"""
Pessimistic-locking baseline runtime.

Drop-in replacement for instrument.SharedStore + instrument.InstrumentedAgent.
Acquires per-cell locks at begin() and releases them at commit(). Tool-registry
mutations also block while any agent has a planned_tool reservation.

Expected behaviour against the four anomalies:
  A_1 (stale-generation):       PREVENTED. Agents serialise on overlapping cells.
  A_2 (phantom-tool):           PREVENTED. Tool registry locked for planned tools.
  A_3 (causal-cascade):         PREVENTED. No concurrent writes during read-set window.
  A_6 (tool-effect-reorder):    NOT PREVENTED. Within-record ordering is unaffected.

The interface matches instrument.SharedStore exactly so InstrumentedAgent
can be reused without modification.
"""

from __future__ import annotations

import json
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


class PessimisticStore:
    """Per-cell-locked key-value store with monotonic clock.

    Reads block while another agent holds a write or pending-write lock
    on any of the requested cells.
    """

    def __init__(self) -> None:
        self._data: dict[str, str] = {}
        self._global = threading.Lock()
        self._cell_locks: dict[str, threading.Lock] = {}
        # Maps cell -> agent_id currently holding it.
        self._cell_holders: dict[str, str] = {}
        self._clock = 0

    def _ensure_cell_lock(self, cell: str) -> threading.Lock:
        with self._global:
            if cell not in self._cell_locks:
                self._cell_locks[cell] = threading.Lock()
            return self._cell_locks[cell]

    def now(self) -> int:
        with self._global:
            return self._clock

    def tick(self) -> int:
        with self._global:
            self._clock += 1
            return self._clock

    def acquire_cells(self, agent_id: str, cells: list[str]) -> bool:
        """Try to acquire locks on cells in sorted order.

        Returns True on full acquisition, False on conflict (in which case
        no locks are held). Non-blocking: a single failed try_acquire aborts
        the whole acquisition, with all already-held locks released.
        """
        held: list[str] = []
        for cell in sorted(cells):
            lock = self._ensure_cell_lock(cell)
            ok = lock.acquire(blocking=False)
            if not ok:
                # Conflict: release everything we got so far and bail.
                for c in reversed(held):
                    with self._global:
                        self._cell_holders.pop(c, None)
                    self._cell_locks[c].release()
                return False
            held.append(cell)
            with self._global:
                self._cell_holders[cell] = agent_id
        return True

    def release_cells(self, agent_id: str, cells: list[str]) -> None:
        """Release locks on cells held by this agent."""
        for cell in sorted(cells, reverse=True):
            with self._global:
                holder = self._cell_holders.get(cell)
                if holder != agent_id:
                    continue
                self._cell_holders.pop(cell, None)
            self._cell_locks[cell].release()

    def read(self, keys: list[str]) -> tuple[dict[str, str], int]:
        """Read assumes the caller already holds locks via acquire_cells()."""
        with self._global:
            return ({k: self._data.get(k, "NULL") for k in keys}, self._clock)

    def write(self, kv: dict[str, str]) -> int:
        """Write assumes the caller holds locks on all keys via acquire_cells()."""
        with self._global:
            self._clock += 1
            self._data.update(kv)
            return self._clock


class PessimisticToolRegistry:
    """Tool registry with reservation-based locking.

    An agent that plans to use tool T at begin() reserves T; concurrent
    remove(T) blocks until commit() releases the reservation.
    """

    def __init__(self, initial: list[str]) -> None:
        self._tools: set[str] = set(initial)
        self._reservations: dict[str, set[str]] = {}  # tool -> set of agent_ids
        self._lock = threading.Lock()
        self._cv = threading.Condition(self._lock)

    def visible(self) -> list[str]:
        with self._lock:
            return sorted(self._tools)

    def reserve(self, tool: str, agent_id: str) -> bool:
        """Reserve `tool` for `agent_id`. Returns True if tool is currently visible."""
        with self._lock:
            if tool not in self._tools:
                return False
            if tool not in self._reservations:
                self._reservations[tool] = set()
            self._reservations[tool].add(agent_id)
            return True

    def release(self, tool: str, agent_id: str) -> None:
        with self._cv:
            if tool in self._reservations:
                self._reservations[tool].discard(agent_id)
                if not self._reservations[tool]:
                    del self._reservations[tool]
            self._cv.notify_all()

    def remove(self, tool: str) -> bool:
        """Remove tool if not reserved. Returns True if removed, False if blocked."""
        with self._lock:
            if tool in self._reservations and self._reservations[tool]:
                # Blocked: pessimistic-locking would have deferred this.
                return False
            self._tools.discard(tool)
            return True

    def add(self, tool: str) -> None:
        with self._lock:
            self._tools.add(tool)


@dataclass
class PessimisticRecorder:
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

    def close(self) -> None:
        if self._file is not None:
            self._file.close()


class PessimisticAgent:
    """Agent that holds per-cell + per-tool locks from begin() to commit().

    Note that begin() may BLOCK if another agent holds the requested cells.
    This is the explicit serialisation that prevents A_1/A_3.
    """

    def __init__(
        self,
        agent_id: str,
        store: PessimisticStore,
        tools: PessimisticToolRegistry,
        recorder: PessimisticRecorder,
    ) -> None:
        self.agent_id = agent_id
        self.store = store
        self.tools = tools
        self.recorder = recorder
        self._pending: dict[str, Any] | None = None
        self._held_cells: list[str] = []
        self._reserved_tool: str | None = None

    def begin(self, read_keys: list[str], planned_tool: str | None = None) -> None:
        if self._pending is not None:
            raise RuntimeError(f"agent {self.agent_id}: begin during pending op")

        # Try-acquire cell locks; if any conflict, abort this op.
        ok = self.store.acquire_cells(self.agent_id, read_keys)
        if not ok:
            # Conflict: this op is dropped (pessimistic locking would have
            # blocked it). Mark _pending sentinel so commit() skips emission.
            self._pending = {"_aborted": True}
            self._held_cells = []
            return
        self._held_cells = list(read_keys)

        # Reserve tool if planned.
        if planned_tool is not None:
            ok = self.tools.reserve(planned_tool, self.agent_id)
            if ok:
                self._reserved_tool = planned_tool

        # Read snapshot under lock.
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
        if self._pending is None:
            raise RuntimeError(f"agent {self.agent_id}: commit without begin")

        p = self._pending
        self._pending = None

        # If begin() was aborted, this is a no-op.
        if p.get("_aborted"):
            self.recorder.aborts += 1
            return

        # If writing to cells we don't already hold, try to acquire them.
        write_kv = write_kv or {}
        new_cells = [c for c in write_kv if c not in self._held_cells]
        if new_cells:
            ok = self.store.acquire_cells(self.agent_id, new_cells)
            if not ok:
                # Couldn't lock additional cells: abort the op silently.
                self.recorder.aborts += 1
                self.store.release_cells(self.agent_id, self._held_cells)
                self._held_cells = []
                if self._reserved_tool is not None:
                    self.tools.release(self._reserved_tool, self.agent_id)
                    self._reserved_tool = None
                return
            self._held_cells.extend(new_cells)

        # Commit writes (or just tick).
        if write_kv:
            write_time = self.store.write(write_kv)
        else:
            write_time = self.store.tick()

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
            "write_time": write_time,
            "planned_tool": p["planned_tool"],
            "tools_used": tools_used,
            "tools_visible_at_read": p["tools_visible_at_read"],
            "io": io,
            "co": co,
        }
        self.recorder.emit(event)

        # Release everything.
        self.store.release_cells(self.agent_id, self._held_cells)
        self._held_cells = []
        if self._reserved_tool is not None:
            self.tools.release(self._reserved_tool, self.agent_id)
            self._reserved_tool = None

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


def make_scenario_pessimistic(
    output_path: Path,
    agent_ids: list[str],
    tool_ids: list[str],
):
    store = PessimisticStore()
    tools = PessimisticToolRegistry(tool_ids)
    recorder = PessimisticRecorder(output_path)
    recorder.open()
    agents = {
        aid: PessimisticAgent(aid, store, tools, recorder) for aid in agent_ids
    }
    return store, tools, recorder, agents
