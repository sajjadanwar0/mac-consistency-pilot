"""
production_extractor.py - LLM-client wrapper that records every model call
as an OpRecord-shaped trace event compatible with the verified detector.

v4 CHANGES vs v3
  - `stateful_tools` now maps tool_name -> (kind, namespace) where
    kind in {"read", "write"}. Read-tools are NOT added to write_set
    (their results are captured in the read_set on the NEXT turn via
    FunctionExecutionResult tracking). Write-tools are added to
    write_set with the EXTRACTED "value" field from the call args,
    not the raw JSON. This eliminates the false-positive A_1 fires
    that v3 produced from comparing tool-call ARGS against tool RESULTS.
  - Non-stateful tools (not in the mapping) retain v3 behavior:
    treated as writes with full args. This is correct for stateless
    tools like web_search where the call args ARE the cell's
    effective input (the query) and successive invocations get
    distinct cells.

DESIGN
  Three tool categories:

    1. Stateful READ tool (kind="read"): e.g. read_workspace(slot=...)
       - Allocates cell <namespace>:<slot>
       - Registers call_id -> cell (for next turn's read tracking)
       - NOT added to write_set (it's a read, not a state mutation)

    2. Stateful WRITE tool (kind="write"): e.g. write_workspace(slot=..., value=...)
       - Allocates cell <namespace>:<slot>
       - Added to write_set with EXTRACTED value (not raw args JSON)
       - Comparable to read results which also contain raw values

    3. Stateless tool: e.g. web_search(query=...)
       - Allocates cell <tool_name>:<invocation_index>
       - Added to write_set with raw args (matches v3 behavior)
       - Successive invocations get distinct cells; A_1 can't fire from
         these alone (no shared cell across invocations).

  Cell-value comparison for A_1 is now between:
    - read_values[c]: actual tool RESULT (e.g. "Develop a plan...")
    - write_values[c]: extracted value (e.g. "Finalize the plan...")
  Both are content strings, not JSON arg blobs, so the detector's
  string-equality test reflects actual state changes.
"""

from __future__ import annotations
import json
from collections import defaultdict
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any


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

    def to_jsonl(self) -> str:
        return json.dumps(asdict(self), separators=(",", ":"))


class OpRecorder:
    """Per-session trace recorder.

    `stateful_tools`: dict mapping tool_name -> (kind, namespace) where
    kind in {"read", "write"}. Read-tools do NOT appear in write_set.
    Write-tools appear with extracted "value" field.
    """

    def __init__(self, path: Path, scenario: str, session_id: str,
                 stateful_tools: dict[str, tuple[str, str]] | None = None):
        self.path = path
        self.scenario = scenario
        self.session_id = session_id
        self.stateful_tools = stateful_tools or {}
        self._fh = None
        self._step = 0
        self._tool_index: dict[str, int] = defaultdict(int)
        self._cell_value: dict[str, str] = {}
        self._call_id_to_cell: dict[str, str] = {}

    def open(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._fh = open(self.path, "w")

    def close(self) -> None:
        if self._fh is not None:
            self._fh.close()
            self._fh = None

    def next_step(self) -> int:
        self._step += 1
        return self._step

    def tool_kind(self, tool_name: str) -> str | None:
        """Returns "read", "write", or None (for stateless tools)."""
        entry = self.stateful_tools.get(tool_name)
        if entry is None:
            return None
        kind, _namespace = entry
        return kind

    def allocate_cell(self, tool_name: str, args_json: str) -> str:
        entry = self.stateful_tools.get(tool_name)
        if entry is not None:
            _kind, namespace = entry
            slot = self._extract_slot(args_json)
            return f"{namespace}:{slot}"
        idx = self._tool_index[tool_name]
        self._tool_index[tool_name] += 1
        return f"{tool_name}:{idx}"

    @staticmethod
    def _extract_slot(args_json: str) -> str:
        try:
            d = json.loads(args_json)
            if isinstance(d, dict):
                for k in ("slot", "key", "name", "id"):
                    if k in d:
                        return str(d[k])[:32]
                if d:
                    return str(next(iter(d.values())))[:32]
        except Exception:
            pass
        return "default"

    @staticmethod
    def extract_write_value(args_json: str) -> str:
        """For write-kind tools, pull out the value field that represents
        the actual content being written. Falls back to full args."""
        try:
            d = json.loads(args_json)
            if isinstance(d, dict):
                for k in ("value", "content", "data", "text"):
                    if k in d:
                        return str(d[k])[:500]
        except Exception:
            pass
        return args_json[:500]

    def remember(self, cell: str, value: str) -> None:
        self._cell_value[cell] = (value or "")[:500]

    def value_of(self, cell: str) -> str:
        return self._cell_value.get(cell, "")

    def register_call(self, call_id: str, cell: str) -> None:
        if call_id:
            self._call_id_to_cell[call_id] = cell

    def cell_for_call(self, call_id: str) -> str | None:
        return self._call_id_to_cell.get(call_id)

    def write(self, record: OpRecord) -> None:
        if self._fh is None:
            raise RuntimeError("OpRecorder not open")
        self._fh.write(record.to_jsonl() + "\n")
        self._fh.flush()


def _extract_tool_calls_with_ids(result) -> list[tuple[str, str, str]]:
    out = []
    content = getattr(result, "content", None)
    if content is None:
        return out
    if isinstance(content, list):
        for item in content:
            name = getattr(item, "name", None)
            args = getattr(item, "arguments", None)
            call_id = getattr(item, "id", None)
            if name is None and isinstance(item, dict):
                name = item.get("name")
                args = item.get("arguments")
                call_id = item.get("id")
            if name:
                if not isinstance(args, str):
                    args = (json.dumps(args, default=str)
                            if args is not None else "")
                out.append((str(name), str(args), str(call_id or "")))
    return out


def _extract_tool_results(messages) -> list[tuple[str, str]]:
    out = []
    for m in messages:
        content = getattr(m, "content", None)
        if content is None and isinstance(m, dict):
            content = m.get("content")
        if isinstance(content, list):
            for item in content:
                call_id = getattr(item, "call_id", None)
                result = getattr(item, "content", None)
                if call_id is None and isinstance(item, dict):
                    call_id = item.get("call_id")
                    result = item.get("content")
                if call_id is not None:
                    text = result if isinstance(result, str) else str(result)
                    out.append((str(call_id), text or ""))
    return out


class ProductionExtractor:
    def __init__(self, inner_client, recorder: OpRecorder, agent_name: str):
        self._inner = inner_client
        self._recorder = recorder
        self._agent_name = agent_name

    def __getattr__(self, name: str) -> Any:
        return getattr(self._inner, name)

    async def create(self, messages, tools=None, *args, **kwargs):
        rec = self._recorder
        agent = self._agent_name

        # READ PHASE: tool results from earlier turns.
        read_time = rec.next_step()
        read_set: list[str] = []
        read_values: dict[str, str] = {}

        for call_id, result_text in _extract_tool_results(messages):
            cell = rec.cell_for_call(call_id)
            if cell is None:
                continue
            # First-occurrence wins; later occurrences are duplicates of the
            # same cell observation from the same call_id.
            if cell not in read_set:
                read_set.append(cell)
                read_values[cell] = result_text[:500]
                rec.remember(cell, result_text)

        # INNER CALL.
        result = await self._inner.create(messages, tools=tools, *args, **kwargs)

        # WRITE PHASE: tool calls in the response. Read-kind tools register
        # their cell but do NOT appear in write_set.
        write_set: list[str] = []
        write_values: dict[str, str] = {}
        for tool_name, args_json, call_id in _extract_tool_calls_with_ids(result):
            cell = rec.allocate_cell(tool_name, args_json)
            rec.register_call(call_id, cell)

            kind = rec.tool_kind(tool_name)
            if kind == "read":
                # Pure read; do not record as a write.
                continue
            if cell not in write_set:
                write_set.append(cell)
            if kind == "write":
                write_values[cell] = rec.extract_write_value(args_json)
            else:
                # Stateless tool: keep v3 semantics (raw args as value).
                write_values[cell] = args_json[:500]

        write_time = rec.next_step()

        rec.write(OpRecord(
            agent_id=agent,
            op_index=rec._step,
            read_set=read_set,
            read_values=read_values,
            read_time=read_time,
            write_set=write_set,
            write_values=write_values,
            write_time=write_time,
            scenario=rec.scenario,
            session_id=rec.session_id,
        ))

        return result

    async def close(self) -> None:
        if hasattr(self._inner, "close"):
            await self._inner.close()