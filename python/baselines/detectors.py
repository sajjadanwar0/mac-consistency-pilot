"""
Python port of the four detectors verified sound + complete in Verus.
Operates on JSONL traces emitted by any runtime in this baseline package.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Optional


def _first_value(kv_list, cell):
    """Match Verus first_value spec: first match in the list wins."""
    if isinstance(kv_list, dict):
        for k, v in kv_list.items():
            if k == cell:
                return v
        return None
    for entry in kv_list:
        k, v = entry[0], entry[1]
        if k == cell:
            return v
    return None


def detect_a1(records: list[dict]) -> Optional[tuple[int, int, str]]:
    """Stale-generation. Returns (i, j, cell) of first witness, or None."""
    n = len(records)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            ri = records[i]
            rj = records[j]
            for c in ri.get("read_set", []):
                if c not in rj.get("write_set", []):
                    continue
                if not (
                    ri["read_time"] < rj["write_time"]
                    and rj["write_time"] < ri["write_time"]
                ):
                    continue
                rv = _first_value(ri.get("read_values", {}), c)
                wv = _first_value(rj.get("write_values", {}), c)
                if rv is None or wv is None:
                    continue
                if rv != wv:
                    return (i, j, c)
    return None


def detect_a2(records: list[dict]) -> Optional[int]:
    """Phantom-tool. Returns index of first record with witness, or None."""
    for i, r in enumerate(records):
        planned = r.get("planned_tool")
        if planned is None:
            continue
        visible = r.get("tools_visible_at_read", [])
        used = r.get("tools_used", [])
        if planned in visible and planned not in used:
            return i
    return None


def detect_a3(records: list[dict]) -> Optional[tuple[int, str, str]]:
    """Causal-cascade. Returns (j, cell, value) of first witness, or None."""
    n = len(records)
    for j in range(n):
        rj = records[j]
        for c in rj.get("read_set", []):
            v = _first_value(rj.get("read_values", {}), c)
            if v is None or v == "NULL":
                continue
            has_antecedent = False
            for k in range(n):
                if k == j:
                    continue
                rk = records[k]
                if c not in rk.get("write_set", []):
                    continue
                if rk["write_time"] > rj["read_time"]:
                    continue
                wv = _first_value(rk.get("write_values", {}), c)
                if wv == v:
                    has_antecedent = True
                    break
            if not has_antecedent:
                return (j, c, v)
    return None


def detect_a6(records: list[dict]) -> Optional[int]:
    """Tool-effect-reorder. Returns index of first record with mismatching io/co."""
    for i, r in enumerate(records):
        io = r.get("io", [])
        co = r.get("co", [])
        if len(io) > 0 and io != co:
            return i
    return None


def classify_level(records: list[dict]) -> int:
    """Return the highest L_n satisfied by `records`.

    L_n chain (from §4):
      L_0: no constraints (anything goes)
      L_1: !A_1
      L_2: !A_1 && !A_3
      L_3: !A_1 && !A_3 && !A_6
      L_4: !A_1 && !A_2 && !A_3 && !A_6
    """
    a1 = detect_a1(records) is not None
    a2 = detect_a2(records) is not None
    a3 = detect_a3(records) is not None
    a6 = detect_a6(records) is not None

    if a1:
        return 0
    if a3:
        return 1
    if a6:
        return 2
    if a2:
        return 3
    return 4


def load_trace(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


if __name__ == "__main__":
    smoke = [
        {
            "agent": "a1",
            "read_set": ["c1"],
            "read_values": {"c1": "NULL"},
            "read_time": 0,
            "write_set": ["c1"],
            "write_values": {"c1": "v1"},
            "write_time": 2,
            "planned_tool": None,
            "tools_used": [],
            "tools_visible_at_read": [],
            "io": [["c1", "v1"]],
            "co": [["c1", "v1"]],
        },
        {
            "agent": "a2",
            "read_set": ["c1"],
            "read_values": {"c1": "NULL"},
            "read_time": 0,
            "write_set": ["c1"],
            "write_values": {"c1": "v2"},
            "write_time": 1,
            "planned_tool": None,
            "tools_used": [],
            "tools_visible_at_read": [],
            "io": [["c1", "v2"]],
            "co": [["c1", "v2"]],
        },
    ]
    print("A_1:", detect_a1(smoke))
    print("Level:", classify_level(smoke))
    assert detect_a1(smoke) is not None, "A_1 smoke test should fire"
    assert classify_level(smoke) == 0, "L_0 expected"
    print("smoke test OK")
