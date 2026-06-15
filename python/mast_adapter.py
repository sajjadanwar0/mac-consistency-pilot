"""
mast_adapter_v3.py - Framework-dispatched MAST-Data trace adapter.

v3 KEY CHANGES FROM v2
  v2 used a single generic text parser that matched ^Speaker: at line
  start. That failed on every framework because MAST traces use
  framework-specific log formats:
    - ChatDev: `[timestamp INFO] **Role**: content` markdown
    - MetaGPT: `[timestamp] FROM: X TO: Y` + `ACTION: name`
    - AG2 (AutoGen): YAML-like `role:` / `name:` / `content:` blocks
    - Others (Magentic / OpenManus / AppWorld / HyperAgent):
      heterogeneous and not currently supported.
  v3 dispatches on `mas_name` and runs the framework-specific
  parser. The 3 supported frameworks cover 957/1242 records (77%).

COVERAGE
  Total dataset:   1,242 records
  Supported:        957 records (77%)
    - AG2:          597
    - MetaGPT:      230
    - ChatDev:      130
  Generic fallback: 285 records (Magentic, OpenManus, AppWorld,
                                  HyperAgent), parsed best-effort.

USAGE
  pip install huggingface_hub
  python mast_adapter_v3.py --out ../mast_oprecords/ --limit 20
  # Smoke test first; full run if numbers look right:
  rm -f ../mast_oprecords/*.jsonl
  python mast_adapter_v3.py --out ../mast_oprecords/
  python analyze_production.py ../mast_oprecords/ --out mast_rates.json
"""

from __future__ import annotations
import argparse
import json
import re
import sys
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



METADATA_KEY_PATTERN = re.compile(
    r"^("
    r"\[?Preprocessing\]?|"
    r"ChatDev[\s\w]*Starts|"
    r"Timestamp|"
    r"config_path|"
    r"config_phase_path|"
    r"config_role_path|"
    r"task_prompt|"
    r"project_name|"
    r"Log\s*File|"
    r"ChatDev\w*Config|"
    r"phase_prompt|"
    r"Phase|"
    r"\[\w+\]"
    r")"
    r"$",
    re.IGNORECASE,
)


def is_metadata_role(role: str) -> bool:
    """Returns True if a role string is metadata, not a real agent."""
    r = role.strip().strip("*").strip()
    if not r or len(r) > 60:
        return True
    return bool(METADATA_KEY_PATTERN.match(r))



TOOL_CALL_PATTERN = re.compile(
    r"(?:^|\W)([a-z_][a-z0-9_]{2,40})\s*\((\s*[^)]{0,200}?)\s*\)",
    re.MULTILINE,
)

NON_TOOL_WORDS = {
    "print", "len", "range", "list", "dict", "set", "type", "int",
    "str", "float", "bool", "abs", "min", "max", "sum", "open",
    "input", "format", "round", "isinstance", "hasattr", "getattr",
    "setattr", "delattr", "callable", "id", "hash", "iter", "next",
    "enumerate", "zip", "map", "filter", "sorted", "reversed",
    "any", "all", "true", "false", "none", "self", "return", "if",
    "else", "elif", "for", "while", "try", "except", "raise",
    "with", "as", "def", "class", "lambda", "import", "from",
    "print_board", "make_move", "checkers_game", "initialize_board",
}


def detect_tool_calls_in_content(text: str) -> list[tuple[str, str]]:
    """Find tool-call-shaped expressions in arbitrary text. Returns a
    list of (tool_name, args_string)."""
    out = []
    seen = set()
    for m in TOOL_CALL_PATTERN.finditer(text[:5000]):
        name = m.group(1).lower()
        if name in NON_TOOL_WORDS or len(name) < 3:
            continue
        args = m.group(2)
        key = (name, args[:50])
        if key in seen:
            continue
        seen.add(key)
        out.append((name, args))
        if len(out) >= 5:
            break
    return out




CHATDEV_PREFIX_RE = re.compile(
    r"\[\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2}(?:[\.,]\d+)?\s+\w+\]\s*",
)
CHATDEV_SPEAKER_RE = re.compile(
    r"\*\*([^*\n]{2,60})\*\*\s*:\s*", re.MULTILINE,
)


def parse_chatdev(trajectory: str) -> list[dict]:
    events = []
    text = CHATDEV_PREFIX_RE.sub("", trajectory)
    matches = list(CHATDEV_SPEAKER_RE.finditer(text))
    if not matches:
        return []
    for i, m in enumerate(matches):
        role = m.group(1).strip()
        if is_metadata_role(role):
            continue
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        content = text[start:end].strip()
        if not content or len(content) < 5:
            continue
        events.append({
            "type": "agent_turn",
            "agent": role[:32],
            "content": content[:1000],
        })
        for tn, targs in detect_tool_calls_in_content(content):
            events.append({
                "type": "tool_call",
                "agent": role[:32],
                "tool_name": tn,
                "args": {"raw": targs[:200]},
                "call_id": f"chatdev_{i}_{tn}",
            })
    return events



METAGPT_FROM_TO_RE = re.compile(
    r"\[(\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2})\]\s+FROM:\s+([^\s]+)\s+TO:\s+(\S+)",
    re.MULTILINE,
)
METAGPT_ACTION_RE = re.compile(r"^ACTION:\s+(\S+)", re.MULTILINE)


def parse_metagpt(trajectory: str) -> list[dict]:
    events = []
    matches = list(METAGPT_FROM_TO_RE.finditer(trajectory))
    if not matches:
        return []
    for i, m in enumerate(matches):
        sender = m.group(2).strip()
        receiver = m.group(3).strip().strip("{}'\"")
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(trajectory)
        chunk = trajectory[start:end]
        action_match = METAGPT_ACTION_RE.search(chunk)
        action = action_match.group(1) if action_match else None
        content_start = action_match.end() if action_match else 0
        content = chunk[content_start:].strip()
        events.append({
            "type": "agent_turn",
            "agent": sender[:32],
            "content": content[:1000],
        })
        if action:
            tool_name = action.split(".")[-1][:40].lower()
            events.append({
                "type": "tool_call",
                "agent": sender[:32],
                "tool_name": tool_name,
                "args": {"receiver": receiver[:40]},
                "call_id": f"metagpt_{i}",
            })
        for tn, targs in detect_tool_calls_in_content(content):
            events.append({
                "type": "tool_call",
                "agent": sender[:32],
                "tool_name": tn,
                "args": {"raw": targs[:200]},
                "call_id": f"metagpt_{i}_{tn}",
            })
    return events



AG2_HEADER_RE = re.compile(r"^\s{0,12}(role|name|content)\s*:\s*(.*)$",
                           re.MULTILINE)


def parse_ag2(trajectory: str) -> list[dict]:
    events = []
    current = {"role": None, "name": None, "content": []}
    in_content = False
    content_indent = None
    lines = trajectory.split("\n")
    i = 0

    def flush():
        if current["name"] or current["role"]:
            speaker = current["name"] or current["role"] or "unknown"
            content = "\n".join(current["content"]).strip()
            if content:
                events.append({
                    "type": "agent_turn",
                    "agent": str(speaker)[:32],
                    "content": content[:1000],
                })
                for tn, targs in detect_tool_calls_in_content(content):
                    events.append({
                        "type": "tool_call",
                        "agent": str(speaker)[:32],
                        "tool_name": tn,
                        "args": {"raw": targs[:200]},
                        "call_id": f"ag2_{len(events)}_{tn}",
                    })

    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()
        indent = len(line) - len(stripped)

        m_hdr = re.match(r"^(role|name|content)\s*:\s*(.*)$", stripped)
        if m_hdr:
            key = m_hdr.group(1)
            val = m_hdr.group(2).strip()
            if key == "role":
                flush()
                current = {"role": val or None, "name": None, "content": []}
                in_content = False
            elif key == "name":
                current["name"] = val or None
            elif key == "content":
                in_content = True
                content_indent = indent + 2
                if val:
                    current["content"].append(val)
        elif in_content:
            if line.strip() == "":
                current["content"].append("")
            elif indent > 0 or (content_indent and indent >= content_indent):
                current["content"].append(stripped)
            else:
                in_content = False
        i += 1

    flush()
    return events



GENERIC_LOG_PREFIX_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}[T\s]\d{2}:\d{2}:\d{2}[\.,]?\d*\s*\|?\s*\w*\s*\|?\s*",
    re.MULTILINE,
)
GENERIC_SPEAKER_RE = re.compile(
    r"^(?:\*\*)?([A-Z][A-Za-z0-9_ ]{1,40})(?:\*\*)?\s*:\s*",
    re.MULTILINE,
)


def parse_generic(trajectory: str) -> list[dict]:
    text = GENERIC_LOG_PREFIX_RE.sub("", trajectory)
    events = []
    matches = list(GENERIC_SPEAKER_RE.finditer(text))
    if len(matches) < 2:
        return []
    for i, m in enumerate(matches):
        role = m.group(1).strip()
        if is_metadata_role(role):
            continue
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        content = text[start:end].strip()
        if not content or len(content) < 10:
            continue
        events.append({
            "type": "agent_turn",
            "agent": role[:32],
            "content": content[:1000],
        })
        for tn, targs in detect_tool_calls_in_content(content):
            events.append({
                "type": "tool_call",
                "agent": role[:32],
                "tool_name": tn,
                "args": {"raw": targs[:200]},
                "call_id": f"gen_{i}_{tn}",
            })
    return events



def normalize_mast_trace(trajectory: str, framework: str) -> list[dict]:
    if not isinstance(trajectory, str) or len(trajectory) < 50:
        return []
    fw = framework.lower()
    if fw == "chatdev":
        return parse_chatdev(trajectory)
    elif fw == "metagpt":
        return parse_metagpt(trajectory)
    elif fw == "ag2":
        return parse_ag2(trajectory)
    else:
        return parse_generic(trajectory)



STATEFUL_TOOL_PATTERNS = [
    (re.compile(r"(.*)_get$|^get_(.*)$"), "read", "memory"),
    (re.compile(r"(.*)_set$|^set_(.*)$"), "write", "memory"),
    (re.compile(r"(.*)_read$|^read_(.*)$"), "read", "memory"),
    (re.compile(r"(.*)_write$|^write_(.*)$"), "write", "memory"),
    (re.compile(r"(.*)_load$|^load_(.*)$"), "read", "memory"),
    (re.compile(r"(.*)_save$|^save_(.*)$"), "write", "memory"),
    (re.compile(r"^update_(.*)$"), "write", "memory"),
    (re.compile(r"^store_(.*)$"), "write", "memory"),
    (re.compile(r"^retrieve_(.*)$"), "read", "memory"),
    (re.compile(r"^edit_(.*)$|^modify_(.*)$"), "write", "memory"),
    (re.compile(r"^view_(.*)$|^inspect_(.*)$"), "read", "memory"),
]


def classify_tool(name: str) -> tuple[str, str] | None:
    nm = (name or "").lower()
    for pat, kind, ns in STATEFUL_TOOL_PATTERNS:
        if pat.match(nm):
            return (kind, ns)
    return None


def extract_slot(args: Any) -> str:
    if isinstance(args, dict):
        for k in ("slot", "key", "name", "id", "path", "file", "topic", "field"):
            if k in args:
                return str(args[k])[:32]
        if args:
            v = next(iter(args.values()))
            if isinstance(v, str):
                return v[:32]
    return "default"


def extract_write_value(args: Any) -> str:
    if isinstance(args, dict):
        for k in ("value", "content", "data", "text", "body", "message"):
            if k in args:
                return str(args[k])[:500]
    return json.dumps(args, default=str)[:500] if args else ""



def events_to_oprecords(events: list[dict], scenario: str,
                        session_id: str) -> list[OpRecord]:
    records: list[OpRecord] = []
    step = 0
    tool_index: dict[str, int] = defaultdict(int)
    call_id_to_cell: dict[str, str] = {}

    current_reads: list[str] = []
    current_read_values: dict[str, str] = {}
    current_writes: list[str] = []
    current_write_values: dict[str, str] = {}
    current_agent: str = "unknown"
    op_index = 0

    def flush_record(agent: str):
        nonlocal step, op_index, current_reads, current_read_values
        nonlocal current_writes, current_write_values
        if not current_reads and not current_writes:
            return
        read_time = step
        step += 1
        write_time = step
        step += 1
        records.append(OpRecord(
            agent_id=agent,
            op_index=op_index,
            read_set=list(current_reads),
            read_values=dict(current_read_values),
            read_time=read_time,
            write_set=list(current_writes),
            write_values=dict(current_write_values),
            write_time=write_time,
            scenario=scenario,
            session_id=session_id,
        ))
        op_index += 1
        current_reads = []
        current_read_values = {}
        current_writes = []
        current_write_values = {}

    for e in events:
        if e["type"] == "agent_turn":
            if current_agent != e["agent"] and (current_reads or current_writes):
                flush_record(current_agent)
            current_agent = e["agent"]

        elif e["type"] == "tool_call":
            tn = e["tool_name"]
            args = e.get("args", {})
            classification = classify_tool(tn)
            args_json = json.dumps(args, default=str)
            if classification is not None:
                kind, ns = classification
                slot = extract_slot(args)
                cell = f"{ns}:{slot}"
                if e.get("call_id"):
                    call_id_to_cell[e["call_id"]] = cell
                if kind == "read":
                    if cell not in current_reads:
                        current_reads.append(cell)
                        current_read_values[cell] = args_json[:500]
                else:
                    if cell not in current_writes:
                        current_writes.append(cell)
                    current_write_values[cell] = extract_write_value(args)
            else:
                idx = tool_index[tn]
                tool_index[tn] += 1
                cell = f"{tn}:{idx}"
                if e.get("call_id"):
                    call_id_to_cell[e["call_id"]] = cell
                if cell not in current_writes:
                    current_writes.append(cell)
                current_write_values[cell] = args_json[:500]

    if current_reads or current_writes:
        flush_record(current_agent)
    return records



def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-id", default="mcemri/MAD")
    parser.add_argument("--filename", default="MAD_sample_19.json")
    parser.add_argument("--out", type=Path,
                        default=Path("../mast_oprecords/"))
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--local-json", type=Path, default=None)
    args = parser.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)

    if args.local_json:
        with open(args.local_json) as f:
            dataset = json.load(f)
    else:
        try:
            from huggingface_hub import hf_hub_download
        except ImportError:
            print("install huggingface_hub", file=sys.stderr)
            sys.exit(1)
        file_path = hf_hub_download(repo_id=args.repo_id,
                                    filename=args.filename,
                                    repo_type="dataset", revision="5a82e32347f70a701a3c68637de12f8a0be3de3c")
        with open(file_path) as f:
            dataset = json.load(f)

    print(f"Loaded {len(dataset)} records.")

    processed = 0
    by_framework: dict[str, int] = defaultdict(int)
    skipped_by_framework: dict[str, int] = defaultdict(int)
    oprecords_by_framework: dict[str, int] = defaultdict(int)

    for idx, record in enumerate(dataset):
        if args.limit is not None and processed >= args.limit:
            break
        framework = record.get("mas_name", "unknown")
        trace = record.get("trace", {})
        trajectory = ""
        if isinstance(trace, dict):
            trajectory = trace.get("trajectory", "")
        elif isinstance(trace, str):
            trajectory = trace
        if not trajectory:
            skipped_by_framework[framework] += 1
            continue

        sid = f"{framework}_{record.get('trace_id', idx)}"
        events = normalize_mast_trace(trajectory, framework)
        if not events:
            skipped_by_framework[framework] += 1
            continue
        oprecs = events_to_oprecords(events, framework.lower(), sid)
        if not oprecs:
            skipped_by_framework[framework] += 1
            continue

        out_path = args.out / f"{framework.lower()}-mast-{idx}.jsonl"
        with open(out_path, "w") as f:
            for r in oprecs:
                f.write(r.to_jsonl() + "\n")

        processed += 1
        by_framework[framework] += 1
        oprecords_by_framework[framework] += len(oprecs)

        if processed <= 5:
            print(f"  [{idx}] {framework} id={sid} events={len(events)} oprecs={len(oprecs)}")

    print(f"\nProcessed: {processed}")
    print(f"Output dir: {args.out}")
    print(f"\nPer framework:")
    print(f"  {'framework':14} {'processed':>10} {'skipped':>10} {'oprecs':>10}")
    all_fws = set(by_framework) | set(skipped_by_framework)
    for fw in sorted(all_fws):
        print(f"  {fw:14} {by_framework[fw]:>10} {skipped_by_framework[fw]:>10} {oprecords_by_framework[fw]:>10}")
    print(f"\nNow run: python analyze_production.py {args.out} --out mast_rates.json")


if __name__ == "__main__":
    main()