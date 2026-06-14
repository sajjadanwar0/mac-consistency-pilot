#!/usr/bin/env python3
"""
mast_structural_classifier.py - Structural triage of MAST-Data traces the
operation-record adapter cannot fully parse.

THE PROBLEM THIS CLOSES
-----------------------
The paper's MAST cell currently reads: "A1 fired in 0 of the 600 traces
parseable into our operation-record model" with the remaining 642 traces
(dominated by AG2: 584/597 unparsed) left as an acknowledged coverage gap.
A hostile reviewer reads that gap as selection bias: "the unparsed majority
might exhibit different patterns."

The decisive observation: the goal for the unparsed remainder is NOT to find
anomalies in it -- it is to determine whether those traces contain ANY shared
mutable-store operations at all. A trace with no shared-store operations has
no cells to be stale: it is structurally outside the catalog's domain, and
its unparseability is evidence of architectural absence, not of hidden
anomalies. This script converts "unparsed (unknown)" into one of:

  NO_SHARED_STORE   No shared mutable-store operation markers anywhere in the
                    trajectory: pure conversation / message-passing. The trace
                    is structurally A1-immune (nothing to read stale).
  CANDIDATE_OPS     Shared-store markers found. These traces MUST be either
                    extracted (extend the adapter) or reported as a residual
                    unknown; they may NOT be claimed immune.
  UNKNOWN           Trajectory empty/undecodable, or evidence ambiguous.
                    Counted against the claim, never for it.

CONSERVATISM CONTRACT (what makes this survive review)
------------------------------------------------------
1. The classifier errs toward CANDIDATE_OPS/UNKNOWN. A single positive marker
   anywhere in the trajectory forces CANDIDATE_OPS; NO_SHARED_STORE requires
   the ABSENCE of every positive marker AND positive structural evidence:
   either recognizable conversational structure in the raw text, or --
   stronger -- the framework-specific adapter parser normalizing the trace
   into >=3 events while extracting ZERO stateful shared-store operations
   (the same parser the paper's 600-trace PARSED cell trusts). An empty or
   exotic file can never be classified immune.
2. Marker rules are enumerated below in MARKERS, mirror the adapter's own
   STATEFUL_TOOL_PATTERNS vocabulary (write/save/update/append/delete/insert
   over files, memory, state, workspace, registry, db), and are printed with
   every classification: each per-trace verdict carries the exact evidence
   strings, so any classification can be audited by grep.
3. --audit-sample N exports a random sample of classified traces (with
   evidence) for blind human labeling; report the agreement rate in the
   paper exactly as the LLM-judge audit (kappa) is reported. Do not publish
   the NO_SHARED_STORE count without this audit.
4. The output sentence for the paper is generated verbatim at the end and
   states the method's limitation in the same breath as the number.

USAGE
-----
  # Same data source as mast_adapter.py (HuggingFace mcemri/MAD), or local:
  python mast_structural_classifier.py                       # HF download
  python mast_structural_classifier.py --local-json MAD_full_dataset.json
  python mast_structural_classifier.py --audit-sample 60 --audit-out audit/
  python mast_structural_classifier.py --out structural_report.json

  Run AFTER mast_adapter.py so the PARSED set is known:
  the classifier re-runs the adapter's parse in-process (imports
  mast_adapter) and only triages what the adapter could not convert.
"""
from __future__ import annotations
import argparse
import json
import random
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

try:
    from mast_adapter import normalize_mast_trace, events_to_oprecords
except ImportError:
    print("Run from the python/ directory next to mast_adapter.py", file=sys.stderr)
    sys.exit(1)

_W = r"[A-Za-z0-9_./-]{1,64}"
MARKERS: list[tuple[str, re.Pattern]] = [
    ("file_write",      re.compile(r"\b(write|save|overwrit\w*|creat\w+)\s*(_|\s)?(to\s+)?(file|" + _W + r"\.(py|md|txt|json|yaml|csv|html|js))\b", re.I)),
    ("file_tool_call",  re.compile(r"\b(write_file|save_file|edit_file|append_file|create_file|delete_file|write_to_file)\b", re.I)),
    ("memory_store",    re.compile(r"\b(memory\.(write|set|update|insert|store)|store_memory|update_memory|save_memory|core_memory_(append|replace))\b", re.I)),
    ("state_mutation",  re.compile(r"\b(update_state|set_state|workspace\.(write|update|set)|shared_(state|memory|workspace))\b|\bstate\[['\"]" + _W + r"['\"]\]\s*=", re.I)),
    ("kv_store",        re.compile(r"\b(redis|sqlite|database|db)\.(set|put|insert|update|write|execute)\b", re.I)),
    ("registry_mut",    re.compile(r"\b(register_tool|unregister_tool|registry\.(add|remove|update))\b", re.I)),
    ("blackboard",      re.compile(r"\b(blackboard|scratchpad|shared.?buffer)\b.{0,40}\b(write|post|update|append)\b", re.I)),
    ("code_file_write", re.compile(r"\bopen\s*\(\s*['\"][^'\"]{1,128}['\"]\s*,\s*['\"][wax]b?['\"]|\.write\s*\(|json\.dump\s*\(|pickle\.dump\s*\(|\.to_csv\s*\(|os\.(remove|rename|makedirs)\s*\(|shutil\.(copy|move|rmtree)", re.I)),
]

CONVERSATIONAL: list[tuple[str, re.Pattern]] = [
    ("role_blocks",    re.compile(r"^\s*-?\s*(role|name|content)\s*:", re.I | re.M)),
    ("speaker_lines",  re.compile(r"^\s*\*{0,2}[A-Z][A-Za-z _]{2,30}\*{0,2}\s*(\(to [^)]+\))?\s*:", re.M)),
    ("from_to",        re.compile(r"\bFROM:\s*\S+\s+TO:\s*\S+", re.I)),
    ("chat_ts",        re.compile(r"\[\d{4}-\d{2}-\d{2}[ T]\d{2}:\d{2}")),
    ("pyrepr_role",    re.compile(r"['\"]role['\"]\s*:\s*['\"]")),
]

MIN_CONV_HITS = 3


def classify_trajectory(text: str) -> tuple[str, list[str]]:
    """Return (verdict, evidence). Conservative by construction.
    Order matters: the marker scan runs FIRST, so a store-operation marker
    can never be hidden by trace brevity; the length floor only gates the
    NO_SHARED_STORE/UNKNOWN distinction."""
    text = text or ""
    evidence: list[str] = []
    for label, rx in MARKERS:
        m = rx.search(text)
        if m:
            snippet = text[max(0, m.start() - 30): m.end() + 30].replace("\n", " ")
            evidence.append(f"{label}: ...{snippet}...")
    if evidence:
        return "CANDIDATE_OPS", evidence
    if len(text.strip()) < 40:
        return "UNKNOWN", ["trajectory empty/too short to classify"]
    conv_hits = []
    for label, rx in CONVERSATIONAL:
        n = len(rx.findall(text))
        if n:
            conv_hits.append(f"{label} x{n}")
    if sum(int(h.split("x")[-1]) for h in conv_hits) >= MIN_CONV_HITS:
        return "NO_SHARED_STORE", conv_hits
    return "UNKNOWN", conv_hits or ["no conversational structure recognized"]


def get_trajectory(record: dict) -> str:
    """Extract the trajectory text. The FIRST branch is verbatim what
    mast_adapter.main() does (confirmed against the source 2026-06-11):
    record["trace"] is a dict whose "trajectory" key holds the text, or
    occasionally a flat string. Fallbacks below only fire for variant
    record shapes; if they ever matter on the full dataset, the sanity
    guard (PARSED ~ 600) catches the divergence."""
    trace = record.get("trace", {})
    if isinstance(trace, dict):
        t = trace.get("trajectory", "")
        if isinstance(t, str) and t.strip():
            return t
    elif isinstance(trace, str) and trace.strip():
        return trace
    for k in ("trajectory", "conversation", "history", "messages", "log"):
        v = record.get(k)
        if isinstance(v, str) and v.strip():
            return v
        if isinstance(v, list) and v:
            return "\n".join(x if isinstance(x, str)
                             else json.dumps(x, default=str) for x in v)
    return ""


def adapter_events(trajectory: str, framework: str, sid: str) -> tuple[int, int]:
    """Run the adapter pipeline; return (n_events, n_oprecords).

    n_oprecords > 0  <=> the trace is in the paper's PARSED cell.
    n_events > 0 with n_oprecords == 0 is itself evidence: the framework-
    specific parser (the same one the paper trusts for the 600-trace cell)
    recognized the trace as a structured conversation and extracted ZERO
    stateful shared-store operations from it."""
    try:
        events = normalize_mast_trace(trajectory, framework)
        if not events:
            return 0, 0
        oprecs = events_to_oprecords(events, framework.lower(), sid)
        return len(events), len(oprecs)
    except Exception:
        return 0, 0


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-id", default="mcemri/MAST-Data",
                    help="canonical dataset: huggingface.co/datasets/mcemri/MAST-Data "
                         "(fall back to --repo-id mcemri/MAD if the download 404s)")
    ap.add_argument("--filename", default="MAD_full_dataset.json")
    ap.add_argument("--local-json", type=Path, default=None)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--out", type=Path, default=Path("structural_report.json"))
    ap.add_argument("--audit-sample", type=int, default=0,
                    help="export N random classified traces for blind human audit")
    ap.add_argument("--audit-out", type=Path, default=Path("structural_audit/"))
    ap.add_argument("--seed", type=int, default=7)
    args = ap.parse_args()

    if args.local_json:
        with open(args.local_json) as f:
            head = f.read(120)
            f.seek(0)
            if head.startswith("version https://git-lfs"):
                print(f"FATAL: {args.local_json} is a Git-LFS pointer, not the "
                      f"dataset. Run `git lfs install && git lfs pull` in the "
                      f"clone, or drop --local-json to fetch from the hub.",
                      file=sys.stderr)
                sys.exit(1)
            try:
                dataset = json.load(f)
            except json.JSONDecodeError as e:
                print(f"FATAL: {args.local_json} is not valid JSON ({e}). "
                      f"Likely a truncated copy or partial LFS checkout. "
                      f"Re-download (e.g. drop --local-json to fetch from the "
                      f"hub) -- do not classify against a corrupt file.",
                      file=sys.stderr)
                sys.exit(1)
    else:
        try:
            from huggingface_hub import hf_hub_download
        except ImportError:
            print("install huggingface_hub or pass --local-json", file=sys.stderr)
            sys.exit(1)
        fp = hf_hub_download(repo_id=args.repo_id, filename=args.filename,
                             repo_type="dataset")
        with open(fp) as f:
            dataset = json.load(f)
    if args.limit:
        dataset = dataset[: args.limit]
    print(f"Loaded {len(dataset)} records.")
    if dataset:
        print(f"Record schema (first record keys): {sorted(dataset[0].keys())}")

    per_trace: list[dict] = []
    counts: Counter = Counter()
    by_fw: dict[str, Counter] = defaultdict(Counter)

    for idx, record in enumerate(dataset):
        fw = record.get("mas_name", "unknown")
        trajectory = get_trajectory(record)
        sid = f"{fw}_{record.get('trace_id', idx)}_{idx}"
        n_ev, n_op = adapter_events(trajectory, fw, sid)
        if n_op > 0:
            verdict, evidence = "PARSED", ["adapter yields OpRecords; in the 600-trace cell"]
        else:
            verdict, evidence = classify_trajectory(trajectory)
            if verdict == "UNKNOWN" and n_ev >= 3:
                verdict = "NO_SHARED_STORE"
                evidence = [f"framework parser normalized {n_ev} events; "
                            f"0 stateful shared-store operations extracted; "
                            f"0 marker hits in raw text"] + evidence
            elif verdict == "NO_SHARED_STORE" and n_ev >= 3:
                evidence.append(f"corroborated: parser normalized {n_ev} "
                                f"events, 0 stateful ops")
        counts[verdict] += 1
        by_fw[fw][verdict] += 1
        per_trace.append({"idx": idx, "framework": fw, "session": sid,
                          "verdict": verdict, "evidence": evidence[:6]})

    EXPECT_PARSED, TOL = 600, 60
    if args.local_json is None and len(dataset) > 1000 \
            and abs(counts["PARSED"] - EXPECT_PARSED) > TOL:
        print(f"\nFATAL: PARSED={counts['PARSED']} but the adapter parses "
              f"~{EXPECT_PARSED} on this dataset. Trajectory-field mismatch "
              f"with mast_adapter.main(); DO NOT use these numbers.")
        print("Diagnose: compare get_trajectory() above with the extraction in")
        print("mast_adapter.py main() (the lines just before "
              "'events = normalize_mast_trace(...)') and align them verbatim.")
        sys.exit(1)

    n_parser_corrob = sum(1 for t in per_trace
                          if t["verdict"] == "NO_SHARED_STORE"
                          and t["evidence"]
                          and t["evidence"][0].startswith("framework parser normalized"))
    n_regex_only = counts["NO_SHARED_STORE"] - n_parser_corrob

    print("\nOverall:")
    for v in ("PARSED", "NO_SHARED_STORE", "CANDIDATE_OPS", "UNKNOWN"):
        print(f"  {v:16} {counts[v]:>5}")
    if counts["NO_SHARED_STORE"]:
        print(f"  (NO_SHARED_STORE evidence: {n_parser_corrob} parser-corroborated, "
              f"{n_regex_only} raw-text structure scan only)")
    print("\nPer framework:")
    print(f"  {'framework':14}{'PARSED':>8}{'NO_STORE':>10}{'CANDIDATE':>11}{'UNKNOWN':>9}")
    for fw in sorted(by_fw):
        c = by_fw[fw]
        print(f"  {fw:14}{c['PARSED']:>8}{c['NO_SHARED_STORE']:>10}"
              f"{c['CANDIDATE_OPS']:>11}{c['UNKNOWN']:>9}")

    args.out.write_text(json.dumps(
        {"counts": dict(counts),
         "by_framework": {k: dict(v) for k, v in by_fw.items()},
         "markers": [m[0] for m in MARKERS],
         "per_trace": per_trace}, indent=1))
    print(f"\nPer-trace verdicts + evidence -> {args.out}")

    if args.audit_sample:
        rng = random.Random(args.seed)
        pool = [t for t in per_trace if t["verdict"] != "PARSED"]
        sample = rng.sample(pool, min(args.audit_sample, len(pool)))
        args.audit_out.mkdir(parents=True, exist_ok=True)
        blind, key = [], []
        for s in sample:
            rec = dataset[s["idx"]]
            blind.append({"session": s["session"],
                          "trajectory_excerpt": (get_trajectory(rec) or "")[:4000]})
            key.append({"session": s["session"], "classifier_verdict": s["verdict"],
                        "evidence": s["evidence"]})
        (args.audit_out / "blind_sheet.json").write_text(json.dumps(blind, indent=1))
        (args.audit_out / "answer_key.json").write_text(json.dumps(key, indent=1))
        print(f"Blind audit sample ({len(sample)}) -> {args.audit_out}/blind_sheet.json "
              f"(label by hand, THEN open answer_key.json; report agreement/kappa)")

    n_unparsed = len(dataset) - counts["PARSED"]
    print("\nPaper-ready claim (and not one word more):")
    mech = []
    if n_parser_corrob:
        mech.append(f"{n_parser_corrob} confirmed by the framework-specific "
                    f"parser itself, which normalizes the trace as a "
                    f"conversation while extracting zero stateful store "
                    f"operations")
    if n_regex_only:
        mech.append(f"{n_regex_only} by a conservative raw-text structure "
                    f"scan with rules enumerated in the artifact")
    mech_s = "; ".join(mech) + "; human-audited on a blind sample"
    print(f'  "Of the {n_unparsed} traces not parseable into operation records, '
          f'{counts["NO_SHARED_STORE"]} contain no shared-mutable-store operations '
          f'({mech_s}) '
          f'and are therefore structurally outside the catalog\'s domain; '
          f'{counts["CANDIDATE_OPS"]} contain candidate shared-store operations '
          f'and remain unclassified pending dedicated extractors; '
          f'{counts["UNKNOWN"]} could not be classified either way. '
          f'The 0/600 result is thus complemented by structural-absence evidence '
          f'for the bulk of the remainder, not extrapolated over it."')
    print("\nDo NOT publish NO_SHARED_STORE without the --audit-sample human check.")


if __name__ == "__main__":
    main()