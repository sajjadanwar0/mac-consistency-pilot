#!/usr/bin/env python3
"""verify_ssi_residual.py -- audit the SSI-triage residual A1 flags.

The live baseline (analyse_real_llm.py) reports SSI at 3% A1 on triage,
0% elsewhere. A verified SSI runtime prevents A1, so any residual flag is
either (a) a detector over-approximation on a malformed agent trace, or
(b) a genuine prevention escape (which would contradict the verified
theorem and must be investigated). This script classifies each flag.

A flag is a PROTOCOL-DEVIATION FALSE POSITIVE iff the same agent wrote the
flagged cell more than once in the session (the agent went off-protocol,
double-writing a shared cell), AND the consuming read observed one of the
agent's own written values (i.e. no stale-past-a-concurrent-commit
occurred -- the read got a value the writer actually produced). Under SSI
that is the detector firing on the agent's self-inconsistency, not an SSI
escape.

Exit 0 and print PASS iff every residual flag is a protocol-deviation
false positive; exit 1 and print the offending trace otherwise.
"""
import glob, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from detectors import detect_a1, load_trace

def main():
    base = sys.argv[1] if len(sys.argv) > 1 else "baseline_runs/2026-05-10"
    ssi_triage = sorted(glob.glob(f"{base}/snapshot_isolation/triage/*.jsonl"))
    if not ssi_triage:
        sys.exit(f"no SSI triage traces under {base}")
    flagged = []
    for f in ssi_triage:
        recs = load_trace(Path(f))
        hit = detect_a1(recs)
        if hit:
            flagged.append((Path(f).name, hit, recs))
    print(f"SSI/triage: {len(ssi_triage)} sessions, {len(flagged)} A1-flagged")
    real_escapes = []
    for name, hit, recs in flagged:
        i, j, cell = hit
        # how many writes to `cell`, and by how many distinct agents?
        writers = [(r.get("agent"), r.get("write_values", {}).get(cell))
                   for r in recs if cell in r.get("write_set", [])]
        distinct_agents = {a for a, _ in writers}
        n_writes = len(writers)
        # the consuming read's value for `cell`
        read_val = recs[i].get("read_values", {}).get(cell)
        written_vals = {v for _, v in writers}
        read_matches_a_written_value = read_val in written_vals
        deviation = (n_writes > 1 and len(distinct_agents) == 1)
        verdict = ("PROTOCOL-DEVIATION FP" if deviation and read_matches_a_written_value
                   else "REAL ESCAPE -- INVESTIGATE")
        print(f"  {name}: cell={cell} writes={n_writes} "
              f"distinct_writers={len(distinct_agents)} "
              f"read_value_was_written={read_matches_a_written_value} -> {verdict}")
        if verdict.startswith("REAL"):
            real_escapes.append(name)
    print()
    if real_escapes:
        print(f"FAIL: {len(real_escapes)} genuine SSI escape(s): {real_escapes}")
        print("This would contradict the verified A1-prevention theorem; "
              "investigate the executable SSI runtime before any claim.")
        sys.exit(1)
    print(f"PASS: all {len(flagged)} SSI/triage residual flags are "
          f"protocol-deviation false positives (single agent double-wrote "
          f"the shared cell; the consuming read observed a written value, "
          f"so no stale-past-commit occurred). The verified A1-prevention "
          f"theorem is not contradicted; the residual is the deterministic-"
          f"detector over-approximation of Sec 4.5.")

if __name__ == "__main__":
    main()