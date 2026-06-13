"""
Comparative analyser for real-LLM baseline runs.

Expected input directory structure (produced by run_real_llm_baselines.sh):
  $INPUT/{vanilla,pessimistic,snapshot_isolation}/{edit-review,plan-execute,triage}/sess-NNNN.jsonl

Output:
  $OUTPUT/comparative_table.md   — paper-ready Markdown
  $OUTPUT/comparative_table.tex  — LaTeX with bootstrap CIs
  $OUTPUT/raw.json               — full per-cell stats

Each cell of the comparative table is the fraction of sessions that
fall to L_0 (i.e., A_1 fired), with 95% bootstrap CI.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent.resolve()
sys.path.insert(0, str(HERE))

from detectors import classify_level, load_trace


RUNTIMES = ["vanilla", "pessimistic", "snapshot_isolation"]
WORKLOADS = ["edit-review", "plan-execute", "triage"]


def bootstrap_ci(samples: list[int], target: int, n_boot: int = 1000, alpha: float = 0.05) -> tuple[float, float]:
    n = len(samples)
    if n == 0:
        return (0.0, 0.0)
    rng = random.Random(0xBEEF)
    fractions: list[float] = []
    for _ in range(n_boot):
        boot = [samples[rng.randrange(n)] for _ in range(n)]
        fractions.append(sum(1 for x in boot if x == target) / n)
    fractions.sort()
    lo_idx = int(n_boot * alpha / 2)
    hi_idx = int(n_boot * (1 - alpha / 2))
    return (fractions[lo_idx], fractions[hi_idx - 1])


def analyse_cell(cell_dir: Path) -> dict:
    if not cell_dir.is_dir():
        return {"levels": [], "n": 0, "missing": True}
    trace_files = sorted(cell_dir.glob("*.jsonl"))
    levels = []
    for tf in trace_files:
        try:
            records = load_trace(tf)
        except Exception as e:
            print(f"  warning: {tf}: {e}", file=sys.stderr)
            continue
        levels.append(classify_level(records))
    return {"levels": levels, "n": len(levels), "missing": False}


def render_markdown(grid: dict[str, dict[str, dict]]) -> str:
    """Print rates of A_1 firing (L_0) per (runtime, workload) cell."""
    out = []
    out.append("## A_1 (stale-generation) firing rate by runtime × workload")
    out.append("")
    out.append("| Runtime | edit-review | plan-execute | triage |")
    out.append("|---|---|---|---|")
    for rt in RUNTIMES:
        cells = []
        for wl in WORKLOADS:
            cell = grid.get(rt, {}).get(wl, {"missing": True})
            if cell.get("missing", False) or cell["n"] == 0:
                cells.append("---")
                continue
            n = cell["n"]
            levels = cell["levels"]
            a1_rate = sum(1 for l in levels if l == 0) / n
            lo, hi = bootstrap_ci(levels, 0)
            cells.append(f"{a1_rate*100:.1f}% [{lo*100:.1f}, {hi*100:.1f}]")
        out.append(f"| {rt} | " + " | ".join(cells) + " |")

    out.append("")
    out.append("## Full level distribution per cell")
    out.append("")
    out.append("| Runtime | Workload | $L_0$ | $L_1$ | $L_2$ | $L_3$ | $L_4$ | n |")
    out.append("|---|---|---|---|---|---|---|---|")
    for rt in RUNTIMES:
        for wl in WORKLOADS:
            cell = grid.get(rt, {}).get(wl, {"missing": True})
            if cell.get("missing", False) or cell["n"] == 0:
                out.append(f"| {rt} | {wl} | --- | --- | --- | --- | --- | 0 |")
                continue
            counts = {n: cell["levels"].count(n) for n in range(5)}
            out.append(
                f"| {rt} | {wl} | "
                + " | ".join(f"{counts[n]}" for n in range(5))
                + f" | {cell['n']} |"
            )

    return "\n".join(out)


def render_latex(grid: dict[str, dict[str, dict]]) -> str:
    out = []
    out.append("\\begin{table}[t]")
    out.append("\\centering")
    out.append("\\caption{$A_1$ firing rate (\\%) across runtime $\\times$ workload (95\\,\\% bootstrap CI).}")
    out.append("\\label{tab:real-llm-baseline}")
    out.append("\\small")
    out.append("\\begin{tabular}{lccc}")
    out.append("\\toprule")
    out.append("Runtime & edit-review & plan-execute & triage \\\\")
    out.append("\\midrule")
    label = {
        "vanilla": "Vanilla (no instrumentation)",
        "pessimistic": "Pessimistic locking",
        "snapshot_isolation": "Snapshot isolation",
    }
    for rt in RUNTIMES:
        cells = []
        for wl in WORKLOADS:
            cell = grid.get(rt, {}).get(wl, {"missing": True})
            if cell.get("missing", False) or cell["n"] == 0:
                cells.append("---")
                continue
            n = cell["n"]
            levels = cell["levels"]
            a1_rate = sum(1 for l in levels if l == 0) / n
            lo, hi = bootstrap_ci(levels, 0)
            cells.append(f"{a1_rate*100:.1f} [{lo*100:.1f}, {hi*100:.1f}]")
        name = label.get(rt, rt)
        out.append(f"{name} & " + " & ".join(cells) + " \\\\")
    out.append("\\bottomrule")
    out.append("\\end{tabular}")
    out.append("\\end{table}")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    grid: dict[str, dict[str, dict]] = {rt: {} for rt in RUNTIMES}
    for rt in RUNTIMES:
        for wl in WORKLOADS:
            cell_dir = args.input / rt / wl
            grid[rt][wl] = analyse_cell(cell_dir)
            n = grid[rt][wl]["n"]
            print(f"{rt}/{wl}: {n} sessions")

    md = render_markdown(grid)
    (args.output / "comparative_table.md").write_text(md)
    print()
    print(md)

    tex = render_latex(grid)
    (args.output / "comparative_table.tex").write_text(tex)

    raw = {
        rt: {
            wl: {
                "n": grid[rt][wl]["n"],
                "levels": grid[rt][wl]["levels"],
            }
            for wl in WORKLOADS
        }
        for rt in RUNTIMES
    }
    (args.output / "raw.json").write_text(json.dumps(raw, indent=2))
    print(f"\nWrote {args.output}/{{comparative_table.md,comparative_table.tex,raw.json}}")


if __name__ == "__main__":
    main()