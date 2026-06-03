"""
Run the four detectors against each runtime's traces, report:
  * Per-runtime level distribution (count and fraction)
  * 95% bootstrap CIs on each fraction
  * Aborted-op count (from runner metadata)

Output is a paper-ready Markdown table plus the underlying CSV.
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


def bootstrap_ci(samples: list[int], target: int, n_boot: int = 1000, alpha: float = 0.05) -> tuple[float, float]:
    """Return (lo, hi) 1-alpha CI for the fraction of samples equal to target."""
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


def analyse_runtime(runtime_dir: Path) -> dict:
    trace_files = sorted(runtime_dir.glob("trace-*.jsonl"))
    levels = []
    for tf in trace_files:
        try:
            records = load_trace(tf)
        except Exception as e:
            print(f"  warning: failed to read {tf}: {e}")
            continue
        levels.append(classify_level(records))

    counts = {n: levels.count(n) for n in range(5)}
    fractions = {n: counts[n] / len(levels) if levels else 0.0 for n in range(5)}

    cis = {n: bootstrap_ci(levels, target=n) for n in range(5)}

    metadata = {}
    meta_path = runtime_dir / "_metadata.json"
    if meta_path.exists():
        metadata = json.loads(meta_path.read_text())

    return {
        "runtime": runtime_dir.name,
        "n_traces": len(levels),
        "counts": counts,
        "fractions": fractions,
        "cis": cis,
        "aborts": metadata.get("total_aborts", 0),
    }


def render_markdown(results: list[dict]) -> str:
    """Compact paper-ready table."""
    out = []
    out.append("| Runtime | $L_0$ ($A_1$) | $L_1$ ($A_3$) | $L_2$ ($A_6$) | $L_3$ ($A_2$) | $L_4$ (clean) | Aborts |")
    out.append("|---|---|---|---|---|---|---|")
    for r in results:
        cells = []
        for n in range(5):
            f = r["fractions"][n]
            lo, hi = r["cis"][n]
            cells.append(f"{f*100:.1f}% [{lo*100:.1f}, {hi*100:.1f}]")
        cells.append(str(r["aborts"]))
        out.append(f"| {r['runtime']} | " + " | ".join(cells) + " |")
    return "\n".join(out)


def render_latex(results: list[dict]) -> str:
    out = []
    out.append("\\begin{table}[t]")
    out.append("\\centering")
    out.append("\\caption{Comparative level distribution across three synthetic runtimes")
    out.append("(700 traces each, scenarios drawn uniformly at random with the same seed).")
    out.append("Each cell is fraction at level (95\\,\\% bootstrap CI). Aborts are commits")
    out.append("rejected by the runtime (no \\fld{OpRecord} emitted).}")
    out.append("\\label{tab:baseline}")
    out.append("\\small")
    out.append("\\begin{tabular}{lcccccc}")
    out.append("\\toprule")
    out.append("Runtime & $L_0$ & $L_1$ & $L_2$ & $L_3$ & $L_4$ & Aborts \\\\")
    out.append("\\midrule")
    label = {
        "vanilla": "Vanilla (uninstrumented control)",
        "pessimistic": "Pessimistic locking",
        "snapshot_isolation": "Snapshot isolation",
    }
    for r in results:
        cells = []
        for n in range(5):
            f = r["fractions"][n]
            lo, hi = r["cis"][n]
            cells.append(f"{f*100:.1f}\\% [{lo*100:.1f}, {hi*100:.1f}]")
        cells.append(str(r["aborts"]))
        name = label.get(r["runtime"], r["runtime"])
        out.append(f"{name} & " + " & ".join(cells) + " \\\\")
    out.append("\\bottomrule")
    out.append("\\end{tabular}")
    out.append("\\end{table}")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input",
        type=Path,
        default=HERE / "synthetic_traces",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=HERE / "synthetic_results",
    )
    args = parser.parse_args()

    args.output.mkdir(parents=True, exist_ok=True)
    runtime_dirs = sorted(d for d in args.input.iterdir() if d.is_dir())

    results = []
    for d in runtime_dirs:
        print(f"Analyzing {d.name}...", flush=True)
        r = analyse_runtime(d)
        results.append(r)
        print(
            f"  {r['runtime']}: counts={r['counts']}, aborts={r['aborts']}"
        )

    md = render_markdown(results)
    (args.output / "table.md").write_text(md)
    print()
    print(md)
    print()

    tex = render_latex(results)
    (args.output / "table.tex").write_text(tex)

    (args.output / "raw.json").write_text(
        json.dumps(
            [
                {
                    "runtime": r["runtime"],
                    "counts": r["counts"],
                    "fractions": r["fractions"],
                    "cis": {str(k): list(v) for k, v in r["cis"].items()},
                    "aborts": r["aborts"],
                    "n_traces": r["n_traces"],
                }
                for r in results
            ],
            indent=2,
        )
    )

    print(f"Wrote {args.output}/{{table.md,table.tex,raw.json}}")


if __name__ == "__main__":
    main()
