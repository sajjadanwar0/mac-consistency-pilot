#!/usr/bin/env bash
#
# Real-LLM baseline run protocol (corrected for python/baselines layout).
set -euo pipefail

PROJECT_ROOT="${PROJECT_ROOT:-$HOME/RustroverProjects/mac-consistency-pilot}"
BASELINES_DIR="$PROJECT_ROOT/python/baselines"
OUTDIR="${OUTDIR:-$PROJECT_ROOT/baseline_runs/$(date +%Y-%m-%d)}"

N_PER_WORKLOAD="${N_PER_WORKLOAD:-100}"
RUNTIMES=("vanilla" "pessimistic" "snapshot_isolation")
WORKLOADS=("edit-review" "plan-execute" "triage")

if [[ -z "${OPENAI_API_KEY:-}" ]]; then
    echo "ERROR: OPENAI_API_KEY not set" >&2
    exit 2
fi
if [[ ! -f "$PROJECT_ROOT/python/autogen_pilot.py" ]]; then
    echo "ERROR: $PROJECT_ROOT/python/autogen_pilot.py not found" >&2
    exit 2
fi
if [[ ! -d "$BASELINES_DIR/runtimes" ]]; then
    echo "ERROR: $BASELINES_DIR/runtimes/ not found" >&2
    exit 2
fi

mkdir -p "$OUTDIR"
echo "Output: $OUTDIR"
echo "Runtimes: ${RUNTIMES[*]}"
echo "Workloads: ${WORKLOADS[*]}"
echo "N per cell: $N_PER_WORKLOAD"
echo

TOTAL_SESSIONS=$((${#RUNTIMES[@]} * ${#WORKLOADS[@]} * N_PER_WORKLOAD))
echo "Total sessions: $TOTAL_SESSIONS"
echo "Estimated cost (gpt-4o, ~$0.0175/session): \$$(echo "scale=2; $TOTAL_SESSIONS * 0.0175" | bc)"
echo

read -rp "Proceed? [y/N] " yn
if [[ "$yn" != "y" && "$yn" != "Y" ]]; then
    echo "Aborted."
    exit 0
fi

START="$(date +%s)"
for runtime in "${RUNTIMES[@]}"; do
    for workload in "${WORKLOADS[@]}"; do
        cell_dir="$OUTDIR/$runtime/$workload"
        mkdir -p "$cell_dir"

        if [[ -f "$cell_dir/.complete" ]]; then
            echo "[skip] $runtime/$workload already done"
            continue
        fi

        echo "[run] $runtime/$workload ..."

        cd "$PROJECT_ROOT/python"
        uv run python autogen_pilot.py \
            --runtime "$runtime" \
            --workload "$workload" \
            --n "$N_PER_WORKLOAD" \
            --output "$cell_dir" \
            --seed "$(date +%s%N | tail -c 6)" \
            2>&1 | tee "$cell_dir/run.log"

        touch "$cell_dir/.complete"
        ELAPSED="$(( $(date +%s) - START ))"
        echo "  cumulative wall-clock: ${ELAPSED}s"
    done
done

echo
echo "[analyse] running detectors..."
cd "$PROJECT_ROOT/python"
uv run python baselines/analyse_real_llm.py \
    --input "$OUTDIR" \
    --output "$OUTDIR/_results"

echo
echo "Done. Results: $OUTDIR/_results/"
echo "Inspect $OUTDIR/_results/comparative_table.md"
