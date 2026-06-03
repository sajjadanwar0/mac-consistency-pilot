# Baseline Runtimes and Case-Study Protocol

This bundle implements the work described in §6.2 (limitations: no
baseline comparison) and §6.4 (illustrative discussion → real case
study) of paper_v4_6.tex.

## What's in this bundle

| File | Purpose |
|---|---|
| `runtimes/pessimistic.py` | Per-cell + per-tool locking runtime |
| `runtimes/snapshot_isolation.py` | MVCC + commit-time read-set validation |
| `detectors.py` | Python port of the four Verus-verified detectors |
| `runner.py` | Drives prompts.json scenarios through all three runtimes |
| `analyse.py` | Bootstrap-CI analysis of synthetic baseline traces |
| `analyse_real_llm.py` | Comparative analysis for real-LLM baseline runs |
| `scripts/run_real_llm_baselines.sh` | Lightsail protocol script |
| `AUTOGEN_INTEGRATION.md` | Patch instructions for autogen_pilot.py |
| `case_study/PROTOCOL.md` | 6-week case-study protocol with PR template |
| `synthetic_results/table.{md,tex}` | Synthetic baseline results (already run) |

## Synthetic baseline results (already run in this bundle)

700 scenarios per runtime, 95% bootstrap CIs:

| Runtime | $L_0$ ($A_1$) | $L_3$ ($A_2$) | $L_4$ (clean) | Aborts |
|---|---|---|---|---|
| Vanilla | 20.7% [18.0, 23.6] | 21.1% [18.3, 24.3] | 58.1% [54.6, 61.6] | 0 |
| Pessimistic | 0.0% [0.0, 0.0] | 0.0% [0.0, 0.0] | 100.0% | 285 |
| Snapshot isolation | 0.0% [0.0, 0.0] | 21.1% [18.3, 24.3] | 78.9% [75.7, 81.7] | 145 |

Interpretation:
- Pessimistic locking prevents both A_1 and A_2 (the registry locking
  prevents tool removal during reservation)
- Snapshot isolation prevents A_1 only (it's a memory protocol; the
  tool registry is unaffected)
- Aborts are the cost: 285 dropped operations under pessimistic
  locking, 145 under SI

The scenarios in prompts.json don't construct A_3 or A_6 directly
(they require trace tampering the current driver doesn't support);
A_3 and A_6 prevention by these runtimes is established by the
Verus completeness proofs, not measured here.

## To run real-LLM baselines on Lightsail

```bash
# 1. Copy this bundle to your Lightsail box
scp -r baselines/ lightsail:~/

# 2. Apply the AutoGen integration patch
# See AUTOGEN_INTEGRATION.md for the exact diff to apply to
# mac-consistency-pilot/python/autogen_pilot.py

# 3. Run the protocol script
export OPENAI_API_KEY=sk-...
bash baselines/scripts/run_real_llm_baselines.sh

# 4. Inspect results
cat baseline_runs/$(date +%Y-%m-%d)/_results/comparative_table.md
```

Estimated: 6-10 hours wall-clock, $30-50 in tokens.

## To start the case study

Read `case_study/PROTOCOL.md`. It identifies AutoGen and LangGraph as
the recommended primary targets and provides:
- Detector deployment recipe per framework
- PR template
- Suggested 6-week timeline (with 2-week fallback)

## Self-check on synthetic baseline numbers

Run from this directory to reproduce:

```bash
python3 runner.py --n 700
python3 analyse.py
```

Should produce identical numbers (seed 42, deterministic).
