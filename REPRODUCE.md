# Reproducing the tables

Every published figure maps to a directory in this tree and a command that
scores it. `./check_tables.sh` scores all of them and exits non-zero on any
disagreement with `expected.json`. It uses python3 only -- no cargo, no
network, no API keys.

```
./check_tables.sh
```

`check_tables.sh` is a second, independent transcription of Definition 1 from
`../mac-consistency/tla/Anomalies.tla:6-13`. It does not call the Verus-verified
`rust-analyser`. Agreement between the two is evidence; a single implementation
scoring itself would not be.

## Map

| Paper | Data | Scored by |
|---|---|---|
| Table 3 (100 / 0 / 42) | `runs/20260913T0424Z/{edit-review,plan-execute,triage}-vanilla/` | `check_tables.sh`; `results.txt` is the rust-analyser output |
| Table 3 caption, further run 1 (52) | `runs/20260913T0128Z/triage-vanilla/` | same |
| Table 3 caption, further run 2 (48) | `runs/20260913T0150Z/triage-vanilla/` -- the Table 4 vanilla cell | same |
| Table 3 caption, pooled (142/300) | the three `triage-vanilla/` cells above | same |
| Table 4 (9 cells) | `runs/20260913T0150Z/<workload>-<runtime>/` | same |
| Table 4 token cost | `runs/20260913T0150Z/tokens-<workload>-<runtime>/` | `python/tokens_capture.py` |
| Table 6, store rows | `python/live_a1_{gpt4omini,haiku,llama}/sessions/store_*.jsonl` | `check_tables.sh` |
| Table 6, superstep rows | `python/live_a1_*/sessions/superstep_*.jsonl` | `check_tables.sh` (completion clock); `results.json` also reports the barrier clock |
| Table 6, material / regenerations / pinned interval | `python/live_a1_*/results.json` | `python/langgraph_live_a1.py` |
| S 5.2, 5.4 synthetic pilot (700 traces) | `python/traces/` | `rust-analyser` |
| S 5.5 baseline comparison | `baseline_runs/` | `python/baselines/analyse_real_llm.py` |
| S 5.6 Finding 5 sweep (155 paired) | `python/hc_curve/`, `python/hc_ceiling/`, `python/hc_s1/` | `python/tokens_capture.py` |
| S 5.7 cookbook (600 sessions) | `production_traces/`, `cookbook_rates_def1.json` | `python/analyze_production.py` |
| S 5.8 corpus projection | `mast_oprecords/`, `python/mast_rates.json` | `python/mast_adapter.py` |
| S 5.8 own-executor racy check | `python/oprecords/`, `python/rates.json` | `python/prevalence_harness.py` -- see the note below |
| S 5.8 topology dynamic confirmation | `python/dynamic_oprecords/`, `python/structural_report.json` | `python/prevalence_dynamic_run.py` |
| S 5.10 wall-clock study | `python/wallclock_results.json` | `python/wallclock_cost_study.py` |
| S 5.12 ToolNode A6 | `python/langgraph_a6_out/`, `python/langgraph_a6_natural/` | `python/langgraph_a6_*.py` |
| S 4.17 sixteen-point matrix | `../mac-consistency/tla/lattice16_results.reference.json` | `../mac-consistency/tla/lattice16.sh` |
| S 4.8 obligation counts | this tree's `verus-detector/src/` | `./verus_count.sh`, `./verus_count.sh --full` |

## Two predicate forms, and which file uses which

Definition 1 requires a strict window: `read_time_i < write_time_j < write_time_i`.
Traces whose records occupy consecutive ticks have width-one windows and the
predicate cannot fire on them regardless of what the agents did.

`python/rates.json` is **not** scored under Definition 1. It reports the
**superstep form** used in Section 5.8 -- a co-superstep write of a different
value by another agent -- because each round of that harness is a single
superstep whose commits land at one tick. Under the superstep form its data
(`python/oprecords/`) gives racy 100/100 and sequential 0/100, which is what
`rates.json` records. Under Definition 1 the same data gives 0/100 and 0/100.
Both numbers are correct for their predicate. Do not read `rates.json` as a
Table 6 figure: Table 6 is `python/live_a1_*/`, a different harness on an
unmodified LangGraph runtime.

## Manifests

`runs/20260913T0424Z/manifest.json` was captured at run time and carries the
detector checksum and the pilot revision the run executed on.

`runs/20260913T0150Z/manifest.json` and `runs/20260913T0128Z/manifest.json` are
**reconstructed**: those runs predate the manifest-writing harness. They carry
`"provenance": "reconstructed"` and state in the file which fields come from the
manuscript rather than from capture. They are not evidence of the run
configuration; the traces are the evidence.

## What is deliberately not in this tree

`python/MAD_*.json*` -- the raw MAST-Data download from HuggingFace
(`mcemri/MAD`, revision `5a82e32`). Large, third-party, and regenerable by
`python/mast_adapter.py`. The derived op-records in `mast_oprecords/` **are**
tracked, so Section 5.8 reproduces without the download.

Numbered `N_*_fix.sh` delivery scripts are process, not artifact.
