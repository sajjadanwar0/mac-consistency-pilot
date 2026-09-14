# Reproducing the tables

Every published figure maps to a directory in this tree and a command that
scores it. `./check_tables.sh` scores all of them, checks that every path named
below exists, and exits non-zero on any disagreement or any dangling path. It
uses python3 only -- no cargo, no network, no API keys.

```
./check_tables.sh
```

`check_tables.sh` is a second, independent transcription of Definition 1 from
`../mac-consistency/tla/Anomalies.tla` lines 6-13. It does not call the
Verus-verified `rust-analyser`. Agreement between the two is evidence; a single
implementation scoring itself would not be.

## Map

| Paper | Data | Scored by |
|---|---|---|
| Table 3 (100 / 0 / 42) | `runs/20260913T0424Z/` | `check_tables.sh`; `results.txt` is the rust-analyser output |
| Table 3 caption, further run 1 (52) | `runs/20260913T0128Z/` | same |
| Table 3 caption, further run 2 (48) | `runs/20260913T0150Z/` vanilla cells | same |
| Table 3 caption, pooled (142/300) | the three triage-vanilla cells | same |
| Table 4 (9 cells) | `runs/20260913T0150Z/` | same |
| Table 4 token cost | the `tokens-` cells of the same run | `python/tokens_capture.py` |
| Table 5 (150/200, 43/43, 18/33, 0/100) | `python/cf_triage.jsonl`, `python/cf_trace_edit.jsonl`, `python/cf_trace_triage.jsonl`, `python/cf_edit.jsonl` | `python/counterfactual_reprompt.py` |
| Table 5 blind sample | `python/audit_sheet.csv` | `python/judge_audit.py` |
| Table 6, store rows | `python/live_a1_gpt4omini`, `python/live_a1_haiku`, `python/live_a1_llama` | `check_tables.sh` |
| Table 6, superstep rows | the same directories | `check_tables.sh` (completion clock); `results.json` also reports the barrier clock |
| S 5.2, 5.4 synthetic pilot (700 traces) | `python/traces` | `rust-analyser` |
| S 5.5 baseline comparison | `baseline_runs` | `python/baselines/analyse_real_llm.py` |
| S 5.6 Finding 5 sweep (155 paired) | `python/hc_curve`, `python/hc_ceiling`, `python/hc_s1` | `python/tokens_capture.py` |
| S 5.7 cookbook (600 sessions) | `production_traces`, `cookbook_rates_def1.json` | `python/analyze_production.py` |
| S 5.8 corpus projection | `mast_oprecords`, `python/mast_rates.json` | `python/mast_adapter.py` |
| S 5.8 own-executor racy check | `python/oprecords`, `python/rates.json` | `python/prevalence_harness.py` -- see the predicate note below |
| S 5.8 topology dynamic confirmation | `python/dynamic_oprecords`, `python/structural_report.json` | `python/prevalence_dynamic_run.py` |
| S 5.10 wall-clock study | `python/wallclock_results.json` | `python/wallclock_cost_study.py` |
| S 5.12 ToolNode A6 | `python/langgraph_a6_out`, `python/langgraph_a6_natural` | `python/langgraph_a6_experiment.py`, `python/langgraph_a6_experiment_natural.py`, `python/toolnode_a6_fix.py` |
| S 4.17 sixteen-point matrix | `../mac-consistency/tla/lattice16_results.reference.json` (sibling repo; not gated here) | `../mac-consistency/tla/lattice16.sh` |
| S 4.8 obligation counts | `verus-detector` | `./verus_count.sh`, `./verus_count.sh --full` |

## Two predicate forms, and which file uses which

Definition 1 requires a strict window: `read_time_i < write_time_j < write_time_i`.
Traces whose records occupy consecutive ticks have width-one windows and the
predicate cannot fire on them regardless of what the agents did.

`python/rates.json` is **not** scored under Definition 1. It reports the
**superstep form** used in Section 5.8 -- a co-superstep write of a different
value by another agent -- because each round of that harness is a single
superstep whose commits land at one tick. Under the superstep form its data
(`python/oprecords`) gives racy 100/100 and sequential 0/100, which is what
`rates.json` records. Under Definition 1 the same data gives 0/100 and 0/100.
Both numbers are correct for their predicate. Do not read `rates.json` as a
Table 6 figure: Table 6 is the `python/live_a1_*` directories, a different
harness on an unmodified LangGraph runtime.

Records in `python/oprecords` and `python/dynamic_oprecords` carry the agent
under the key `agent_id`, not `agent`. The detector and `check_tables.sh` alias
it; a third-party scorer that does not will read every agent as null and report
zero.

## Manifests

`runs/20260913T0424Z/manifest.json` was captured at run time and carries the
detector checksum and the pilot revision the run executed on.

The `20260913T0150Z` and `20260913T0128Z` manifests are **reconstructed**: those
runs predate the manifest-writing harness. They carry
`"provenance": "reconstructed"` and state in the file which fields come from the
manuscript rather than from capture. They are not evidence of the run
configuration; the traces are the evidence.

## What is deliberately not in this tree

`python/MAST/` -- the raw MAST corpus as downloaded: 12,961 files, 1,209 MB,
including PDF, WAV, PNG and `.pdb` payloads that no result in this paper reads.
Section 5.8's evidence is the derived op-records in `mast_oprecords` and
`python/mast_oprecords`, both tracked, together with `python/mast_rates.json`.
`python/mast_adapter.py` re-fetches the raw corpus from HuggingFace
(`mcemri/MAD`, revision `5a82e32`).

`python/MAD_*.json*` -- the same download in single-file form.

Numbered `N_*_fix.sh` delivery scripts are process, not artifact.

## Ignore files

`check_ignores.sh` gates that only the root `.gitignore` carries active
rules among the ignore files git honors. Evidence in this repository was
invisible for two rounds because `python/.gitignore` carried two rules
nobody had read. Ignore files inside already-ignored directories (`.idea/`,
`.venv/`, `verus-count-clone/`) are shadowed and are reported as such, not
counted.
| S 6.3 interrupt() probe | `python/interrupt_probe_results.json` | `python/langgraph_interrupt_probe.py` |
| S 6.3 CrewAI shape probe | `python/crewai_shape_results.json` | `python/crewai_shape_probe.py` |
