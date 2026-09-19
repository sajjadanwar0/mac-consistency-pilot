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
| S 5.6 Figure 2 and its statistics | `python/hc_curve`, `python/hc_ceiling` | `python3 python/fig_cost_envelope.py --stats-only` (add `--out FILE` for the figure; needs matplotlib) |
| S 5.7 cookbook (600 sessions) | `production_traces`, `cookbook_rates_def1.json` | `python/analyze_production.py` |
| S 5.8 corpus projection | `mast_oprecords`, `python/mast_rates.json` | `python/mast_adapter.py` |
| S 5.8 own-executor racy check | `python/oprecords`, `python/rates.json` | `python/prevalence_harness.py` -- see the predicate note below |
| S 5.8 topological susceptibility (k of N) | `python/prevalence_static.py` | `python3 python/prevalence_static.py` |
| S 5.8 census of public LangGraph repositories (stated frame, seeded sample, all 180 sampled repositories read by streaming, static front end; no third-party code is imported or run) | `python/langgraph_census/frame.json`, `python/langgraph_census/sample.json`, `python/langgraph_census/graphs.jsonl`, `python/langgraph_census/summary.json` | `python3 python/langgraph_census.py --check` and `--selftest` (offline); `python3 python/langgraph_static.py --selftest`; `python3 python/langgraph_static.py --oracle` (exit 0 static equals executed, 1 a disagreement, 2 langgraph not importable here, 3 a fixture could not be executed); `python3 python/langgraph_census.py --refetch 10` (network: pinned commits must give the same facts); the network modes `--frame` and `--sample` need `--out DIR` and refuse the tracked directory |
| S 5.8 extraction precision (what a real front end recovers) | `python/langgraph_extract.py` | `python3 python/langgraph_extract.py` (needs langgraph) |
| S 4.8 L1 refinement, simulation check | `verus-detector/src/lib_ssi.rs`, `verus-detector/src/lib_si_concurrent.rs` | `python3 python/l1_refinement_mock.py` |
| S 4.8 L1 invariant (inductiveness) | `verus-detector/src/lib_ssi.rs`, `verus-detector/src/lib_si_concurrent.rs` | `python3 python/l1_invariant_mock.py` |
| S 5.5 task utility (complete AND clean) | `runs/` | `python3 python/task_utility.py` |
| S 5.3 witness classes (cold-start vs supersession) | `runs/`, `python/live_a1_*` | `python3 python/witness_classes.py` |
| S 5.8 corpus instrument | `python/prevalence_corpus.py` | `python3 python/prevalence_corpus.py --provider ... --model ...` (needs a key; `prevalence_harness.instrument_layered` is exercised offline by `langgraph_extract.py`) |
| S 5.8 topology dynamic confirmation | `python/dynamic_oprecords` | `python/prevalence_dynamic_run.py` -- see the predicate note below |
| S 6.3 interrupt() probe | `python/interrupt_probe_results.json` | `python/langgraph_interrupt_probe.py` |
| S 6.3 CrewAI shape probe | `python/crewai_shape_results.json` | `python/crewai_shape_probe.py` |
| predicate cross-check, all three forms | `python/dynamic_oprecords`, `python/oprecords`, `python/mast_oprecords` | `python3 python/predicate_matrix.py` |
| S 5.6 Finding 6, Table 5 (price per sound commit) | `runs/20260913T0150Z` | `python3 python/workcost.py`; `python3 python/realstore_metrics.py --metric usd --tex` must print the same body |
| S 5.10 wall-clock on the REAL stores (1,800 committed sessions, no new inference) | `runs/20260913T0150Z`, `pilot_tokens_claude`, `python/realstore_wallclock.json` | `python3 python/realstore_metrics.py --check` (recomputes and compares); `python3 python/realstore_metrics.py` prints the tables |
| S 5.10 injected-abort sensitivity study (aborts injected at fixed 0.20 / 0.05, the stores do not run) | `python/wallclock_results.json` | `python/wallclock_cost_study.py` |
| S 5.12 ToolNode A6 | `python/langgraph_a6_out`, `python/langgraph_a6_natural` | `python/langgraph_a6_experiment.py`, `python/langgraph_a6_experiment_natural.py`, `python/toolnode_a6_fix.py` |
| S 4.17 sixteen-point matrix | `../mac-consistency/tla/lattice16_results.reference.json` (sibling repo; not gated here) | `../mac-consistency/tla/lattice16.sh` |
| S 4.8 obligation counts | `verus-detector` | `./verus_count.sh`, `./verus_count.sh --full`; the Verus build is pinned in `verus-detector/verus-version.txt` |

## Three predicate forms, and which file uses which

`python/predicate_matrix.py` scores every committed op-record directory under
all three at once and prints them side by side; run it rather than comparing
numbers across sections by hand.

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

`python/fig_cost_envelope.py` reports the accounting identity that governs
the Finding 5 sweep, and separates it from what the sweep measures. In all
155 SSI sessions `generations == W*depth + aborts`, and in all 155 vanilla
and 155 pessimistic ones `generations == W*depth`; the realized abort rate
is therefore extra generations per baseline generation, and regressing
token overhead on it recovers one quantity only -- the price of a retried
generation relative to a first-attempt one. `--stats-only` prints the
identity check alongside the four quantities the identity does not force.

`python/langgraph_extract.py` answers a question `prevalence_static.py`
cannot: what does the same structural predicate return when its inputs come
from a compiled `StateGraph` instead of from a hand encoding? It reports a
2x2 precision matrix over declared and extracted read and write sets. On the
appendix's discriminating pair the encoded verdict is 1 of 4 susceptible and
every other cell of the matrix is 3 of 4, so precision on BOTH sides is
load-bearing. LangGraph 1.2 supplies neither by default; a per-node
`input_schema` on `add_node` does narrow the read set, but there is no
per-node output schema and `ChannelWrite` carries `static=None`, so the write
set is not recoverable at any annotation effort. Read the k-of-N bound with
that scope attached.

The obligation totals are measured against a SPECIFIC Verus build, recorded
in `verus-detector/verus-version.txt`. This is not bookkeeping. `vstd`'s API
moves between releases, and a newer verifier makes proof files stop
*compiling* rather than makes a proof fail -- which `verus_count.sh` reports
as "no verification summary" with no indication that the toolchain is the
cause. Measured on 2026-09-14 at revision `c55901bd`, with the tree
byte-identical: the pinned build gives 331 curated / 352 full, 0 errors;
Verus 0.2026.09.13 gives 148 / 169 with ten files failing to compile,
including `lib_ssi.rs`, `lib_consistency_lattice.rs` and `lib_l2_exec.rs`.
`verus_count.sh` now compares `$VERUS --version` against the pin and refuses
to present a total from a mismatched build as the paper's figure.

`python/l1_invariant_mock.py` answers the question that comes after it. A
Verus refinement needs an invariant Inv on the concrete state that (I1) holds
initially, (I2) is preserved from ANY Inv-state and not merely from reachable
ones, and (I3) implies `all_invariants` of the abstract state under alpha.
(I2) is what sinks such proofs: an invariant true on every reachable state but
not inductive is unprovable by induction, because the step obligation is
discharged from Inv alone with no reachability to lean on. The tool checks
both: (I3) holds over 89,759 Inv-states and (I2) over 520,008 transitions out
of arbitrary Inv-states, with zero violations in each.

It also reports which conjuncts do work. Three of `SiStore::inv`'s four are
load-bearing -- `trace_times` discharges `inv_clock_monotone` and
`inv_record_writetime_le_clock`, `link` discharges `inv_last_write_dominates`,
and `!a1_struct` discharges `inv_no_intervening_write`. `versions_le_clock`
does not: nothing in `all_invariants` bounds `last_write` by the clock, and
(I2) survives without it. And one conjunct that `SiStore::inv` cannot state,
because `SiStore` does not hold the snapshots, is required: every outstanding
snapshot's read time must be at or below the clock, or
`inv_pending_read_time_le_clock` fails under alpha.

`python/l1_refinement_mock.py` answers the question that comes before the
open refinement of Section 4.8: is the theorem true, and under what
hypotheses? It transcribes the abstract SSI machine and the deployed
concurrent store from their sources and checks simulation exhaustively. Over
506,880 transitions in four configurations there are zero counterexamples for
begin, for a successful commit and for a validation abort. Every failure is
the concrete store's guard refusal, and the guard is reachable only at the
clock ceiling -- `read_time > clock` never occurs, because `begin_step` sets
the read time to the clock and the clock is monotone. So the theorem holds
under two hypotheses: the snapshot came from `begin_step` on this store, and
`clock < u64::MAX`. Two limits are structural and no abstraction function
removes them: the concrete `Rec` carries no values, so the target is the
value-erased abstract machine; and the concrete side of the relation is
(`SiStore`, outstanding snapshots), because `pending` lives in the abstract
state and not in `SiStore`. This is a bounded check, not a proof.

`python/task_utility.py` scores what prevention costs in WORK rather than in
tokens. For every cell it reports `clean` (no Definition-1 witness),
`complete` (every role that commits in the unguarded cell of the same run also
commits here) and `both`. `complete` is a structural proxy, not a judgment
that the task succeeded. The divergence is the point: on edit-review,
pessimistic locking is clean in 100 of 100 sessions and complete in 1;
default-SI is clean in 95 and complete in 5, and those 5 are exactly the 5
that fired, so the reviewer's contribution reaches the log if and only if it
is stale. On triage, default-SI is complete-and-clean in 45 of 100 against the
unguarded baseline's 52. Read a prevention claim against `both`.

`python/witness_classes.py` splits every committed Definition-1 witness into
the two classes the predicate does not distinguish. COLD-START: the read value
was the store's initial sentinel, so the reader reached the cell before anyone
wrote it. SUPERSESSION: the read value was written by another agent and a
concurrent write superseded it -- the phenomenon the paper's narrative
describes. The committed datasets are not alike. Across `runs/` the synthetic
pilot's 485 witnesses are 94.2% cold-start, and every one of the 300
edit-review-vanilla witnesses is cold-start. Across `python/live_a1_*` the
live study's 292 witnesses are 100% supersession. The tool also separates
three different reasons a dataset can show no witness at all -- no operation
records, width-one windows, or a window that was open and did not fire -- and
names which cells fall where, because pooling them reads as one result.

Two further facts fall out of running the same four graphs rather than only
reading them, and both are reported by `python/langgraph_extract.py`.

First, **LangGraph refuses to execute the encoded susceptible shape.** Two
co-superstep nodes writing one non-reducer channel raise
`InvalidUpdateError: At key '...': Can receive only one value per step`, from
`LastValue.update`. Of the four graphs, three execute and the one the encoding
calls susceptible does not. Every one of the six susceptible topologies in
`prevalence_static.py` has two or more co-layer writers on the flagged cell,
so all six are in that class. A reader sharing a channel with a SINGLE
co-superstep writer does run, and that is the deployable shape the live study
measures.

Second, **one instrumented run recovers the write set exactly.** It matched
the declared write sets in 3 of the 3 runnable graphs. The write set is the
input static extraction cannot supply, and a node's update dict is that write
set, which is why `prevalence_corpus.py` wraps nodes with
`prevalence_harness.instrument_layered` rather than reading the compiled
object. `instrument_layered` derives each node's superstep from the graph's
own edges and raises rather than defaulting an unlayered node to superstep 0:
that default would place it in the first superstep with every other unlayered
node and manufacture firings.

`python/prevalence_static.py` uses a THIRD form: the structural
over-approximation, which keeps the window and drops the value conjunct. It is
an upper bound, not the same relaxation as the superstep form, and the two
numbers are not comparable.

`python/dynamic_oprecords` needs one further caveat before its superstep
figures are read. The executor pre-populates every cell with the sentinel
`NULL` so that first-layer reads are recorded at all, and all 520 superstep
firing events in that directory are reads of that sentinel rather than of a
value another agent produced. Under Definition 1 the same records give 0/360,
because the executor stamps read and commit on consecutive ticks and every
window has width one. `python/oprecords`, by contrast, has 0 of 100 superstep
firings on the sentinel. `python/predicate_matrix.py` reports both columns.

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

`python/check_imports.py` gates that every intra-repo import in a file this
document cites resolves statically. It is pure AST: no execution, no
third-party imports, so a machine without `langgraph`, `openai` or `crewai`
installed still runs it and a probe that legitimately needs them is not
flunked. A file this document does not cite is reported as a warning and does
not set the exit code. It reported one such case until round 5:
`python/prevalence_corpus.py` imported `instrument_layered`, which was defined
nowhere in the tree. That function now exists in `python/prevalence_harness.py`
and every intra-repo import in the repository resolves, so the gate runs with
zero warnings.

`check_ignores.sh` gates that only the root `.gitignore` carries active
rules among the ignore files git honors. Evidence in this repository was
invisible for two rounds because `python/.gitignore` carried two rules
nobody had read. Ignore files inside already-ignored directories (`.idea/`,
`.venv/`, `verus-count-clone/`) are shadowed and are reported as such, not
counted.
