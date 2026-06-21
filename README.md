# mac-consistency-pilot

The Verus proof development and the empirical Python harnesses for the paper
**Verified Detection and Prevention of Concurrency Anomalies in Multi-Agent
Large Language Model Systems** (arXiv:2606.17182).

This is the repository behind §5 (the empirical pilot, Tables S1–S6 of the
online appendix) and the detector/runtime obligations counted in §4. It has
two parts:

| Path | Contents |
|---|---|
| `verus-detector/` | The full Verus development — 27 proof files, **274 curated / 295 full** distinct verified obligations |
| `python/` | The empirical harnesses: cost/wall-clock measurement, MAST and cookbook prevalence, the in-the-wild repros, the corpus survey, and the inter-rater/judge audits |
| `reproduce_mac.sh` | One-shot reproduction: Verus + GenMC + TLC + TLAPS + runtime (`--formal-only` for the proof half) |
| `verus_count.sh` | Authoritative obligation counter (curated headline / `--full` distinct total) |

The other two repositories are `mac-consistency` (TLA+ / TLC / TLAPS) and
`mac-consistency-runtime` (the executable Rust runtime).

---

## Prerequisites

- **Verus** (main-branch build) and a recent **Rust** toolchain (`cargo`).
- **Python 3** (standard library only) for the harnesses under `python/`.
- Optional: **GenMC 0.17+** (https://github.com/MPI-SWS/genmc) for the RC11
  weak-memory check, and `tla2tools.jar` + `tlapm` for the TLC/TLAPS phases
  of `reproduce_mac.sh`.

---

## Quick reproduction

```bash
./reproduce_mac.sh                # Verus + GenMC + TLC + TLAPS + runtime (~10 min)
./reproduce_mac.sh --formal-only  # only Verus + GenMC + TLC + TLAPS (~5 min)
```

The harness classifies each TLC model by its expected outcome (an
expect-violation model's non-zero exit is a *pass*), checks each Verus file
against its pinned obligation count, and runs the GenMC RC11 litmus check
(N = 2, 3, 4 → 2, 6, 24 complete executions = N!, plus a relaxed-ordering
negative control that must report a race).

---

## A. The Verus development (`verus-detector/`)

`verus_count.sh` is the source of truth for the totals. Per-file `verus`
counts **double-count** modules that are re-`include`d by a self-contained
parent (notably the exec-mode files), so do **not** sum them naively:

```bash
./verus_count.sh           # curated headline total (superseded/helper files excluded): 274
./verus_count.sh --full    # full distinct total (empties the exclude list):           295
```

The files, grouped by role, with their live-confirmed per-file counts:

**Detector equivalence (sound *and* complete vs. the TLA+ predicates)**
- `lib_detector_equivalence.rs` — 24
- `lib_detect_a1_exec.rs` — 9   (executable `detect_a1`, 0 assume/admit/external_body)
- `verified_a1.rs` — runtime delegation to the verified `detect_a1`

**Lattice-level safety**
- `lib_l2_safety.rs` — 22   (transitive cascade + non-vacuity witness)
- `lib_l3_safety.rs` — 6
- `lib_l4_safety.rs` — 5
- `lib_concurrent_semantics.rs` — 9   (atomic-event lift, 0 axioms)
- `lib_a4_split_view.rs` — 9   (monotone-primary no-split)
- `lib_consistency_lattice.rs` — the L0–L4 composition root

**Exec-mode discipline (self-contained; re-include their level models)**
- `lib_l2_exec.rs` — 49
- `lib_l3_exec.rs` — 7   (a₆-free capstone)
- `lib_l4_exec.rs` — 9   (a₂-free snapshot discipline)
- `lib_pessimistic_exec.rs`, `lib_pessimistic_invariant.rs`, `lib_si_commit_invariant.rs`

**Spec ↔ runtime refinement**
- `lib_refinement_pessimistic.rs` — 31
- `lib_refinement_ssi.rs` — 18
- `lib_refinement_ssi_chain.rs` — 17
- `lib_refinement_default_si.rs` — 18
- `lib_occ_l2_refinement.rs` — 8   (OCC/ETag L1→L2 channel refinement, §6.5)
- `lib_langgraph_refinement.rs` — 7   (LangGraph runtime refinement, 0 axioms)
- `lib_l2_projection.rs` — 3   (L2 state→trace projection, 0 axioms)

**Strategy safety and trust base**
- `lib.rs`, `lib_ssi.rs`, `lib_default_si.rs` — the three deployed-strategy
  safety developments (pessimistic / SSI / default-SI)
- `lib_rustbelt_interface.rs` — 4   (the two structural lemmas
  `lemma_acquire_establishes_hold` and `lemma_mutex_exclusion_abstract`,
  plus `lemma_no_panic_in_runtime_critical_section` and
  `lemma_poison_is_fail_safe`; the three `RUSTBELT_OBLIGATION` stubs are
  `external_body` and are *not* counted as verified)

All counted files verify with `0 errors`. The trust base is two structural
axioms (in the refinement files) and the mutex correspondence; the three
RustBelt stubs are the explicit, enumerated residual.

---

## B. The empirical harnesses (`python/`)

Standard-library Python; the JSON/CSV/`.tex` outputs are the data behind the
paper's tables and findings.

**Cost and wall-clock (Tables S1, S2, S5, S6; §5.6, §5.10)**
- `cost_aggregate.json`, `cost_table.tex`, `runs.csv` — per-session token cost
  by runtime and workload.
- `paired_cost_analysis.py` — the paired SSI plan-execute overhead (~8%, p=0.007).
- `high_contention_cost.py` — the contention-scaled cost model.
- `plot_cost_envelope.py`, `fig_cost_envelope.pdf` — the cost-envelope figure.

**Prevalence: MAST and the cookbook (Tables S3, S4; §5.7–5.8)**
- `mast_adapter.py`, `mast_structural_classifier.py`, `mast_rates.json` —
  the MAST-Data analysis (0/600 parsed across the six parsed frameworks).
- `prevalence_static.py`, `structural_report.json`, `rates.json` — the
  16-topology static susceptibility classification.
- `prevalence_dynamic_run.py`, `prevalence_harness.py` — the dynamic
  confirmation across three model families (20/20 fire on susceptible
  topologies, 0/20 on immune ones).
- The 600-session cookbook A₁ rates (shared_workspace 90/100, five stateless
  topologies 0/100) reproduce here.

**In-the-wild reproductions (§5.12, §6)**
- `deerflow_3123_repro.py` — the ByteDance deer-flow silent lost update (#3123),
  the verified L0→L1 fix.
- `langgraph_a6.py`, `langgraph_a6_experiment.py`,
  `langgraph_a6_experiment_natural.py` — tool-effect reordering (A₆) in
  LangGraph's ToolNode on unmodified output.
- `l3_live_a6.py` — the live L₃ deployment of the commit-order sequencer:
  fires four concurrent tool effects per session through real models (reusing
  `prevalence_dynamic_run.py`'s `ModelClient`), takes the real completion order
  as the A₆ reorder source, and measures prevention. Across three model families
  (40 sessions each) the baseline showed A₆ in 110/120 sessions; the L₃ sequencer
  prevented it in 0/120. The runnable runtime is `mac-consistency-runtime`
  (`examples/l3_deploy.rs`).
- `letta_a1_probe.py`, `langgraph_prevalence.py`,
  `langgraph_corpus_results.json` — framework probes.
- `github_corpus_survey.py`, `prevalence_corpus.py` — the third-party repo
  corpus survey.

**Pilot drivers and instrumentation**
- `driver.py`, `autogen_pilot.py`, `run_production.py`,
  `production_extractor.py`, `production_scenarios.py`, `instrument.py`,
  `tokens_capture.py`, `prompts.json`.
- `counterfactual_reprompt.py` — the counterfactual re-prompt experiment.

**Inter-rater and judge audits (§5)**
- `judge_audit.py`, `audit_agreement.py`, `audit_sheet.csv` — the LLM-judge
  audit (κ ≈ 0.96, 59/60) and the inter-annotator agreement.

**Sub-projects with their own READMEs**
- `python/baselines/` — the Python runtime baselines (`detectors.py`, the
  pessimistic/SI runtimes, real-LLM and synthetic result tables). See
  `python/baselines/README.md`.
- `python/MAST/` — the MAST dataset, inter-annotator-agreement annotations,
  and the LLM-judge pipeline. See `python/MAST/README.md`.

---

## What this artifact establishes (reconciled with the paper)

| Claim | Where | Result |
|---|---|---|
| Detectors sound and complete | `verus-detector/lib_detector_equivalence.rs` | 24 verified, 0 errors |
| Full verified obligation count | `verus_count.sh` | 274 curated / 295 full |
| GenMC RC11 weak-memory check | `reproduce_mac.sh` (GenMC phase) | 2 / 6 / 24 executions (N = 2/3/4), control races |
| A₁ rate on MAST-Data | `python/mast_*` | 0 / 600 parsed |
| Cookbook A₁ (shared workspace) | `python/prevalence_*` | 90 / 100 (cross-agent 89 / 100) |
| A₆ live prevention (L₃) | `python/l3_live_a6.py` | baseline 110/120; L₃ sequencer 0/120 across 3 model families |
| Prevention cost | `python/*cost*` | SSI within noise; pessimistic 1.6–2.3× on the contended cell |

---

## Notes

- Per-file Verus counts are pinned in `reproduce_mac.sh` and may be revised
  as the development evolves; `verus_count.sh` reconciles them to the curated
  274 / full 295 headline by removing re-included (double-counted) modules.
- Generated artifacts (Rust `target/`, trace directories, `.tlacache/`) are
  git-ignored. The large per-session trace directories are reproduced by the
  harnesses rather than committed.