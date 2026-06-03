# Case Study Protocol: Finding $A_n$ Anomalies in Open-Source Multi-Agent Frameworks

This document specifies a concrete protocol for finding real-world
instances of the four formalised anomalies in deployed multi-agent
frameworks, validating them with the verified detector pipeline, and
filing patches upstream.

The goal is one accepted PR. That single PR is worth more in reviewer
credibility than the entire empirical pilot.

Estimated effort: 4-6 weeks of human-in-the-loop work.
Estimated $n$ of bugs found: 2-5 (filed), 1-2 (accepted).

---

## Phase 1: Target framework selection (week 1)

### Primary targets

These are open-source multi-agent frameworks with active concurrent
state-sharing patterns and reachable maintainers.

| Framework | Repo | Stars | Concurrency model | Best $A_n$ candidate |
|---|---|---|---|---|
| **AutoGen** | github.com/microsoft/autogen | 30k+ | GroupChat with shared state via "termination" | $A_1$, $A_3$ |
| **LangGraph** | github.com/langchain-ai/langgraph | 8k+ | State graph with channels; checkpointing | $A_1$, $A_6$ |
| **CrewAI** | github.com/crewAIInc/crewAI | 22k+ | Sequential by default; concurrent in `Process.hierarchical` | $A_1$, $A_2$ |
| **MetaGPT** | github.com/geekan/MetaGPT | 45k+ | Role-based with shared memory environment | $A_3$, $A_2$ |
| **OpenAI Swarm** | github.com/openai/swarm | 15k+ | Handoff-based; tool registry mutations | $A_2$ |

### Selection criteria

Pick **two** primary targets based on:
1. **Recent commit activity** (≥1 commit in last 30 days). Maintainers are reachable.
2. **Issues tagged `concurrency` or `race`**. Indicates the maintainers know they have these problems and welcome fixes.
3. **Public examples that exercise concurrent agents**. Reproducible without our infrastructure.

Recommended primary pair: **AutoGen** + **LangGraph**.
- AutoGen has the closest semantic match to our operational model (multi-agent shared termination conditions create natural $A_1$ and $A_3$ surfaces).
- LangGraph's state-channel model with checkpointing and parallel branches can produce $A_1$ and $A_6$ when the checkpointer commits effects out of channel-update order.

---

## Phase 2: Detector deployment (week 2)

### 2.1 Identify the runtime's "operation boundary"

For each target, locate the equivalent of our `OpRecord`. This is the
record-emission seam where a single agent's read-set, write-set, and
tool-call sequence are bracketed.

| Framework | Operation boundary |
|---|---|
| AutoGen | `ConversableAgent.generate_reply` → `ConversableAgent.send` round trip |
| LangGraph | Node entry → state-channel update via `add_messages` reducer |
| CrewAI | `Task.execute_sync` from `Crew.kickoff` |
| MetaGPT | `Action.run` from `Role._act` |

### 2.2 Add an instrumentation hook

Insert a small hook (≈30 lines) at the operation boundary that emits
`OpRecord` JSONL events. The hook captures:
- `read_set`: state keys accessed in this operation
- `read_values`: values read at the start
- `read_time`: monotonic counter
- `write_set` / `write_values` / `write_time`: state keys updated at commit
- `tools_visible_at_read` / `planned_tool` / `tools_used`: tool registry snapshot
- `io_seq` / `co_seq`: tool effect issued vs committed order

Reference implementation: `mac-consistency-pilot/python/instrument.py`.

### 2.3 Validate the hook on framework's own examples

Run each framework's published "concurrent agent" example with the
hook attached. Inspect a few traces by hand to confirm shape. Then
run the four detectors (`baselines/detectors.py`) and check whether
any anomalies fire.

If detectors fire on a framework example, that is *itself* the bug:
the framework's own showcased example exhibits a concurrency anomaly.

---

## Phase 3: Witness collection and triage (weeks 3-4)

### 3.1 Sweep representative workloads

For each target framework, run the detector against:

1. **The framework's own examples** (`examples/`, `cookbook/`, `notebooks/`).
2. **Any benchmark suite the framework ships** (e.g., AutoGen's `agbench`).
3. **Three custom workloads** matching our paper's three:
   - edit-review: 2 agents on a shared document
   - plan-execute: planner produces task list, executor consumes
   - triage: 3 agents with classification handoff

### 3.2 Filter detector hits

For each anomaly hit, classify it as:
- **(a) Spec bug**: the framework's documentation says this should not happen
- **(b) Implementation bug**: the framework's documentation is silent but the behaviour is clearly buggy (corrupts state, drops messages)
- **(c) Workload bug**: the workload is unrealistic and the framework can reasonably refuse to support it
- **(d) False positive**: detector pattern matches but the underlying meaning is benign

(a) and (b) are the candidates for upstream PRs. (c) and (d) are dropped.

### 3.3 Build minimum reproducer

For each (a) or (b) hit:
1. Strip the workload to the minimum that still triggers the anomaly
2. Verify reproduction at framework HEAD (latest commit, not pinned version)
3. Capture: original workload code, expected vs observed behaviour, OpRecord trace, detector witness

---

## Phase 4: Upstream filing (week 5-6)

### 4.1 PR/issue template

Use this template for the bug report:

```
## Title
Race condition in <component>: stale read commits divergent value

## TL;DR
Two concurrent invocations of <Agent.method> read the same shared
state, then commit conflicting writes in a non-deterministic order.
The later writer's value overwrites the earlier writer's, but the
earlier writer's downstream effects already used the now-overwritten
state. This is a stale-generation anomaly (formalised as A_1 in
[link to paper, once on arXiv]).

## Reproduction
[Minimal Python script, ≤40 lines]

Expected: <state coherence property the framework documents>
Observed: <state value after run differs from any agent's intended
write; concrete value shown>

## Trace
[Attach OpRecord JSONL trace from the detector pipeline]

## Diagnosis
The shared <component> is accessed without <appropriate concurrency
control>. Specifically:
- Agent A reads <state> at read_time = T1
- Agent B reads <state> at read_time = T2 (T1 ≈ T2)
- Agent B commits <write> at write_time = T3 (T1 < T3 < T_commit_A)
- Agent A commits a different write at write_time = T_commit_A
- Final state reflects A's write but A's downstream side effect
  reflects pre-T3 state

## Suggested fix
Two options:
(1) Take a [per-cell mutex / state checkpoint] across the read-and-
    commit window. This serialises concurrent agents but prevents
    the anomaly. We measured ~XX% latency overhead in our baseline
    runs against [comparable workload].
(2) Validate at commit time that no <state key> in the read set was
    modified between read_time and commit_time, aborting on
    conflict (snapshot isolation). This preserves throughput at the
    cost of XX% aborted operations.

We have a Verus-verified detector for this anomaly available at
<link to artifact>; happy to contribute a regression test.

## Repro environment
<framework version, Python version, OS>
```

### 4.2 Channels by framework

- **AutoGen**: file as GitHub issue first, then PR if maintainers ask. Their `concurrency` tag exists.
- **LangGraph**: GitHub issue. They have a Discord; consider a heads-up.
- **CrewAI**: GitHub issue. Maintainers are responsive on issues.
- **MetaGPT**: GitHub issue. Slower turnaround; expect 2-4 weeks for first response.
- **OpenAI Swarm**: GitHub issue. Note: marked "experimental" by OpenAI; PRs may go unanswered.

### 4.3 Disclosure timing

Standard 90-day responsible-disclosure window. If the bug is severe
(e.g., silent data loss in a production-recommended pattern), contact
maintainers privately first and offer to coordinate disclosure.

---

## Phase 5: Paper integration

After Phase 4, update the paper with the following:

1. **§5 Empirical pilot**: add a "Real-system case study" subsection
   reporting the bugs found, with anonymised per-bug summary table.
   Cite the upstream tracker for any accepted PRs/issues.

2. **§6.4 Illustrative discussion**: replace the informal Atomix /
   SagaLLM / CodeCRDT placements with concrete bug-find evidence.

3. **Abstract**: add one sentence: "Applied to <N>
   open-source multi-agent frameworks, the detector pipeline
   identified <K> previously-undocumented concurrency anomalies, of
   which <M> have been acknowledged by upstream maintainers."

4. **Threats to validity**: note that the case study used HEAD-of-main
   versions of each framework; behaviour at pinned releases may differ.

This is the work that lifts the paper from 7.0-class to 8.0-class. A
single accepted PR with a documented bug fix is the kind of evidence
top-tier reviewers ask for.

---

## What to defer if time runs short

If you have only 2 weeks instead of 6:

- **Skip MetaGPT, Swarm**: focus on AutoGen + LangGraph
- **Skip Phase 3.1 frameworks-own-examples sweep**: go directly to custom workloads
- **Skip 4.3 disclosure timing**: file public issues immediately
- **Accept "issue filed" instead of "PR merged"**: maintainer
  acknowledgement is also strong reviewer evidence.

A 2-week version still produces 1-3 issue filings and lifts the paper
from 7.0 to 7.4. Worth doing even at half-effort.
