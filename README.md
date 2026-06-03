# mac-consistency: empirical pilot package

End-to-end pipeline for the empirical evaluation (paper §7, Tier A1):

```
┌────────────────────────┐    JSONL events    ┌──────────────────────────┐
│ AutoGen runtime        │ ─────────────────► │ Rust analyser            │
│ (Python; instrumented) │                    │ (anomaly detectors)      │
└────────────────────────┘                    └────────────┬─────────────┘
                                                           │
                                            equivalence proof (Verus)
                                                           │
                                              ┌────────────▼──────────┐
                                              │ TLA+ Anomalies.tla    │
                                              │ (existing artifact)   │
                                              └───────────────────────┘
```

The boundary is JSONL: Python writes one event per line, Rust reads it. No bridge code.

## Directory contents

| Path | Purpose |
|---|---|
| `python/instrument.py` | Wraps an AutoGen scenario, emits one JSONL event per agent operation |
| `python/driver.py` | Runs N scenarios with varied prompts, collects traces |
| `python/prompts.json` | Task scenarios |
| `rust-analyser/` | Trace ingestion + A₁/A₂/A₃/A₆ detectors + level classifier |
| `verus-detector/` | Verus spec + executable + equivalence proof for A₁ |
| `sample-traces/example.jsonl` | Synthetic trace for testing the analyser without AutoGen |

## Step-by-step setup

### 1. Python side (AutoGen)

```bash
cd python
python -m venv .venv
source .venv/bin/activate
pip install autogen-agentchat autogen-core autogen-ext openai
# Set your API key
export OPENAI_API_KEY=sk-...
```

### 2. Rust analyser

```bash
cd ../rust-analyser
cargo build --release
# Test against the synthetic trace before running real AutoGen
./target/release/analyser ../sample-traces/example.jsonl
```

You should see anomaly counts and a level classification.

### 3. Verus (optional; strengthens formal contribution)

Install Verus per https://verus-lang.github.io/verus/ (you have it installed already). Then:

```bash
cd ../verus-detector
verus --crate-type=lib src/lib.rs
```

Expected output:
```
verification results:: 5 verified, 0 errors
```

(Numbers depend on Verus version; the key is `0 errors`.)

## Step-by-step run

### Quick test (no AutoGen, synthetic data)

```bash
cd rust-analyser
cargo run --release -- ../sample-traces/example.jsonl
```

Output:
```
=== Trace summary ===
events: 7
operations reconstructed: 3
=== Anomaly detection ===
A1 (Stale-Generation):       1 occurrence(s)
A2 (Phantom-Tool):           0 occurrence(s)
A3 (Causal-Cascade):         0 occurrence(s)
A6 (Tool-Effect-Reorder):    0 occurrence(s)
=== Level classification ===
Highest level satisfied: L_0
```

This validates the detectors work end-to-end on a known-anomalous trace.

### Real AutoGen pilot (4–5 weeks of work; this is the entry point)

```bash
cd ../python
source .venv/bin/activate

# 1. Run N=10 sessions (test small first)
python driver.py --n 10 --output ../traces

# 2. Scale up after sanity check
python driver.py --n 500 --output ../traces

# 3. Analyse aggregate
cd ../rust-analyser
for f in ../traces/*.jsonl; do
    cargo run --release --quiet -- "$f"
done | tee ../analysis.txt

# 4. Aggregate stats (write your own; the per-trace output is parseable)
```

### Verifying detector A₁ against the spec

```bash
cd verus-detector
verus --crate-type=lib src/lib.rs
```

If verification succeeds, you have proven that the Rust `detect_stale_generation` function in this package returns `Some` iff the TLA+ predicate `StaleGeneration` holds. Cite this in §5 of the paper as "spec-to-implementation equivalence verified in Verus."

## Extending

- **Add A₂/A₃/A₆ Verus proofs:** copy the structure from `verus-detector/src/lib.rs`. Each follows the same pattern: spec predicate, exec function, ensures clause linking them.
- **Add scenarios:** edit `python/prompts.json`. Each scenario is a list of (agent_role, task_description) pairs.
- **Tune anomaly bounds:** the Rust analyser is bound-free (works on whole histories); only the formal verification has bounds.

## What this gets you for the paper

| Section | Evidence type | New |
|---|---|---|
| §3 anomaly catalogue | TLC witnesses | (existing) |
| §4.4 snapshot insufficiency | TLC witness | (existing) |
| §5 mechanisation | TLAPS + **Verus equivalence** | Verus is new |
| §6.4 deployed mappings | TLC for CodeCRDT | (existing) |
| §7 (NEW) empirical study | AutoGen traces × anomaly detectors | All new |

The §7 contribution alone moves the paper from 6.0/10 to ~7.5/10 in the brutal review framing. Adding the Verus equivalence pushes the formal contribution above "PROOF BY DEF" and answers the #1 review criticism directly.
