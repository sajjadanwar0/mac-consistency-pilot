# AutoGen pilot integration

The existing `autogen_pilot.py` constructs a vanilla `SharedStore`,
`ToolRegistry`, and `InstrumentedAgent`s from `instrument.py`. To run
under the baseline runtimes, replace the imports based on the
`--runtime` flag.

## Patch (apply to autogen_pilot.py)

```python
# Near the top, replace:
#   from instrument import make_scenario, InstrumentedAgent, SharedStore, ToolRegistry
# with:

import argparse
_pre_parser = argparse.ArgumentParser(add_help=False)
_pre_parser.add_argument("--runtime", choices=["vanilla", "pessimistic", "snapshot_isolation"], default="vanilla")
_pre_args, _ = _pre_parser.parse_known_args()

if _pre_args.runtime == "vanilla":
    from instrument import (
        make_scenario,
        InstrumentedAgent as RuntimeAgent,
        SharedStore as RuntimeStore,
        ToolRegistry as RuntimeTools,
    )
elif _pre_args.runtime == "pessimistic":
    import sys
    sys.path.insert(0, "/home/$USER/baselines")
    from runtimes.pessimistic import (
        make_scenario_pessimistic as make_scenario,
        PessimisticAgent as RuntimeAgent,
        PessimisticStore as RuntimeStore,
        PessimisticToolRegistry as RuntimeTools,
    )
elif _pre_args.runtime == "snapshot_isolation":
    import sys
    sys.path.insert(0, "/home/$USER/baselines")
    from runtimes.snapshot_isolation import (
        make_scenario_si as make_scenario,
        SIAgent as RuntimeAgent,
        MVCCStore as RuntimeStore,
        SIToolRegistry as RuntimeTools,
    )
```

## Argparse changes

Add to the existing argparse:

```python
parser.add_argument("--runtime", choices=["vanilla", "pessimistic", "snapshot_isolation"], default="vanilla")
parser.add_argument("--workload", choices=["edit-review", "plan-execute", "triage"], default="edit-review")
```

## What the workload should do

For each of the three workloads, run the AutoGen GroupChat pattern that
was already used to produce the existing 300-session pilot, but route
read/write/tool operations through `RuntimeAgent` instead of the
hardcoded `InstrumentedAgent`. The interface is unchanged
(`begin/commit/op` plus `tools.add/remove`), so the workload code
should work without further changes.

## Notes

- The pessimistic runtime drops on-conflict ops silently. The trace
  count per session may be lower than for vanilla. This is correct
  behaviour for the baseline: the runtime would have blocked these
  operations.
- The SI runtime emits `_metadata.json` per scenario with
  `total_aborts`. Pass this through to the analysis pipeline.
- All three runtimes emit JSONL traces of the same shape so the same
  detector pipeline analyses all three.
