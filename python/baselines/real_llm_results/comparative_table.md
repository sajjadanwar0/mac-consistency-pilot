## A_1 (stale-generation) firing rate by runtime × workload

| Runtime | edit-review | plan-execute | triage |
|---|---|---|---|
| vanilla | 100.0% [100.0, 100.0] | 0.0% [0.0, 0.0] | 33.0% [24.0, 42.0] |
| pessimistic | 0.0% [0.0, 0.0] | 0.0% [0.0, 0.0] | 0.0% [0.0, 0.0] |
| snapshot_isolation | 0.0% [0.0, 0.0] | 0.0% [0.0, 0.0] | 3.0% [0.0, 6.0] |

## Full level distribution per cell

| Runtime | Workload | $L_0$ | $L_1$ | $L_2$ | $L_3$ | $L_4$ | n |
|---|---|---|---|---|---|---|---|
| vanilla | edit-review | 100 | 0 | 0 | 0 | 0 | 100 |
| vanilla | plan-execute | 0 | 0 | 0 | 0 | 100 | 100 |
| vanilla | triage | 33 | 0 | 0 | 0 | 67 | 100 |
| pessimistic | edit-review | 0 | 0 | 0 | 0 | 100 | 100 |
| pessimistic | plan-execute | 0 | 0 | 0 | 0 | 100 | 100 |
| pessimistic | triage | 0 | 0 | 0 | 0 | 100 | 100 |
| snapshot_isolation | edit-review | 0 | 0 | 0 | 0 | 100 | 100 |
| snapshot_isolation | plan-execute | 0 | 0 | 0 | 0 | 100 | 100 |
| snapshot_isolation | triage | 3 | 0 | 0 | 0 | 97 | 100 |