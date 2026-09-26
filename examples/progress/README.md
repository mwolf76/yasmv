# Guaranteed progress

These small models distinguish reaching a goal from guaranteeing its arrival.

| Model | `check-progress FINISHED` |
| --- | --- |
| `complete.smv` | Proven: READY → WORKING → DONE |
| `stalled.smv` | Violated: WORKING has no successor |
| `retry-forever.smv` | Violated: SEND → RETRY → SEND can repeat forever |

Use a fresh native process for each model:

```text
workspace open "/tmp/progress-investigation"
read-model "examples/progress/retry-forever.smv"
reach FINISHED -shortest -depth 3
check-progress FINISHED -states 10000 -wall-ms 30000
dump-trace
export-progress "/tmp/progress.json"
validate-progress "/tmp/progress.json"
job show -full
```

The retry model has a successful path and an indefinitely unsuccessful path.
No fairness assumption rules out repeated loss. The displayed failure trace is
finite; its progress artifact records the closing transition back to loop_start.

For the bounded retry example, check `SUCCEEDED || EXHAUSTED` for eventual
completion. Checking `SUCCEEDED` alone fails because giving up is possible.
See [the progress guide](../../docs/PROGRESS_CHECKING.md).
