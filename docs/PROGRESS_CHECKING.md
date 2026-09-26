# Guaranteed progress

`check-progress P` asks whether every maximal execution from every legal initial
state visits the Boolean state condition P at least once. A maximal execution
is infinite or ends at a state with no legal successor. A goal true initially
already succeeds; subsequent behavior is irrelevant.

A reachable non-goal dead end violates progress. A reachable cycle avoiding the
goal also violates progress, even if it has an exit to the goal. No fairness is
assumed. Inputs remain compile-time bindings; per-step choices are state variables.

## Native shell

```sh
export YASMV_HOME="$PWD"
./yasmv
```

```text
workspace open "/tmp/progress-investigation"
read-model "examples/progress/retry-forever.smv"
goal set finished FINISHED
check-progress finished -states 10000 -wall-ms 30000
dump-trace
export-progress "/tmp/progress.json"
validate-progress "/tmp/progress.json"
job show -full
```

The native defaults are 10,000 non-goal states and 30,000 ms. The commands support
`-conflicts`, `-propagations`, and `-async`; checking also supports `-c EXPR`.
Validation uses the saved artifact's target and assumptions. Depth is not a
limit for this backend. Export uses the last completed job with progress evidence.
Named goals are resolved by the shell; agent queries use explicit expressions.

## Machine requests

Use `--query-file` with:

```json
{
  "version": 1,
  "model": "examples/progress/complete.smv",
  "query": {
    "operation": "check-progress",
    "target": "FINISHED",
    "limits": {"states": 10000, "wall_ms": 30000}
  }
}
```

`validate-progress` takes a `progress` artifact and its own `states` and `wall_ms`
budgets. All verification consumes those budgets. Zero wall/solver-work budgets
return UNKNOWN. A state budget must be positive. State limits count distinct
stored non-goal valuations, including hidden and frozen variables. Reaching the
limit still permits finishing already admitted states; requiring another state
returns UNKNOWN. Validation also returns UNKNOWN when an artifact exceeds its
state budget.

The agent's `query.run` and `job.submit` accept these operations under an explicit
revision. `progress.show` retrieves the artifact by `job_id`; `progress.export`
takes `job_id` and `file`. Full results are also available via `job.show` with
`full: true`. Compact results retain a progress summary and evidence reference.
The artifact is stored in the immutable job result and survives restart.

## Results and evidence

| Result | Meaning |
| --- | --- |
| `completed / proven` | Every execution reaches the goal; verified finite-graph ranking certificate |
| `completed / violated` | Replay-validated loop or dead end before the goal |
| `unknown` | Exploration or verification incomplete; no conclusion |
| `completed / valid` or `invalid` | Supplied progress evidence passed or failed semantic verification |
| `error` | Malformed request/artifact, unsupported model fragment, or internal failure |

Checking conclusions have `scope: unbounded`. There is no shortest-failure claim
or bounded-success interpretation. Exploration statistics report states, edges,
fully expanded nodes, and pending nodes.

A `progress-counterexample-v1` artifact has `kind: loop | deadlock` and embeds a
normal finite trace. A loop's last state transitions back to `loop_start` (zero
based); the closing edge is not a synthetic stutter. `validate-progress` checks
that edge or proves the final state has no successor, including goal successors.
It also checks the generating target/assumptions, model identity and complete
state values. `validate-trace` alone only establishes finite path feasibility.

A `progress-proof-v1` artifact has `kind: proof`, all relevant non-goal states,
outgoing edges, goal-exit flags, and decreasing ranks. Fresh solvers recheck
initial coverage, state/edge feasibility, successor coverage, and absence of
non-goal dead ends. The verifier checks strict rank decrease on non-goal edges.
This shares the compiler and SAT backend; it is not an independent formal proof
checker. Tests compare with an independent least-fixed-point graph oracle.

Unsatisfiable initialization produces `proven` with `vacuous: true` and
`initial_satisfiable: false`. The shell labels this explicitly. It does not
establish that the system can run. Assumptions restrict the analyzed system and
can create dead ends; the result retains those assumptions.

Progress failure paths can be inspected and simulated as finite traces. A
continuation does not inherit the loop/deadlock claim. Scenario export of a
saved progress path requires explicit finite-prefix conversion: export and
import the finite trace, then export that trace as a scenario. Executing a finite
prefix is not evidence that an implementation runs forever.

## Supported models and limits

The initial backend enumerates concrete states using SAT and checks the graph.
Large bit-vector models can exceed the state/time budgets. Fresh processes and
compiled snapshots use the same semantics. All state types supported by exact
trace exchange are supported, with literal compile-time inputs.

INIT and INVAR must be state-local. TRANS may relate the current and next state;
explicit time references and nested NEXT beyond one step are rejected, including
through definitions, module parameters, and inputs. Untimed, deterministic Boolean targets and
assumptions are required. Nondeterministic set expressions in those predicates
are rejected, including aliases; model choices belong in state variables. General temporal logic, repeated response guarantees,
fairness, controller synthesis, and symbolic progress backends are future work.

Run `make progress-test` for oracle, replay, resource-limit and CLI/agent tests.
The full `make test` gate includes them. The [design plan](PROGRESS_CHECKING_PLAN.md)
records the staged implementation and fairness follow-up.

## Acceptance and performance

Local acceptance on 2026-09-26 used GCC 13.3 on Linux aarch64. The 14 progress
tests passed, including 128 exhaustive two-state decisions against an independent
fixed-point oracle, larger nondeterministic graphs, all eight supported CNF
configurations, artifact tampering, state types, and CLI/agent persistence. Native
query tests cover interruption during discovery, verification, and replay. The
existing regression gate also passed (`make -o progress-test test`, with the
progress suite run separately). An installation staged under a temporary prefix
successfully checked, exported, and revalidated a proof outside the source tree.

ASan/UBSan checks passed without diagnostics, with leak checking disabled for
the existing singleton lifecycle. The first progress run passed 12 tests; two
retry-model tests correctly returned UNKNOWN at their 15-second deadline.
Those two tests and the proof/counterexample budget regressions passed when
rerun with `YASMV_PROGRESS_TEST_WALL_MS=90000`. All eight native query tests also
passed under sanitizers. This override changes test budgets only, not CLI defaults.

[Recorded measurements](benchmarks/m6-progress.json) include state/edge counts,
checker and standalone verification times, peak process RSS, compiler flags, and
binary/model digests. These are single fresh-process samples with startup costs:

| Model | Non-goal states / edges | Check, including evidence verification | Standalone verification |
| --- | --- | --- | --- |
| Complete | 2 / 1 | 1.28 s | 1.27 s |
| Stalled | 2 / 1 | 1.27 s | 1.27 s |
| Retry forever | 2 / 2 | 1.28 s | 1.28 s |
| Bounded retry, faulty | 34 / 36 | 1.47 s | 1.40 s |
| Bounded retry, deduplicating | 23 / 28 | 1.40 s | 1.37 s |

Peak RSS was about 373 MiB for each fresh worker across all five examples.
These small examples establish a reproducible baseline, not a scalability
guarantee. Large concrete state spaces remain limited by enumeration and budgets.
