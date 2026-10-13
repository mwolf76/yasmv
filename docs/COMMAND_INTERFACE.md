# Unified checking interface

The `check` command selects the question first, then the method and limits.
This is a breaking interface change: old checking commands and query operation
names are rejected. Model input bindings still use `set` and `get`.

| Command | Meaning | Default |
| --- | --- | --- |
| `check init` | Is INIT ∧ INVAR satisfiable under the assumptions? | SAT |
| `check trans` | Does a path of N transitions exist, without INIT? | SAT, N=1 |
| `check reachable EXPR` | Can an initialized execution reach EXPR? | Interpolation |
| `check invariant EXPR` | Does EXPR hold in every reachable state? | Interpolation |
| `check progress EXPR` | Does every maximal execution eventually visit EXPR? | Explicit graph |

Transition consistency establishes existence, not totality or freedom from
deadlocks. Safety and reachability are dual: an invariant P is checked by
searching for !P. Progress is universal eventuality, without fairness. A
reachable non-goal cycle or dead end refutes it, even if another execution
reaches the goal. Empty initialization is reported explicitly as vacuous for
progress and interpolation proofs.

## Methods and operands

```text
check reachable BAD -method bmc -depth 20 -shortest
check invariant SAFE -method induction -depth 20
check invariant SAFE -method interpolation -wall-ms 120000
check progress FINISHED -states 10000 -async
job wait
job show -full
```

BMC checks depths zero through N and requires `-depth N` (0–10000).
Induction requires `-depth N` (1–10000): both the base-check bound and the
induction length. Reachability induction proves the target's negation.
A SAT induction step alone does not refute safety: it can begin at an
unreachable state. Only an initialized concrete path becomes a counterexample.

Interpolation is unbounded by default, including for invariant checks. It
rejects `-depth`; there is initially no user-facing horizon cap. It refines an
overapproximation, increasing its suffix horizon on spurious paths, until it
finds a concrete counterexample, verifies an invariant, or stops for resources.
The default method is interpolation for both reachable and invariant. There
is no silent fallback for unsupported fragments. `-shortest` requires BMC;
current BMC and interpolation concrete witnesses also carry shortest-path
certificates whenever their preceding concrete depth checks completed.

Positional operands are always model expressions. Saved expressions require
an explicit name, so saved metadata never shadows a model symbol:

```text
property set safe !BAD
goal set done FINISHED
check invariant -name safe
check reachable -name done
check progress -name done
```

Saved invariant names resolve in properties; reachable/progress names resolve
in goals. Expressions are checked against the loaded immutable model revision.

`-c EXPR` is repeatable. State assumptions constrain every analyzed state.
BMC reachability additionally accepts timed path constraints `@N{EXPR}` from
the start and `$N{EXPR}` from the end. Paths shorter than a referenced position
do not satisfy the constraint. Conclusions and shortest-path claims concern
the constrained query, never unrestricted reachability.

## Budgets and execution

All variants accept `-wall-ms N`, `-conflicts N`, `-propagations N`, `-sync`, and
`-async`. `-wall-ms unlimited` disables the time budget. Zero time or solver
work budgets return UNKNOWN. `-states N` applies only to progress; `-depth`
applies to trans, BMC and induction. Invalid combinations are rejected.
Wall limits are cooperative, include native loading and evidence verification,
and are not memory limits. A worker watchdog allows ten additional seconds
for process cleanup and replay. Unlimited time disables that watchdog too.

Background jobs capture their resolved settings at submission. `job wait`
retrieves a result and selects a replay-validated witness, if any. `job show
-full` displays the resolved request and evidence. Closing the shell cancels
outstanding jobs; async is not a persistent service.

Results distinguish satisfiable/unsatisfiable, reachable/unreachable,
violated/proven, bounded safety (`holds_bounded`), unknown and execution errors.
A bounded unreachable result includes `scope: through_depth` and
`unbounded_outcome: unknown`. Verified proofs have unbounded scope. Resource
exhaustion never upgrades partial exploration into a proof. Normal semantic
negative results do not cause an execution-error exit code. Shell `on failure`
selects unsatisfiable, unreachable, violated or invalid outcomes; bounded safety
is a completed `on success` result, explicitly labeled as bounded. Unknown
uses the separate UNKNOWN result and sticky exit status 3.

## Interactive settings

| Setting | Built-in default | Values |
| --- | --- | --- |
| `check.timeout` | `30s` | Integer durations in ms, s, m, h; or `unlimited` |
| `check.execution` | `sync` | `sync`, `async` |
| `check.progress.max_states` | `10000` | 1–1000000 |

```text
settings list
settings show check.timeout
settings set check.timeout 5m
settings set check.execution async
settings save
settings reset check.timeout
```

Precedence: command override, session setting, saved user setting, built-in.
Inspection shows the effective value, source, default and description. Names
and values are validated before mutation. `reset` selects the built-in value
in the current session. `save` atomically persists effective non-default
preferences to `$XDG_CONFIG_HOME/yasmv/settings.json`, falling back to
`~/.config/yasmv/settings.json`. Reset and save remove a persistent override.
No model or workspace is required to manage settings. Existing jobs never
change when settings change. Invalid configuration is reported, not ignored.

## Structured queries

Structured clients do not load interactive settings. They use the same built-in
checking limits and explicit request overrides. The native request is:

```json
{
  "version": 1,
  "model": "tests/models/query.smv",
  "query": {
    "operation": "check",
    "variant": "invariant",
    "target": "TRUE",
    "method": "interpolation",
    "limits": {"wall_ms": 120000}
  }
}
```

`target` contains the predicate for reachable, invariant, and progress. There
is no target for init/trans. `shortest: true` requires `method: bmc`. The native
API requires expressions; workbench/agent queries may instead use `name`,
resolved against their explicit revision before submission. Native evidence
contains the resolved expression. `wall_ms: -1` means unlimited.

All checking operations use `operation: check` and a `variant`. Removed
operation names, `strategy` selectors, and old `property` operands are errors.
The internal algorithm enum is private and does not define the wire contract.
The resolved query is recorded in job requests, trace artifacts, and native
`statistics.check`. Structured workbench requests can override `hard_timeout`;
otherwise check jobs derive it from their wall budget. Other job types retain
their existing process-supervision policy.

Explanation, trace, artifact validation/export, and diameter commands remain
separate. The schemas, browser, C verification tools, examples and tests use
the new contract. Legacy maze and bridge examples containing NEXT in INVAR
select BMC explicitly and label their negative conclusions as bounded.
Historical benchmark reports retain their original requests and hashes as
historical evidence, not runnable current API examples.

## Local validation (2026-10-13)

The optimized C++20 build passes with warnings treated as errors. All groups
in `make test` passed across the main run, remaining-target run, and focused
reruns after fixes. This includes LLVM 18 translation and C verification,
the eight CNF configurations, native query and trace tests, CLI settings and
job snapshots, workbench sessions, progress, interpolation, explanations,
scenarios, and the shipped examples. JSON Schema checks ran with `jsonschema`
installed. Chromium acceptance also passed, covering the browser workflows
and bounded, induction, and interpolation checks.

The functional harness validates semantic outcomes and replay evidence instead
of comparing solver-dependent witness snapshots. Its failure-injection tests
still reject false success, crashes, nonzero exits, and timeouts. Historical
benchmark reports were not regenerated. These are local results; sanitizer
and hosted CI runs are separate.
