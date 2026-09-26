# M3: bounded explanations and executable scenarios

This milestone adds explanations for impossible initial states, single-step
continuations, and bounded reachability, plus action-scenario export and a toy
implementation adapter. It builds on the immutable revisions and model-trace
replay contracts in [WORKBENCH.md](WORKBENCH.md).

## Start and follow the release workflow

Use the documented [build](../README.md#build), extract microcode, and run:

```sh
python3 -m tools.workbench serve
```

1. Choose **Faulty receiver**, save and validate, then search **Duplicate
   execution** through depth 12. The witness reaches the failure at depth 5.
2. Inspect its timeline and Boolean watches. Export its trace JSON if desired.
3. Select a step and create a child trace under a loss/retry constraint. To
   reproduce a blocked branch, select step 0 and enter `action = ACK`: the
   prefix pins `action = SEND`, so this next transition is impossible.
4. Click **Explain next step**. The UI displays a verified conflicting subset,
   its state coordinates, source links, bound, fixed background, and whether
   subset minimization completed. The explanation concerns one new transition,
   regardless of the **New transitions** value used for ordinary branching.
5. Select the original six-state trace and click **Export selected trace as
   scenario**. Model replay runs again before a scenario is published.
6. Replay against **Faulty receiver**: all observations match and duplicate
   execution is reproduced. Replay against **Deduplicating receiver**: the first
   difference is at state 5, after DELIVER, where expected executions are `2`
   and actual executions are `1`. Duplicate execution has not been reproduced.
7. Download the scenario, reload the browser, or restart the server. The
   original revision, parent and child traces, explanations, scenario, and
   implementation replay jobs remain available with their query context.

The initial-state and bounded-search explanation controls are in **Explain an
impossible query** below the search form. They run separate jobs; a normal
negative search does not incur explanation or minimization costs automatically.

## What an explanation establishes

Each source INIT, INVAR, and TRANS constraint is compiled into a complete unit
and asserted behind a selector. Generated inertial frame conditions, individual
pinned state values, user assumptions, and the target are also selectable.
A selector gates the root formula and every DD, arithmetic, and selection
clause emitted for that unit. An enabled use emits its complete definitions,
including definitions shared with disabled uses. Disabling a selector removes
the requirement; it does not assert the constraint's negation.

The MiniSat adapter returns the failed signed group assumptions after UNSAT.
The explanation service extracts the enabled subset and **solves again with
only that subset enabled before publishing it**. A SAT or interrupted query
never yields an impossibility explanation.

### Fixed background

The following remain fixed during core extraction and minimization:

- Declarations, finite type domains, signedness and bit widths.
- Compile-time input bindings and frozen-variable identity.
- The compiler's expression and arithmetic semantics.

Enum domains, including enum array elements, remain explicit background
constraints even when a generated domain INVAR selector is disabled. Removing
a source constraint does not change the language's types. No model INIT,
transition, pin, user assumption, or target is silently fixed as background.
A continuation's full parent must pass replay before explanation begins; its
selected prefix values are then individually selectable in the explained query.

Source constraint IDs retain their model occurrence and instance provenance;
`:tK` adds the state coordinate. Pin, assumption, and goal IDs identify their
query origin. The result's `constraints` catalog supplies spans and generated
constraint parent IDs. UI source links follow those parent references for
instantiated and generated constraints.

### Bounds and minimality

`explain-reach` checks each depth `0…N` independently, including shorter paths
that cannot extend to depth N. A completed negative contains a core for **each**
depth and `unbounded_outcome: unknown`. If any depth is feasible, no negative
explanation is returned. `exact_depth` is an explicit option for rechecking an
individual core; it makes no claim about shorter paths.

Optional minimization deletes one constraint at a time and retains a deletion
only after UNSAT. If every remaining deletion is SAT, the core is
**subset-minimal**: no single member can be removed while retaining UNSAT under
the fixed background. This is not a smallest-cardinality claim.

Shrinking has separate check and wall-time budgets **per depth**, within the
outer job's limits. If its budget expires, the last verified core is retained
with `subset_minimal: false` and the minimization stop reason. If the outer query
is interrupted before its required decisions complete, status is `unknown` and
no explanation is published. Previously completed cores do not establish an
unfinished through-depth claim.

## Explanation API

The native query-v1 and workbench job-v1 protocols gain three operations:

| Operation | Fields | Completed outcomes |
| --- | --- | --- |
| `explain-init` | Optional state `assumptions`; no depth | `satisfiable` or `unsatisfiable` |
| `explain-step` | Parent `trace` or workbench `trace_id`; optional `prefix_length`; depth omitted or 1 | One-transition `satisfiable` or `unsatisfiable` |
| `explain-reach` | Boolean state `target` and `limits.depth` | Feasible at some checked depth, or UNSAT through the bound |

Watches and `until` are not explanation options. Workbench revisions' default
watches are not evaluated for these jobs. Parent replay and the main decision
use normal query limits. The optional `explanation` object contains:

```json
{"minimize": true, "checks": 100, "wall_ms": 1000}
```

An example workbench query body (inside the existing job envelope):

```json
{
  "operation": "explain-step",
  "trace_id": "REPLACE_WITH_SAVED_TRACE_ID",
  "prefix_length": 1,
  "assumptions": ["action = ACK"],
  "explanation": {"minimize": true, "checks": 100, "wall_ms": 1000}
}
```

A completed negative adds an `explanation` object following
[explanation-v1.schema.json](formats/explanation-v1.schema.json). Its `cases`
contain `depth`, `verified_unsat`, `subset_minimal`, `candidate_count`,
`minimization`, and the retained high-level `constraints`. The standard result
still carries effective model identity, diagnostics, statistics, and source
catalog. The saved workbench request retains the original parent reference,
assumptions, limits, and options.

For independent reassertion, set `explanation.active_ids` to a case's constraint
IDs and rerun the same query. For a reachability case at depth K, also set
`limits.depth: K` and `explanation.exact_depth: true`. Other constraints are
disabled; declarations and the reported background remain fixed. Unknown IDs
are rejected. Deleting each ID in turn checks the subset-minimal claim. These
subset rechecks explain only the selected constraints, not the full model.

## Executable scenarios

[Scenario metadata v1](formats/scenario-v1.schema.json) now has an executable
profile: `adapter`, `actions.mapping`, and `actions.observations`, in addition to
the existing action symbol, controllable labels, observed symbols, and argument
bindings. Older v1 catalog metadata can remain a non-executable catalog; export
requires the complete explicit mapping profile.

The supported adapter is `retry-protocol-v1`. It accepts the eight named
protocol actions and requires `phase`, `retries`, `executions`, and `seen`
observations, plus the fixed argument `job_id = "job-1"`. Action labels map to
adapter action names, observed symbols map to adapter fields, and arguments
bind either a constant string or a typed trace symbol. Metadata cannot name an
executable or import arbitrary adapter code.

Export rejects missing mappings, unmapped action literals, absent or unassigned
required observations, unsupported adapter actions, and invalid typed values.
The last state's selected action is **not executed**: a trace with N states
exports N−1 actions. Initial observations and observations after every action
are checked. Integer values remain decimal strings with declared width and
signedness; no conversion through floating-point numbers occurs.

Each [executable scenario](formats/executable-scenario-v1.schema.json) includes:

- Model identity, original trace identity and digest, and workbench revision.
- Generating query context, including assumptions, limits, and branch ancestry.
- A record of successful model-trace replay at export.
- Explicit action names, typed arguments, expected initial and subsequent
  observations, and their source symbols/types.
- A deterministic policy: reset the implementation, execute actions in order,
  compare exact observations, and stop at the first divergence.
- A SHA-256 content ID for integrity and immutable storage.

The metadata mapping is part of a saved revision. Adding or editing it creates a
new revision. Existing M2 revisions remain usable; to export one, save a new
revision with mappings and import/revalidate its old trace JSON against the new
revision, or choose the updated example and run its goal again.

### Model replay versus implementation replay

Model replay checks the symbolic trace against SMV semantics, the generating
query, and parent evidence. Implementation replay calls the independent Python
state machine in `examples/retry-protocol/runner.py`. It controls request loss,
reply loss, delivery, retry, acknowledgement, and terminal stuttering explicitly.
It does not call the checker or translate the model into implementation code.

Replay records the first differing state, action, field, expected value, and
actual value, along with how many actions executed and whether duplicate
execution actually occurred. A corrected implementation diverging from faulty
expectations is a useful result, not a model-trace validation failure.

The portable scenario's model validation record is historical. Standalone
implementation replay reports `recorded_at_export_not_rechecked`; it does not
claim to validate the model again. Content hashes detect accidental edits, not
authenticate artifact authors. Deliberately changed expectations require a new
content ID and are checked against the implementation like any other scenario.

### Run without the workbench

Export from a trace JSON, its exact model/configuration, and explicit metadata:

```sh
python3 -m tools.scenario export trace.json \
  --model examples/retry-protocol/faulty.smv \
  --metadata examples/retry-protocol/scenario.json \
  --output scenario.json

python3 -m tools.scenario replay scenario.json --implementation faulty
python3 -m tools.scenario replay scenario.json --implementation deduplicating
```

Export performs fresh checker replay; optional `--inputs`, `--root`, `--binary`,
and `--home` select the matching configuration. Replay requires Python and the
repository's built-in adapter, but neither a server nor a checker process.
CLI exit codes are 0 for matched/exported, 3 for a localized implementation
divergence, and 2 for malformed artifacts, mapping, validation, or execution
errors. `--output` publishes JSON atomically.

### Workbench transport and persistence

The existing job envelope also accepts:

```json
{"operation": "export-scenario", "trace_id": "SAVED_TRACE_ID"}
```

```json
{"operation": "replay-scenario", "scenario_id": "SAVED_SCENARIO_ID", "implementation": "deduplicating"}
```

Scenario jobs use their saved query context and the envelope's hard timeout;
they do not accept new query assumptions or solver limits. Export performs a
fresh model replay. Implementation replay uses a separate adapter subprocess
with controlled arguments and working directory, process-group cancellation,
and a deadline. A scenario is immutable and belongs to its saved revision;
replaying it under another revision is rejected.

`GET /api/scenarios` lists saved scenario summaries and
`GET /api/scenarios/{id}` retrieves a portable artifact. Revision documents may
include `scenario` metadata. Capabilities advertise explanation operations and
the supported adapter. Job events retain `started`, `progress`, and one terminal
`result`; adapter work reports the `implementation-replay` phase. Saved replay
results keep the scenario ID, selected implementation, observations, and first
divergence separate from model-trace evidence.

## Verification

```sh
make developer-workflow-test
make test
```

The explanation tests reassert each reported core in fresh processes and, when
minimality is claimed, delete every member to require SAT. Cases cover INIT,
INVAR, assumptions, pinned values, generated frames, shared arithmetic,
disabled selectors, bounded dead ends, shrinking limits, corrupt parents, and
UNKNOWN. Existing incremental solver tests exercise failed assumptions across
the eight supported CNF option combinations.

Scenario tests cover exact query/model/trace provenance, numeric widths, missing
mappings, replay prerequisites, immutable artifacts, tampering, localized
divergence, standalone commands, and both receivers. The Chromium acceptance
workflow includes explaining a blocked branch, exporting the original trace,
replaying both implementations, downloading a portable scenario, and restoring
results after reload, alongside all M2 browser checks.

### Local acceptance evidence — 2026-09-26

- The complete `make test` gate passed, including the existing C++, short,
  functional, reliability, query, and workbench suites, plus nine explanation
  and eight scenario tests. Focused additions then passed for instantiated
  enum domains and source parents, shared conditional/array expressions, and
  malformed portable artifacts, bringing coverage to eleven explanation and
  nine scenario tests.
- AddressSanitizer and UndefinedBehaviorSanitizer passed the explanation and
  scenario suites, the additional native explanation cases, and the existing
  reliability gate across all eight supported CNF settings. An incomplete
  parent trace was also checked after the final fix: it returns UNKNOWN with
  `solver_unknown` and no explanation. Leak detection remains disabled under
  the existing singleton ownership policy.
- Chromium completed the M2 and M3 browser acceptance workflow, including a
  loss/retry branch, its blocked continuation explanation, scenario download,
  both implementation replays, saved-result reload, and the mobile layout.
  The faulty receiver matched the exported witness and executed the job twice;
  the deduplicating receiver first diverged at state 5, with one execution
  instead of the expected two.
- Published JSON schemas, the retry sidecar, and actual explanation and scenario
  artifacts passed schema validation. Python compilation, JavaScript syntax,
  and whitespace checks passed.
