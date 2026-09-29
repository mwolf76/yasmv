# Query, diagnostic, and trace contracts (M1)

M1 implements packages 06–09 of [the implementation plan](IMPLEMENTATION_PLAN.md).
The core still owns one model per process. Use a fresh process for each external
job; the direct C++ interface serializes execution over the existing managers.

## Run a job

Build using the recipe in [CORRECTNESS_BASELINE.md](CORRECTNESS_BASELINE.md).
From the repository root, save this as `request.json`:

```json
{
  "version": 1,
  "model": "tests/models/query.smv",
  "query": {
    "request_id": "toggle-1",
    "operation": "reach",
    "target": "x",
    "limits": {"depth": 3, "wall_ms": 5000}
  }
}
```

```sh
YASMV_HOME="$PWD" ./yasmv --quiet --query-file request.json
python3 tools/run-query.py request.json --hard-timeout 10 --output result.json
```

The checker writes one complete JSON object to stdout; diagnostic logging goes
to stderr. Model filenames are relative to the worker's working directory.
Use `--root main` on the checker or runner for multi-module models. Optional
request `inputs` maps compilation-time input names to expression strings.
Trace export currently requires input values to be literals (optionally negated),
including literal arrays. Other input expressions fail trace export explicitly.
Changing inputs changes model identity. Per-step actions remain ordinary model
variables, as specified in the accepted plan.

The runner launches a process group, enforces a deadline covering startup and
loading, sends TERM and then KILL if necessary, and discards incomplete worker
output. A forced timeout returns `status: unknown`, `stop_reason: deadline`,
`forced_termination: true`, and no trace. `--output` replaces the destination
atomically. Worker crashes or malformed worker output become internal errors.
This remains the M1 isolation primitive. The implemented M2 artifact runner
adds progress events, capability discovery, persistent artifacts, and a browser
workbench; see [WORKBENCH.md](WORKBENCH.md).

## Typed C++ boundary

Public declarations are in `src/query/query.hh`, `runtime.hh`, `source.hh`, and
`trace.hh`. Algorithms no longer take a shell `Command&`. Interactive commands
construct the same `QuerySpec` used by machine jobs and render `QueryResult`.

```cpp
query::QuerySpec spec;
spec.operation = query::Operation::reach;
spec.target = parse::parseExpression("x");
spec.limits.depth = 3;
spec.limits.wall_ms = 5000;
query::QueryContext context(spec.limits);
query::QueryResult result = query::execute(spec, context);
Json::Value output = result.json();
```

The model must already have passed `ModelMgr::analyze()`. The convenience
`execute(spec)` constructs the context. With an explicit context, construct it
with the request's limits; its lifetime covers loading if the caller also
installs a `ContextScope` around loading. `checked(spec)` is the shell adapter:
it throws on execution errors, while preserving ordinary negative/unknown
outcomes. Each context joins its watchdog before destruction. All engines used
by that context detach on destruction. Cancellation is cooperative at loading,
compilation, encoding, solving, and decoding boundaries. The signal handler
only sets a `sig_atomic_t` notification; ordinary code performs interruption.

Contexts and manager-backed expression/witness pointers are process-local.
Persistent concurrent sessions and ownership cleanup remain M4 work. The
current service deliberately selects one compatible reachability strategy per
query. Explicit `forward`/`backward` select direction; bounded reach supports
forward only. Opt-in `interpolation` supports unbounded `reach` and
`prove-property` with a positive concrete depth cap. See
[interpolation](STRONGER_ANALYSIS.md#interpolation) for evidence and eligibility.
Empty, unknown, or incompatible strategy configurations fail.

## Outcomes and scope

| Operation | Completed outcomes | Evidence / scope |
| --- | --- | --- |
| `check-init` | `satisfiable`, `unsatisfiable` | Initial-state consistency at depth 0 |
| `check-trans` | `satisfiable`, `unsatisfiable` | Transition consistency through a required positive depth; does not assert INIT |
| `pick-state` | `satisfiable`, `unsatisfiable` | Initial witness, enumeration, or exact count |
| `reach` | `reachable`, `unreachable` | Witness, bounded negative, or legacy simple-path exhaustion |
| `simulate` | `simulated`, `deadlocked` | New chronological continuation trace with parent metadata |
| `diameter` | `diameter` | Legacy maximum simple-path bound over invariant states |
| `validate-trace` | `valid`, `invalid` | Whole-trace replay, with mismatch step when inconsistent |

`status` is `completed`, `unknown`, or `error`. An unknown result has no
conclusive outcome. `complete` refers to the reported scope. A bounded
unreachable result has `scope: through_depth`, `stop_reason: depth_limit`, all
fully checked depths, and `unbounded_outcome: unknown`. It is not a safety proof.
Unbounded negative results identify `proof_method: simple-path-exhaustion`.
This preserves the existing algorithm; induction/proof artifacts remain M4.

Exit codes are 0 for completed computations (including negative results), 2 for
invalid requests/models/artifacts, 3 for inconclusive jobs, and 4 for internal
errors. There is no implicit expectation check. A structurally valid trace
whose transition is inconsistent returns completed `invalid`; malformed,
wrong-model, wrong-type, and wrong-goal artifacts are validation errors.

Result identity includes source-content digest, selected root, effective input
bindings/environment constraints, word width, supported CNF and SAT settings,
engine version, and a digest of the actual arithmetic fragment files. Model
revision is derived from these fields. Paths and elapsed times are excluded.
Digests identify local artifacts; they are not authentication signatures.

The solver identity records CaDiCaL's version, signature, verified build revision,
and search-propagation/cooperative-limit semantics. `--solver-info` reports the
linked solver identity without loading a model.

Statistics report compilation/encoding/solving/decoding elapsed milliseconds,
solver work, and maximum observed solver variables/clauses. These are measured
phase totals, not disjoint CPU accounting. Replay additionally reports the
number of constraints checked by the independent evaluator.

## Limits

All limits default to `-1` (unlimited):

| Limit | Semantics |
| --- | --- |
| `depth` | Maximum reach depth; transition-check depth; number of continuation steps; maximum diameter search depth |
| `states` | Positive enumeration/count limit for `pick-state` |
| `wall_ms` | Cooperative wall deadline, including loading in machine mode |
| `conflicts` | Total CaDiCaL conflict budget across the job's solves |
| `propagations` | Cooperative CaDiCaL search-propagation threshold across the job's solves |

Search-propagation counters exclude preprocessing work. Propagation thresholds
and conflict budgets above `INT_MAX` are checked cooperatively and can overshoot
between callbacks; they are not strict work caps. Exhausted budgets suppress
conclusive results and evidence even if the solver has just finished.

Zero solver-work or wall budgets return unknown. State limits must be positive;
reaching one produces an incomplete count. Reach depth zero checks the initial
state. Continuation depth must be positive (default one). Unsupported limit
combinations are rejected. A diameter depth limit returns unknown unless a
complete result was established. Every fully solved search depth is recorded.
Loading/guard validation consumes the same wall and solver-work budget.

Bounded reach and continuation require state assumptions. Legacy unbounded
reach accepts compatible timed assumptions. Backward trace replay translates
end-relative constraints into chronological coordinates; constraints outside
the recorded trace fail validation. The isolated runner supplies the hard stop
for operations without frequent cooperative checkpoints.

## Source provenance

The parser records declaration/INIT/INVAR/TRANS occurrences separately from
interned expressions. Each has an ID, module, expression, source span, parent
IDs, and optional explanation. Duplicate expressions at different locations
retain different IDs. Spans use one-based lines/columns and an exclusive end
column. They identify clause/declaration bodies.

Compiler units carry occurrence IDs. Instance IDs extend their source ID with
`@scope`; synthesized frame IDs identify module and variable. Frame constraints
refer to their variable declaration and assignment guards. Synthesized records
have a null span and an explanation rather than an invented source location.
IDs apply within a source revision; changed sources need explicit mapping.

Diagnostics contain `severity`, `code`, `message`, `primary`, and `related`.
Guard overlap diagnostics point to both source clauses. Model type/resolution
failures retain the relevant constraint spans. The conservative guard rule
from M0 is unchanged.

## Trace v1 and replay

The request and trace shapes are documented in
[query-v1.schema.json](formats/query-v1.schema.json) and
[trace-v1.schema.json](formats/trace-v1.schema.json). C++ import checks required
and unknown fields, version, identity, model symbol types, exact ranges, and
consecutive steps. The JSON schemas describe structure; symbol-dependent
value/range and model-consistency checks are performed by replay.

A trace contains identity, ID, generating query, typed symbols, explicit steps,
origin information, and optional branch metadata. Display steps always begin
at zero and run chronologically, including backward witnesses. The original
direction/time remains in `origin`.

| Model value | JSON representation |
| --- | --- |
| Boolean | `true` / `false` |
| Integer | Canonical decimal **string**, with width/signedness in symbol metadata |
| Enum | Literal name string, checked against the declared literals |
| Array | Array with exact declared length and recursively typed elements |
| Unassigned | Missing symbol value or `null`; never coerced to zero |

For example, uint64 maximum is `"18446744073709551615"` and int64 minimum is
`"-9223372036854775808"`. JSON numbers are rejected for integer state values.
Partial arrays are rejected; missing whole values yield inconclusive replay.
A trace records state variables, including inputs and frozen variables. Derived
DEFINE expressions remain available to the legacy display/evaluator; they are
not extra state in trace v1.

To replay, submit `operation: validate-trace` and put the complete artifact in
`query.trace`. Import creates a separate witness. A fresh solver pins every
recorded value and checks INIT, every INVAR, every TRANS, and generating query
assumptions/goal. An independent evaluator also checks the supported Boolean
connectives, integer constants/equality, NEXT, and guarded assignments. It
reports how many constraints it checked; unsupported expression forms rely on
SAT replay. This is a supplementary oracle, not a separate implementation of
the whole language.

To continue, submit `operation: simulate`, the parent in `query.trace`, optional
state `assumptions`/`until`, and `limits.depth`. The service validates the parent,
pins its entire prefix, and creates a new trace. Continuation assumptions apply
to the source states of new transitions. Existing parent assumptions are
validated over the parent; they do not silently become new continuation
constraints. The parent remains unchanged.

The child's `branch` records `parent_id`, `prefix_length`, and `parent_digest`.
The generating query embeds `parent_trace`, allowing replay of continuation
chains in a fresh process. Import also accepts a separately supplied parent.
Replay checks its digest, validates the parent recursively, and checks exact
prefix equality. The digest uses compact JsonCpp serialization in sorted object
key order; integral numeric options are normalized to JSON integers before
fingerprinting. A valid trace certifies the recorded path, not a separate claim that
no extension exists; deadlock is an outcome of the continuation query.

`dump-trace -f json` exports v1; `read-trace "file.json"` validates before
registration. Exporting multiple selected traces produces a JSON array of v1
objects; import each member separately. The legacy JSON shape is intentionally
not accepted as v1. Plain-text dump remains available. Legacy imports without generating-query
metadata cannot be exported as v1. Simulation now selects a
new continuation trace rather than changing the parent in place.

## Verification

`make query-test` runs direct C++ contract/cancellation tests and process-level
request/replay tests. `make test` includes those plus the M0 suites. These
checks and the ASan/UBSan gate run locally before committing; CI runs only
the CLI trace/replay and agent protocol smoke checks. See the
[local gate commands](CORRECTNESS_BASELINE.md#ci-and-local-pre-commit-gates).
Fixtures cover bounded and unbounded results,
negative/unknown/error outcomes, exact numeric boundaries, backward replay,
wrong/tampered artifacts, missing values, frozen/input values, source parentage,
continuation chains, CLI agreement, and forced worker deadlines.

### Local acceptance record — 2026-09-26

The LLVM-enabled build used GCC 13.3, C++20, `-O2 -g -Wall -Werror`, MiniSat
2.2.1, JsonCpp 1.9.5, ANTLR C runtime 3.4, and Boost 1.83 on Linux/aarch64.
`make test` passed 32 existing C++ tests, 43 short cases, 13 functional cases,
26 process/harness regressions, the three reliability cases in all eight CNF
configurations, six direct query cases, and the new process query suite. The
subsequent JSON numeric-normalization case brings that suite to 21 tests.
The LLVM checks remain translation smoke tests.

A separate clean core build with `-O1 -g -fsanitize=address,undefined
-fno-omit-frame-pointer` passed the reliability and query checks with
`ASAN_OPTIONS=detect_leaks=0` and `UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1`.
Leak detection retains the M0 exclusion for process-lifetime managers.

The 2,432 arithmetic fragments have manifest SHA-256
`3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.
Use `tools/build-provenance.py` to regenerate the full toolchain/library/fragment
inventory for another build.

## Additive native API extensions in M2

Query-v1 accepts `validate-model` (completed `valid`, scope `model`), which checks
model structure without requiring an initial state. `simulate` accepts optional
positive `prefix_length`, selecting the number of retained parent states; the
whole parent is still replayed and embedded for provenance. Its depth limit
counts new transitions after that prefix.

Optional `watches` maps display names to Boolean state expressions or DEFINE
names. Temporal and non-Boolean watches are rejected. Result `watches` maps each
name to its Boolean values in chronological trace order. Values are evaluated
using SAT with each complete state pinned, preserving the checker's bit-vector
semantics. Watches do not constrain the generating query. Trace-v1 continues to
carry the generating specification; evaluated watch views live outside the
trace in workbench artifacts. Interrupted watch evaluation remains inconclusive.

## Additive native API extensions in M3

`explain-init`, `explain-step`, and `explain-reach` return either a feasible
result or a verified high-level conflicting subset. Query `explanation` options
control per-depth subset minimization and explicit subset rechecks. Result
`explanation` carries bound, fixed background, source references, and verified
cores; interrupted decisions have no explanation. See
[EXPLANATIONS_AND_SCENARIOS.md](EXPLANATIONS_AND_SCENARIOS.md) for the complete
contract and the separate executable scenario/implementation replay workflow.

## M4 additions

`shortest-reach`, `check-property`, and `prove-property` add shortest-witness
evidence and named safety checks. Bounded reachable results now include an
`optimality` certificate; safety results use `violated`, `holds_bounded`, or
`proven` with explicit base/step verification evidence. Trace replay recognizes
resolved safety properties and verifies the final violation. Existing version 1
requests and traces remain valid. See [STRONGER_ANALYSIS.md](STRONGER_ANALYSIS.md)
for result scope, assumption semantics, optional compiled sessions, and limits.

## CLI model inspection (M5)

Successful `validate-model` results additionally contain `symbols`, using the
same name-to-type/frozen/input descriptors as trace v1. This catalog describes
resolved state variables and is available even when INIT is contradictory;
validation does not require an initial witness. The CLI and agent workflow is
documented in [CLI_WORKBENCH.md](CLI_WORKBENCH.md). Existing native request
formats and trace serialization are unchanged.
