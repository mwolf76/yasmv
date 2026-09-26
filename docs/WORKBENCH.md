# Local model workbench (M2–M4)

M2 implemented work packages 10–12: an artifact runner, a browser workbench, and
a retry-protocol demonstration. The server and CLI use Python 3.10+ standard
library modules; the browser uses ordinary HTML, CSS, and JavaScript. There are
no runtime npm dependencies or external web assets. M3 adds bounded
explanations and executable scenario export/replay; see
[EXPLANATIONS_AND_SCENARIOS.md](EXPLANATIONS_AND_SCENARIOS.md). M4 adds shortest
witnesses, named safety checks, induction proofs, and optional compiled sessions;
see [STRONGER_ANALYSIS.md](STRONGER_ANALYSIS.md).

## Start

Build the checker using the existing instructions, with arithmetic microcode
available, then run from the repository root:

```sh
python3 -m tools.workbench serve
# Optional separate artifact store, checker build, or port:
python3 -m tools.workbench --store /tmp/my-exploration --binary ./yasmv serve --port 8766
```

Open `http://127.0.0.1:8765`. Choose an example, save and validate its revision,
select a goal and explicit depth/deadline, then search. Pick initial state is
also available. Editing source, root module, compile-time inputs, named goals,
safety properties, or watches creates a new revision when saved. Query assumptions do not mutate
that revision. Word widths are set in the source, using the existing directive.

Results distinguish completed positive/negative computations, execution errors,
and inconclusive interruption. A bounded negative is always labeled with its
bound and unknown unbounded outcome. Model validation checks parsing, types, and
structure; it does not claim that an initial state exists.

## Inspect and branch

Generated traces are replayed in a fresh worker before publication as trusted
artifacts. Uploaded JSON appears as **Untrusted import** until replay succeeds;
a failed import cannot enable export or branching. Replay verifies the effective
model identity, all state values, INIT/INVAR/TRANS, the generating query, and
embedded branch ancestry. Export preserves the exact trace-v1 artifact.

The timeline shows state variables, Boolean watches (including DEFINE names),
changes since the previous state, and differences from another saved trace.
Comparison can cross revisions; revision IDs remain visible. Integer state
values stay decimal strings, including values beyond JavaScript's exact numeric
range. **Watches currently support Boolean state expressions only**; non-Boolean
or temporal expressions are rejected explicitly. State variables retain their
existing integer, enum, Boolean, and array trace types.

Selecting state `k` and branching pins states `0…k`, including state `k`'s action.
The new constraint applies at the source of each added transition. An
incompatible constraint yields a blocked continuation containing only the
successfully established prefix. The UI explains when a fresh search is needed.
The full parent is embedded in the child and replayed before it is accepted;
parent artifacts are immutable. Reload restores the revision, trace, comparison,
selected state, and selected job. Jobs and artifacts also survive server restart.

## Artifact protocol v1

The artifact runner wraps the existing native query-v1 protocol. The native
`--query-file` API and `tools/run-query.py` remain available. Native query-v1 gains
additive `validate-model`, `prefix_length`, and Boolean `watches` support.

Discover capabilities without opening an artifact store:

```sh
python3 -m tools.workbench capabilities
```

Create a revision from a JSON document containing `source` (SMV text), optional
`name`, `root`, and maps of `inputs`, `goals`, and `watches` (expression strings):

```sh
python3 -m tools.workbench --store /tmp/exploration revision revision.json
```

Use the returned `id` in a job document:

```json
{
  "version": 1,
  "request_id": "find-duplicate-001",
  "revision": "REPLACE_WITH_REVISION_ID",
  "hard_timeout": 60,
  "query": {
    "operation": "reach",
    "target": "DUPLICATE",
    "assumptions": [],
    "limits": {"depth": 12, "wall_ms": 50000}
  }
}
```

```sh
python3 -m tools.workbench --store /tmp/exploration run request.json
```

Stdout is JSON Lines. Each accepted job emits `started`, zero or more `progress`,
and exactly one terminal `result`. Every event has `version`, `request_id`, and a
zero-based monotonic `seq`. Progress reports `phase` (`analysis` or `replay`) and
elapsed milliseconds in that phase; it does **not** estimate solver completion.
Native checker output and logs go to job files, never onto machine stdout.
A rejected request emits one error result and launches no worker. CLI exits are
0 for completed, 3 for unknown, and 2 for errors. SIGINT/SIGTERM cancel an active
CLI job and still produce a terminal result.

The [job schema](formats/workbench-v1.schema.json) describes the envelope. Unknown
fields, duplicate JSON keys, nonfinite numbers, unsupported protocol versions,
JSON nesting beyond 256 levels, malformed limits, and unsupported operations are rejected before starting a
worker. Expression syntax/types are validated by the checker. Request IDs must
be unique in a store; clients can retrieve an existing job instead of resubmitting.

| Operation | Required query fields | Meaning |
| --- | --- | --- |
| `validate-model` | — | Load and validate source/configuration |
| `pick-state` | — | Find one initial state under assumptions |
| `reach` | `target`, `limits.depth` | Search depths 0 through the bound |
| `validate-trace` | `trace` or `trace_id` | Replay imported or stored evidence |
| `simulate` | `trace` or `trace_id`, `limits.depth` | Extend a replay-valid trace |

For continuation, optional `prefix_length` selects the number of retained states
(default: the whole parent); `limits.depth` counts **additional** transitions.
`until` can stop at a reachable condition during continuation. `trace_id` refers
to the outer artifact's SHA-256 ID, not the native worker-local trace name.
`watches` optionally overrides the revision's Boolean watch map for a job.
The server deliberately offers bounded reachability only; advanced native query
operations remain available through the native API.

## HTTP transport

The server binds only to IPv4 loopback. Host and Origin checks reject foreign
origins and DNS rebinding; mutation requires JSON content type. Static content
uses a restrictive content security policy. Source, expressions, and diagnostics
are rendered as text. This is a local developer tool, not a remotely hosted,
authenticated, multi-user service or an operating-system sandbox.

| Method and endpoint | Response |
| --- | --- |
| GET `/api/capabilities` | Protocol version, operations, supported limits and features |
| GET `/api/examples` | Source and goal/watch presets for both receivers |
| GET / POST `/api/revisions` | List revisions / save immutable revision |
| GET `/api/revisions/{id}` | Exact source and configuration |
| GET / POST `/api/jobs` | List persisted jobs / submit one structured request |
| GET `/api/jobs/{id}` | Original request, running flag, final result if available |
| GET `/api/jobs/{id}/events?after=N` | New events as JSON Lines; default N = -1 |
| POST `/api/jobs/{id}/cancel` | Request cancellation; send `{}` |
| GET `/api/traces?revision=ID` | Trace summaries, optionally filtered |
| GET `/api/traces/{id}` | Replay-validated trace artifact and evaluated watches |

Protocol errors return HTTP 400, missing artifacts 404, origin failures 403.
Accepted jobs return HTTP 202 immediately. Clients poll events/results. HTTP
reconnection does not submit a second job.

## Isolation and storage

`.yasmv-workbench/` is ignored by Git. A SHA-256 digest identifies each immutable
source/configuration revision. Each job has a dedicated directory and request,
progress log, worker stdout/stderr, and atomic final result. Trace artifacts have
separate content IDs and carry their revision, original job, validation status,
watch expressions, watch values, and trace. Repeated native IDs cannot collide across workers.

One runner owns a store at a time, enforced with a file lock; use the server API
while it is open. Up to four jobs run concurrently. Every analysis and generated
trace replay starts a new checker process with an argument array, controlled
working directory, explicit model path, and `YASMV_HOME`. Cancellation/hard
deadlines terminate the worker process group, then kill it if needed. The hard
deadline covers analysis plus replay. Worker crashes or malformed output produce
structured errors without changing prior revisions or trusted traces.

Artifacts are published using temporary files and atomic rename. On restart,
unfinished jobs become inconclusive `worker_interrupted` results; partial event
lines are discarded and missing terminal events are recovered without duplication.
Results are not resumed automatically. Store retention and deletion are manual;
no background garbage collection removes evidence.

## Verification

```sh
make workbench-test
make test
```

`tests/test_workbench.py` checks malformed envelopes, process isolation and
compile-time inputs, immutable revisions, selected prefixes (including an
immediately blocked branch), watches, untrusted imports, crash/deadline/cancel
handling, restart recovery, CLI events, HTTP origin checks, and the independent
protocol oracle. Existing M0/M1 suites remain regression gates.

Browser acceptance is separate from runtime dependencies and exercises actual
Chromium interactions, import/export, watches, branching, comparison, reload,
cancellation, bounded labels, and mobile layout:

```sh
# Node 22+; install test tooling outside the repository if preferred.
npm install --prefix /tmp/yasmv-browser playwright@1.63.0
/tmp/yasmv-browser/node_modules/.bin/playwright install chromium
PLAYWRIGHT_MODULE=/tmp/yasmv-browser/node_modules/playwright node tests/workbench-browser.cjs
```

See [the retry protocol guide](../examples/retry-protocol/README.md) for the exact
state graph, expected witness, limits, and scenario sidecar. The implemented M3 extension adds bounded explanations and executable scenario
export with a retry-protocol adapter, as documented in the linked M3 guide.

### Local acceptance evidence — 2026-09-26

- Full `make test`: passed, including 32 existing C++ unit tests, 43 short tests,
  13 functional cases, LLVM translation smoke, 26 reliability process tests,
  three C++ reliability cases across eight CNF settings, six C++ query cases,
  21 query process tests, and 15 new workbench tests.
- Final checker rebuild and all 15 workbench tests: passed.
- All 15 workbench tests against an AddressSanitizer/UndefinedBehaviorSanitizer
  build: passed. Leak detection is disabled for the existing singleton lifetime
  policy, as in the M0/M1 sanitizer configuration.
- Chromium acceptance: passed, including reload, cancellation, rejected import,
  trusted import/export, selected-prefix branch, blocked prefix, comparison,
  fixed-model bounded labels, original-artifact recovery, and 390px layout.
- Published schemas and retry sidecar: validated. Duplicate-key, nonfinite, and
  excessive-nesting request regressions pass. `git diff --check` passes.

The retry witness first reaches duplicate execution at depth 5 and passes both
checker replay and the independent Python state machine. The deduplicating
model has no duplicate witness through depth 12. These are the M2 exit gates;
M3 acceptance evidence is recorded in the explanation and scenario guide.

## M4 additions

Revisions may include `properties`, a map of names to Boolean state assertions.
The UI offers shortest search, bounded safety checks, and verified k-induction.
Start with `python3 -m tools.workbench --reuse-models serve` to opt into owned
compiled snapshots. Existing jobs and artifacts retain their format and replay
requirements. See [STRONGER_ANALYSIS.md](STRONGER_ANALYSIS.md).
