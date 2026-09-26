# Native CLI and agent protocol (M5)

Model exploration is integrated into the existing yasmv interpreter. There is
one prompt, one loaded model, and one trace register. HTTP is optional.

## Start

Build the checker and extract microcode as described in the
[correctness baseline](CORRECTNESS_BASELINE.md). Workspace commands require
Python 3.10+ with standard library modules only.

```sh
export YASMV_HOME="$PWD"
./yasmv
```

`help` lists every command topic. Each command has its own page, such as
`help workspace` for artifact storage or `help job` for background jobs.
Existing editing, history, native expression syntax, `do`, and `on` continue
to apply. Quote file paths; write expressions normally. Shell options use a single dash because SMV uses `--` for comments.

## Explore the retry protocol

From the repository root, in the native shell:

```text
workspace open "./investigation"
read-model "examples/retry-protocol/faulty.smv"
goal set duplicate DUPLICATE
property set once !DUPLICATE
watch set duplicate DUPLICATE
show-symbols
reach duplicate -shortest -depth 12
list-traces
dump-trace
dump-trace -f json -o "/tmp/duplicate-trace.json"
scenario configure "examples/retry-protocol/scenario.json"
scenario export -o "/tmp/duplicate-scenario.json"
scenario replay faulty
scenario replay deduplicating
explain-step -at 0 -c action = ACK -minimize
job show -full
simulate -at 0 -c action = ACK -depth 1
check-property once -depth 12
```

The shortest witness reaches duplicate execution after five transitions. The
faulty receiver matches the scenario. The deduplicating receiver diverges at
state 5. The explanation checks why the selected prefix cannot continue with
ACK. `job show -full` retrieves the full explanation or proof evidence.

Start a fresh yasmv process to investigate the corrected model:

```text
workspace open "./investigation"
read-model "examples/retry-protocol/deduplicating.smv"
property set once !DUPLICATE
prove-property once -depth 12
job show -full
```

The native interpreter retains its existing one-model-load-attempt policy.
Source replacement requires a new process. Agents can use multiple immutable
revisions within one agent connection.

## Commands and shared state

A workspace is the directory that stores exploration artifacts. The commands
below use the native shell's loaded model and trace register. Use `help` for
the topic list and `help COMMAND` for syntax, behavior, and examples:

```text
help workspace
help reach
help explain-step
help job
```

| Commands | Purpose |
| --- | --- |
| `workspace open "PATH"`, `workspace show` | Choose an artifact store and inspect selections |
| `read-model`, `set`, `get` | Existing native model loading and input bindings |
| `goal`, `property`, `watch` with `set NAME EXPR` / `list` | Save named expressions in an immutable revision |
| `show-symbols` | Inspect resolved symbols, types, and frozen/input flags |
| `capabilities` | Discover agent operations; use `yasmv --capabilities` for machine-readable schemas |
| `reach EXPR -depth N`, optionally `-shortest` | Bounded or shortest search, accepting saved goal names |
| `check-property NAME -depth N`, `prove-property NAME -depth N` | Bounded safety checking and verified induction |
| `explain-init`, `explain-step`, `explain-reach EXPR -depth N` | Explain inconsistent assumptions and bounded impossibility |
| `simulate -at K -depth N` | Continue the current trace after preserving states 0 through K |
| `list-traces`, `select-trace`, `dump-trace`, `read-trace` | Existing native trace inspection and exchange |
| `compare-traces NAME NAME` | Compare native trace names or durable artifact IDs |
| `job list`, `show`, `wait`, `events`, `cancel` | Inspect and control supervised jobs |
| `scenario configure "FILE"`, `list`, `show`, `export`, `replay IMPLEMENTATION` | Configure and replay executable scenarios |

A plain `reach EXPR` and ordinary `simulate -k N` retain their native behavior.
New reach options select the bounded worker path and require `-depth N`.
Property and bounded explanation commands also require explicit depths.
A saved goal takes precedence over the same target spelling in a bounded
search; use an equivalent explicit expression such as `x && TRUE` to avoid
an ambiguous saved name.

Property/explanation commands accept `-c EXPR`, `-wall-ms N`, `-conflicts N`,
`-propagations N`, and `-async`. Explanations additionally accept `-minimize`;
`explain-step -at K` selects a prefix. Reach accepts `-c`, `-wall-ms`, and
`-async`. `simulate -at K -depth N` counts N additional transitions; the action
at K remains part of the preserved prefix. Use `-t NAME` for a different native
trace. Inputs, root, word width, and solver configuration come from the native
session. Extra environment constraints are currently rejected by workspace jobs.

Worker traces are replayed against the loaded native model before being
registered and selected. They work with existing trace commands, `echo`, and
native simulation. Conversely, traces from native commands are replayed and
persisted when used by explanations or scenarios. Failed queries preserve the
current native trace. Metadata edits do not replace the native model or trace.
Named expressions are validated when used. Saved watches are evaluated on
worker traces and included in job evidence.

The loaded source is captured at read time: editing the source file does not
silently change the model used by workers. A saved workspace never substitutes
for a missing or failed native model load. Workspace selection and metadata are
persistent; loading a model in a new shell restores metadata matching its source,
root, and inputs. The shell still explicitly loads its model and selects traces.

A store has one owner at a time. Close the HTTP server before opening the same
store from the CLI. Switch workspaces after active jobs finish. The default is
`.yasmv-workbench` in the current directory.

## Batch use and jobs

```sh
./yasmv --quiet < investigation.commands
```

The native parser handles every command, including commands inside `do` and
`on success` / `on failure`. Errors remain sticky in batch exit status: 2 for
invalid input, 3 for unknown/interrupted work, 4 for internal errors. Completed
negative outcomes can drive `on failure` without turning into execution errors.
Use the agent transport below for structured output.

```text
reach FALSE -depth 10000 -async
job show
job cancel
job wait
```

Omitting a job ID selects the last submitted job. `job wait` registers a completed
job's trace in the native interpreter; `job show` only inspects it. `job show
-full` includes full evidence. Ctrl-C cancels a synchronous worker job. Closing
the shell cancels outstanding jobs and reaps the workers. Isolated jobs retain the engine’s
60-second default hard deadline; agent requests can set `hard_timeout` explicitly.

The existing `--query-file` and `--session-file` APIs remain supported.

## Agent protocol

```sh
./yasmv --capabilities
./yasmv --agent --store ./agent-investigation --reuse-models
```

`capabilities` lists operations with argument schemas, the query contract,
limits, evidence features, and exit codes. It does not acquire a workspace lock
or start a checker. Agent mode accepts one JSON object per line on stdin:

```json
{"version":1,"request_id":"load-1","operation":"model.load","arguments":{"file":"examples/retry-protocol/faulty.smv"}}
```

Use the returned revision ID explicitly:

```json
{"version":1,"request_id":"search-1","operation":"query.run","arguments":{"revision":"REVISION_ID","query":{"operation":"shortest-reach","target":"DUPLICATE","limits":{"depth":12}},"hard_timeout":60}}
```

Each command produces zero or more `started`/`progress` events and exactly one
terminal `result` event. Every event has version, the client request ID, and a
sequence number starting at zero for that command. The terminal event's `result`
contains a query result or a management result with `status` and `data`.
Worker job IDs are separate from protocol request IDs. Machine stdout contains
JSON Lines only; checker diagnostics remain in persisted job logs.

The [request schema](formats/cli-v1.schema.json) and dynamically advertised
argument schemas describe the same operation catalog. Query arguments use the
[workbench query schema](formats/workbench-v1.schema.json). Model-dependent
validation still runs in the checker. Duplicate keys, unsupported versions,
unknown fields/operations, and reused request IDs in a connection are rejected.
Malformed envelopes receive a terminal error; an unextractable request ID is
null. The next request can still execute. Request IDs are unique per connection;
job IDs are unique in the persistent store.

Analysis operations require an explicit revision. Trace, scenario, and job
operations require explicit artifact IDs. Interactive aliases and selections
are resolved by the shell before dispatch and are not interpreted by the agent
service. Agents can use `model.save` with an inline revision document instead
of a filesystem path, and `metadata.set` to construct named goals/properties.

### Cancellation and concurrency

`query.run` waits for completion and streams progress. To keep accepting
commands while work runs, use `job.submit` with the same arguments. It returns
immediately; follow with `job.events`, `job.show`, or `job.cancel`. `job.wait`
waits and streams progress. Up to four engine jobs can run concurrently.
`job.events` pages events and summarizes terminal evidence; retrieve full
results through `job.show` with `full: true`.

Native reach, property, and explanation commands accept `-async`. Ctrl-C cancels
a waiting job and preserves the shell. EOF closes the runner and cancels
outstanding jobs. In agent mode, SIGTERM also closes the runner. Worker
process groups and compiled snapshots retain the existing deadline and cleanup
rules. A synchronous command must finish or be interrupted before the next
input command is processed; use `job.submit` for cancellation over stdin.

## Architecture and packaging

`src/parser/grammars/smv.g` parses native commands. The interpreter owns the
loaded model, environment, selected trace, command composition, and terminal.
`src/workbench.cc` connects workspace commands to a private Python service over
a local socket. That service never reads terminal input and never prints a prompt.

`native.py` binds each request to the native source snapshot and configuration.
`client.py` validates and dispatches operations. `engine.py` supervises isolated
checker workers and stores immutable artifacts. Worker identities must match
the native context, and returned traces pass native replay before import.
`cli.py` renders human summaries and implements versioned agent JSON Lines.
The HTTP service continues to use the same engine independently.

`yasmv --agent` replaces the process with the agent transport. The executable
locates Python modules beside the source executable, under an installation's
`share/yasmv`, or in configured package/source paths. It passes the exact binary
and arguments without shell interpolation. Installation includes modules, help,
schemas, examples, and optional UI assets. Python must be available as `python3`.

## Verification

`make cli-test` exercises the real executable, shared native model and traces,
retry scenarios, explanations, properties, structured discovery, protocol recovery,
explicit revision isolation, cancellation, native help, and installed discovery.
Run the query, workbench, analysis, and native regression gates when changing
shared contracts. Sanitizer runs retain the existing `detect_leaks=0` policy
for legacy managers.

### Local acceptance — 2026-09-26

- All 15 CLI cases passed in the normal build. The same cases passed under
  ASan/UBSan across batches; the composition case was rerun after correcting
  its expected native trace name, alongside the added exit-cleanup case.
- Native unit, short, functional, LLVM smoke, and all eight CNF configuration
  checks passed. Workbench, explanation, scenario, analysis, and session cases
  passed across batches. An existing session-cancellation timing test failed
  during the parallel batch and passed on an isolated rerun.
- All seven native query cases and 21 query process cases passed.
- A staged installation performed a shortest search through the native shell,
  exported its trace, and exposed agent discovery outside the source tree.
- Interactive checks confirmed the original prompt, loaded-source snapshot,
  Ctrl-C recovery, and shared trace selection. Python compilation and whitespace
  checks passed.
