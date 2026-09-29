# Shortest witnesses, safety proofs, and compiled sessions

M4 adds certified shortest witnesses, named safety properties, k-induction, and
optional reuse of compiled models. The CLI and workbench retain version 1 with
additive operations and result fields. Existing saved revisions remain readable.

## Workbench workflow

1. Save a model. **Find shortest witness** searches from depth zero through
   **Max depth**, and reports the completed UNSAT checks preceding the witness.
2. Add Boolean assertions to **Named safety properties · JSON**, for example
   `{"At most once": "!DUPLICATE"}`. Save the new revision.
3. Select the property under **Check a safety property**. **Check through bound**
   searches for a reachable violation. **Prove by induction** uses Max depth as
   k, checks the base cases, and tries the induction step.
4. Inspect the proof evidence. A reachable counterexample uses the normal replay
   and timeline workflow. A failed induction assignment is shown separately and
   is explicitly labeled as potentially unreachable.

Properties are assertions to verify, and are stored separately from goals,
model constraints, and query assumptions. Assumptions restrict every state in
both base and step obligations. An unbounded conclusion applies to that
restricted system; the result retains the exact assumptions and property.

The retry examples include `At most once`. The faulty model is refuted by a
shortest counterexample at depth 5. The deduplicating model can be proved at
k = 12. At smaller k its induction step can be satisfiable from unreachable
states, even when bounded search has found no violation.

## Native query contract

Use the existing `--query-file` envelope:

```json
{
  "version": 1,
  "model": "examples/retry-protocol/deduplicating.smv",
  "query": {
    "operation": "prove-property",
    "property": {"name": "At most once", "expression": "!DUPLICATE"},
    "limits": {"depth": 12, "wall_ms": 60000}
  }
}
```

| Operation | Required query fields | Completed outcomes |
| --- | --- | --- |
| `shortest-reach` | Boolean state `target`, nonnegative depth | `reachable`, `unreachable` |
| `check-property` | Named Boolean state `property`, nonnegative depth | `violated`, `holds_bounded` |
| `prove-property` | Named Boolean state `property`, positive depth | `violated`, `holds_bounded`, `proven` |

Untimed Boolean state assumptions and Boolean watches are supported. All
operations honor the existing cancellation, deadline, conflict, and propagation
budgets. Errors and interrupted queries never publish a proof or optimality
claim. A wall limit includes loading for fresh CLI requests; the workbench hard
deadline covers loading, cache validation, waiting, analysis, and witness replay.

Workbench requests name a property from the immutable revision rather than
sending a new expression:

```json
{"operation": "prove-property", "property": "At most once", "limits": {"depth": 12}}
```

Unknown property names are rejected before starting a worker. Native generating
queries in exported traces contain the resolved name and expression, preserving
replay without the workbench. Replay checks the violation at the final state.

### Shortest-witness evidence

Bounded reachability already searched depths in increasing order. Its completed
positive results now include `optimality`:

```json
{
  "criterion": "transitions",
  "certified": true,
  "depth": 2,
  "unsat_depths": [0, 1],
  "method": "increasing-depth-exhaustion"
}
```

This is optimality for the recorded model, target, and assumptions. Depth counts
transitions; depth zero needs no earlier UNSAT obligation. Each earlier depth
must complete before search moves on. If a smaller check is interrupted, this
strategy has no later feasible witness to return and reports UNKNOWN without
an optimality claim. An unbounded legacy search does not acquire a shortest
claim. A bounded negative result still says `unbounded_outcome: unknown`.

The evidence records solver results, not an independently checkable SAT proof
file. Witness replay certifies feasibility; it does not reestablish minimality.
Regression oracles independently enumerate small graphs to check both claims.

### Safety and induction evidence

For k-induction, the base checks every depth 0 through k for:

```text
INIT(s0) ∧ INVAR(s0..sn) ∧ ASSUMPTIONS(s0..sn)
∧ TRANS(s0,s1)..TRANS(s[n-1],sn) ∧ ¬PROPERTY(sn)
```

The step omits INIT, assumes PROPERTY at states 0 through k−1, and asks for a
violation at k under the same invariants, transition relation, and assumptions.

- A SAT base is a reachable `violated` result with a shortest trace.
- Completed UNSAT bases with a SAT step yield `holds_bounded`, with unbounded
  outcome UNKNOWN. `proof.induction_counterexample` is an arbitrary-state step
  assignment, marked `reachable: not_established`; it is never saved as a
  replay-validated trace or exported as a scenario automatically.
- UNSAT base and step obligations are rebuilt and checked in fresh solvers,
  without incremental goal selectors, before publishing `proven`,
  `scope: unbounded`, and `proof.verified: true`.
- An interruption in either discovery or verification returns UNKNOWN without
  a successful proof claim. All verification work consumes the query budget.

`proof` retains the property, assumptions, base UNSAT depths, induction depth,
step status, verified base depths, and verification method `fresh-solvers`.
Finite domains, widths, frozen variables, and compile-time inputs remain part
of the model semantics. Dead ends are allowed. A system with no initial states
satisfies safety vacuously; proving a property is not evidence that INIT is
satisfiable. Use Pick initial state to check initialization separately.

Fresh solver verification shares the compiler and SAT backend; it is not an
independent proof checker. Exhaustive test oracles cover that remaining semantic
risk on small models. Cost optimization and auxiliary invariant discovery are
separate future features.

## Optional compiled sessions

```sh
python3 -m tools.workbench --reuse-models serve
```

Omit `--reuse-models` to retain the original fresh-process-per-stage runner.
The option also applies to the workbench JSON Lines `run` command. It is
currently supported on Linux, matching the supported build environment.

### Ownership decision

Package 17 is implemented with process-owned immutable snapshots. The core's
legacy expression, declaration, encoding, CUDD, witness, and cache managers
remain process scoped. A snapshot owns them for one validated model revision;
a child process owns all query-local mutations and solvers. The OS reclaims
those resources when the owner exits. This avoids depending on incomplete
singleton destructors for reuse.

The snapshot parses, validates, compiles INIT/INVAR/TRANS units (including
generated constraints), and computes model/microcode identity before reporting
ready. Only then can the runner publish it in its bounded pool. A failed
candidate load leaves previously published snapshots usable. No model reload
is performed inside an existing snapshot.

For each query the snapshot forks while single threaded, before parsing query
expressions or creating a QueryContext timer. The child inherits compiled units
through copy-on-write memory and uses fresh compilers and solvers for query
expressions. All child changes disappear on exit. The parent reaps each child
before starting another. Different snapshots can execute concurrently; a
snapshot serializes its own queries. No concurrent queries share a mutable
C++ address space.

Compiler temporary encodings now use process-wide unique identifiers with a
spelling that cannot appear as an SMV identifier. Previously independent
compiler instances restarted their temporary numbering, which could alias a
model unit and query unit in the same solver. Reuse regressions and the CNF
option matrix cover the repair.

This implements compilation reuse and owned lifecycle boundaries without
claiming that arbitrary multi-model in-process sessions are safe. Replacing
legacy manager lookups with explicit C++ owners, full in-process teardown, and
concurrent queries in one process remain a separate migration with destructor
and race gates. Process isolation remains the supported execution boundary.

### Cache and lifecycle rules

The pool holds at most four snapshots, evicting idle entries. A lookup hashes
source, selected root, effective input expressions, checker binary bytes, and
all microcode JSON filenames and bytes. The checker configuration is fixed by
the runner; source pragmas supply effective widths. Native model identity also
records encoding options, input values, environment constraints, and microcode
identity. Generated clauses derive from this validated source and compiler.
The pool rechecks the external fingerprint after loading before publication.

Hashes are recomputed on lookup, including same-size content edits with restored
mtimes. A changed binary, root, source, input, or microcode requires a new
snapshot. Hashing the packaged 181 MiB of microcode is deliberately included in
warm query timings. Goal/property/watch metadata does not change compilation;
resolved query expressions and saved artifact revision IDs still isolate jobs.

Cancellation or a hard deadline discards the affected snapshot. Graceful close
asks its parent to kill and reap the active child, with process-group kill as
a fallback. A worker crash produces an execution failure; subsequent requests
can load a new snapshot. Closing the Engine joins active jobs and closes every
snapshot. Sessions are transient and never replace durable revisions/results.

Results report `statistics.compiled_snapshot`, `session_cache_hit`,
`session_key`, and the original `session_load_ms`. No result cache is used.

The native transport is available as `yasmv --quiet --session-file load.json`.
The load document contains `version: 1`, `model`, and optional `inputs`; root
selection remains `--root`. It emits one `status: ready` JSON line with identity,
source constraints, and loading time, followed by one result for each native
query JSON line on stdin. EOF closes the snapshot. The workbench owns the hard
deadline and lifecycle; direct transport clients must also supervise it.

## Verification

```sh
make analysis-test
make query-test reliability-test
make test
```

The analysis tests compare shortest depths, reachable violations, and successful
induction proofs with exhaustive four-state graphs. They include zero-step
violations, unreachable cycles, dead ends, assumptions, inconclusive induction,
and properties requiring larger k. Native checkpoint tests interrupt base,
step, and verification work and require the next query to remain valid.

Session tests compare fresh and cached results, check child reaping and stable
parent memory, exercise repeated load/query/destroy and eviction, interleave
queries across revisions, cancel and crash snapshots, reject failed loads,
invalidate changed inputs/root/content, and reload saved workbench results.
Chromium covers shortest search, bounded safety, a successful proof, reachable
refutation, and result reload alongside the prior milestone workflows.

For a reproducible local comparison, run:

```sh
python3 tools/benchmark-sessions.py --runs 5 --output /tmp/session-benchmark.json
```

The report records every sample, source and checker hashes, native model and
microcode identity, query/options, machine, compiler flags, and Python version.
It checks that fresh and cached outcomes and optimality evidence agree. Cold
snapshot loading is reported separately from warm queries.

### Recorded benchmark — 2026-09-26

The [five-run report](benchmarks/m4-sessions.json) uses the faulty retry model,
`DUPLICATE`, depth 12, aarch64 Linux, GCC 13.3, and the recorded optimized build
flags. Median elapsed time was **1,292 ms fresh** and **181 ms warm**, including
full external content hashing on every cache lookup. The initial snapshot load
is recorded separately. These are local development-machine measurements;
the report preserves individual samples and exact inputs for comparison.

### Local acceptance evidence — 2026-09-26

- Every suite in `make test` passed, including the existing C++, short,
  functional/LLVM smoke, reliability, query, workbench, explanation, and scenario
  tests, plus six M4 analysis tests and seven session tests.
- The compiler isolation regression passed all eight supported CNF option
  combinations. Seven native query tests passed, including deterministic
  cancellation during base checks, induction, and proof verification.
- AddressSanitizer and UndefinedBehaviorSanitizer passed the M4 analysis and
  session suites, the 26 reliability process cases, all eight CNF combinations,
  the seven native query cases, and the focused corrupted-property replay
  check. Leak detection remains disabled for the legacy process-lifetime
  managers; session tests explicitly verify child reaping and stable parent
  memory. The long sanitizer invocation was completed in separate batches.
- Chromium completed the M2–M4 workflow: shortest search, branch/explanation,
  scenario export and both implementation replays, bounded safety, unbounded
  induction proof, reachable refutation, artifact reload, and mobile layout.
- Published schemas and real native requests, shortest-witness traces, bounded
  evidence, and proof results validated. Changed Python modules compiled,
  JavaScript syntax checks passed, distribution entries exist, and
  `git diff --check` passed.

The [benchmark report](benchmarks/m4-sessions.json) records matching fresh and
cached results and the measured benefit. The implementation plan records the
process ownership refinement and the remaining in-process migration separately.

## Guaranteed progress (M6)

Universal eventuality is available through `check-progress`. Its graph proofs,
loop/dead-end evidence, and resource semantics are documented separately in
[the progress guide](PROGRESS_CHECKING.md). It complements safety induction and
does not add general LTL/CTL or fairness.

## Interpolation

Select `strategy: "interpolation"` on native `reach` with no depth cap, or on
`prove-property` with a positive `limits.depth`. `auto` retains the existing
algorithms. Bounded `reach`, `shortest-reach`, and `check-property` reject the
interpolation strategy. The workbench job API uses the same selection; unbounded
workbench reach omits `limits.depth` and can supply a wall or solver budget.
The browser offers **Interpolation** under **Proof method**. In the terminal:

```text
property set safe !bad
prove-property safe -strategy interpolation -depth 12 -wall-ms 60000
job show -full
```

An interpolating property query may prove safety before its depth cap. At cap
exhaustion it returns `holds_bounded` only after concrete UNSAT checks at every
depth from zero through the cap. Interruption returns `unknown`. A reachable
violation is a shortest concrete path, decoded to normal trace v1 and replayed
by the workbench. An approximation-started SAT result never becomes a trace.
`checked_depths` and `optimality.unsat_depths` describe actual concrete checks;
image iterations and suffix horizons are separate statistics.

The initial fragment requires deterministic, untimed Boolean INIT, INVAR,
target/property, and assumptions, expanding defines, parameters, and effective
inputs. Transition constraints may be nondeterministic but must refer only to
the current and next state, without absolute time. Arithmetic, finite enums,
arrays, hierarchy, frozen variables, and partial transitions are supported.
Assumptions constrain every state and can create dead ends or an empty initial
set. The result explicitly records vacuity for the latter. Effective input
values in interpolation witnesses are evaluated with SAT against the pinned
path; their decoding shares the query's cancellation and solver budgets.

A successful proof has `proof_method: "interpolation"`, `scope: "unbounded"`,
and `proof.verified: true`. The fresh-solver obligations are
`initial_containment`, `transition_closure`, and `target_exclusion`, each
`unsatisfiable`. `statistics.interpolation` records the suffix horizon, image
queries, enlargements, restarts, concrete/spurious SAT counts, proof nodes, and
circuit nodes. These counters are not byte-accurate memory accounting.

`proof.invariant` uses [state invariant v1](formats/invariant-v1.schema.json).
It binds the circuit to the full model/configuration identity, target, and
assumptions, with a symbol catalog and a one-based atom dictionary. Each atom
identifies a symbol's flattened native encoding bit and whether it is frozen;
integer bits are most-significant first, arrays concatenate element encodings.
`nodes` contains reachable gates in topological order. Even `id` values identify
gates, `atom` identifies an input, and `and: [left, right]` identifies a
conjunction. References use their low bit for negation; 0 and 1 denote false
and true. Gate IDs can have gaps. `root` selects the invariant output.

The inline artifact is inspection evidence, not a new save/revalidate command.
Schema validation checks structure; it does not establish inductiveness or
model identity. The engine establishes the three obligations before publishing
it. Model compilation and these checks share the native compiler/backend.

The [benchmark guide](INTERPOLATION_BENCHMARKS.md) compares interpolation with
bounded search, simple-path exhaustion, and k-induction on fixed safety cases,
including process time, memory, proof sizes, and incomplete outcomes.
