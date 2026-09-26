# M6 design and implementation plan: guaranteed progress

Status: core and CLI/agent implementation delivered on `feat/guaranteed-progress`,
branched from master `672db218`. Prepared 2026-09-26 against `e7ccf081`.
The [user guide](PROGRESS_CHECKING.md) describes implemented behavior; browser
presentation and fairness remain follow-ups. Acceptance results are recorded there.

## User outcome

Ask: **Does every execution eventually reach a state satisfying this goal?**

The first release answers one universal eventuality question. It returns a
verified proof, a replayable failure, or an explicit inconclusive result. A
failure is either a reachable dead end before the goal or a reachable repeating
execution that never visits the goal.

This complements reachability (some execution reaches the goal) and safety
(every reachable state satisfies a condition). It does not choose a winning
controller, guarantee repeated service of requests, or implement general LTL/CTL.

## 1. Semantic contract

Let P be an untimed, deterministic Boolean state expression, including expanded
DEFINEs and module parameters. Nondeterministic predicates are rejected; model
choices remain ordinary state variables.
Starting from every legal initial state, every **maximal execution** must visit
P at least once. A maximal execution is infinite, or finite and ends at a state
with no legal successor. Visiting P in the initial state already succeeds.
Behavior after the first visit to P is irrelevant.

- A dead end with P false violates progress; a dead end with P true succeeds.
- A reachable cycle entirely outside P violates progress, even if that cycle
  has an exit to P. Nondeterminism can choose the cycle forever.
- Rejoining a previously visited state does not by itself establish a cycle:
  two different paths can merge in an acyclic graph.
- No implicit fairness, scheduler preference, probability, or synthetic
  self-loop is added. All modeled choices are universally quantified.
- INIT, INVAR, TRANS, finite type domains, inputs, and frozen variables retain
  their existing meanings. P is a property, not an added invariant.
- State assumptions restrict initial states and every successor. They can
  create dead ends; those dead ends count as failures of the restricted system.
  Results display these assumptions explicitly.
- Unsatisfiable initialization yields a vacuous proof, with
  `initial_satisfiable: false` and `vacuous: true` prominently displayed.
  A successful proof alone must not be presented as evidence of a runnable model.
- First-release models must have state-local INIT/INVAR and a one-step TRANS
  relation. Reject explicit time references or nested NEXT that exceed this
  boundary, including occurrences hidden by DEFINEs, module expansion, and
  input substitution. The graph algorithm requires a time-homogeneous Markov
  state; the broader language's timed expressions cannot silently be accepted.

This is eventual completion from initialization, not “always eventually P” or
“every request eventually receives a response.” Those require separate contracts.

## 2. First backend: SAT-assisted graph exploration

Use the existing compiler and SAT engine to enumerate concrete initial states
and successors. Analyze the resulting graph in C++. This provides a complete
decision procedure when the finite exploration fits its limits, with an explicit
state-space cost. Symbolic lasso search is a later performance backend.

1. Check initial satisfiability separately. Enumerate all legal initial states
   with !P using exact assignment blocking; initial states satisfying P need no
   expansion. Proving completion requires exhausting this enumeration.
2. Explore these states in breadth-first order. For each state s, pin its entire
   valuation at time 0, assert TRANS(0), INVAR and assumptions at both endpoints,
   and enumerate successors satisfying !P at time 1. Do not assert INIT again.
3. Also determine whether any legal successor satisfying P exists. Record that
   as a successful exit; goal states need not be stored or expanded. A node is
   a dead end only when both successor searches are conclusively exhausted
   without any successor. “No non-goal successor” is insufficient.
4. Record exact non-goal edges and predecessors. Use an actual directed-cycle
   algorithm to find a nonempty cycle, including a self-loop. A partial graph
   can establish a failure, but cannot establish successful completion.
5. If all initial non-goal states and all their reachable non-goal successors
   are exhausted, and the graph has neither a cycle nor a dead end, progress
   holds. Build the certificate described below before publishing `proven`.

State identity includes every semantic state variable: module-qualified names,
hidden/action variables, arrays, and frozen values. Distinct initial frozen
valuations must not be merged. Compile-time inputs belong to model identity;
DEFINEs and compiler auxiliaries are not independent state dimensions. Allocate
and concretize all semantic bits, enforce finite domains, and block complete
valuations rather than SAT auxiliaries. Never convert missing values to zero.

Extract reusable state enumeration/pinning helpers from existing code where
appropriate. Do not directly reuse `assert_fsm_uniqueness` as a graph key: its
within-execution comparison deliberately skips frozen variables.

## 3. Results, resource limits, and evidence

Native operation: `check-progress`, with a Boolean `target`.

```json
{
  "version": 1,
  "model": "examples/retry-protocol/deduplicating.smv",
  "query": {
    "operation": "check-progress",
    "target": "SUCCEEDED || EXHAUSTED",
    "limits": {"states": 10000, "wall_ms": 30000}
  }
}
```

| Result | Meaning and evidence |
| --- | --- |
| `completed / proven` | Universal eventuality established; `scope: unbounded`; verified graph certificate |
| `completed / violated` | Replayed dead end or loop; `scope: unbounded`; counterexample artifact |
| `unknown` | Exploration or verification unfinished; stop reason and exploration statistics; no conclusive outcome |
| `error` | Invalid model/request/artifact, or internal failure under the existing exit-code contract |

Do not reuse `holds_bounded`: visiting many states without finding a cycle does
not establish that every execution completes within that many transitions.
Do not claim a shortest counterexample in this release.

Require a positive state limit and wall limit for discovery, with CLI defaults
of 10,000 states and 30,000 ms. Limits count distinct stored non-goal states across
all initial valuations. At the state limit, exhaustion of already admitted states
may still finish a proof; needing one additional distinct state returns UNKNOWN.
Reject `depth` in this first backend rather than giving it a new interpretation.
Honor conflict/propagation budgets, cancellation, and the runner's hard timeout.
Discovery and all verification consume the same budgets. Track nodes, edges,
fully expanded nodes, and pending frontier separately; graph levels are not the
existing `checked_depths` proof obligations. Check cancellation during graph
processing and serialization too. Account for dense edge storage in profiling;
add an explicit edge/memory limit before raising default exploration sizes.

### Failure artifacts and replay

Introduce `progress-counterexample-v1`: model identity, complete generating
progress query, `kind: loop | deadlock`, and an embedded finite `trace-v1` path.
For a loop, add zero-based `loop_start`; the last state has a real transition
back to that index. A one-state path with a valid self-loop is allowed.

The embedded path uses an ordinary reach query with target !P and the exact same
assumptions, so existing finite trace replay can validate its path. The wrapper
retains the progress claim. Add `validate-progress` for the stronger validation:

- Validate model identity, full values, INIT, every state and recorded edge.
- Check !P at every recorded state.
- For a loop, pin both endpoints and recheck the closing TRANS edge in a fresh
  solver, including invariants, assumptions, inputs, and frozen identity.
- For a dead end, pin the final state and prove that no legal successor exists,
  including successors that satisfy P.
- Reject malformed indices and mismatched contexts. Incomplete values or
  interrupted validation cannot certify a violation.

Ordinary `validate-trace` certifies only the embedded path, not the loop or
deadlock claim. Branching and simulation may use a validated finite path;
their child is a normal trace and does not inherit the progress violation.
An infinite counterexample is not an executable finite scenario. Require an
explicit finite-prefix conversion before scenario export and label its scope.

### Proof certificate and verification

Store a versioned `progress-proof-v1` artifact containing the query/model
identity, all enumerated non-goal states and edges, successful-exit flags, and
a nonnegative rank for each node. Ranks strictly decrease along every non-goal
edge. This makes absence of cycles checkable without trusting the traversal.

Before publishing a proof, verify in fresh solver instances:

1. No legal initial non-goal state is missing from the certificate.
2. Every listed valuation is well-typed, legal, and satisfies !P.
3. Every listed edge/goal exit is feasible, and no legal non-goal successor of
   any listed state lies outside its listed outgoing successors.
4. Every listed non-goal state has at least one legal successor.
5. Every non-goal edge strictly decreases rank.

Recheck initial satisfiability for the vacuity flag. This certificate can also
be supplied to `validate-progress`; interruption returns UNKNOWN. Keep large
certificates in immutable artifacts, with summaries/references in agent output.
Fresh SAT verification shares the compiler/backend and is not an independent
formal proof checker. Differential graph tests supply an additional oracle.

## 4. Delivery packages

| Package | Work and principal integration points | Completion gate |
| --- | --- | --- |
| 21. Semantics and oracle | Request/result/evidence schemas in `docs/formats/`; independent Python graph oracle; model-fragment validation contract | Handwritten examples distinguish existential reachability, universal eventuality, dead ends, vacuity, and cycle-with-exit |
| 22. Exact exploration | New `src/query/progress.cc`; reusable state helpers near `trace.cc`; `query.hh`, `query.cc`, `io.cc`, runtime budgets, build source lists | SAT enumeration and decisions match independent tiny deterministic and nondeterministic graphs; all supported finite state types preserve identity |
| 23. Evidence and verification | New progress artifact/replay code; graph ranks, fresh-solver obligations, immutable artifact storage | Every emitted failure/proof revalidates; tampering and interrupted verification never yield certified results |
| 24. Native and agent integration | Parser/commands/help, `src/workbench.cc`, `tools/workbench/{protocol,engine,client,native,cli,sessions}.py`, packaging | CLI and agent results agree; explicit revisions, cancellation, saved artifact reload, and isolated compiled sessions work |
| 25. Examples and browser presentation | Retry completion property, stalled/looping models, optional browser goal control and loop/dead-end display | A user can find, inspect, save, and revalidate each outcome without confusing reachability with guaranteed progress |

Packages 21–24 plus documented examples form the CLI/agent release. Browser
presentation may ship afterward. Keep named safety-property metadata unchanged:
the CLI accepts an expression or existing named goal and resolves it to an
explicit target before dispatch. Shell syntax:

```text
goal set finished SUCCEEDED || EXHAUSTED
check-progress finished -states 10000 -wall-ms 30000
job show -full
```

Agent `query.run` uses the explicit expression. Capability discovery advertises
the supported property form, backend, resource limits, artifact versions, and
`fairness: none`. Reject fairness fields until supported.

## 5. Validation and release acceptance

Add `tests/test_progress.py` with an independent graph oracle using a different
decision method (backward inevitable-goal fixed point). Generate small explicit
graphs, encode them as SMV, and compare results, including nondeterministic
branching, multiple initial states, self-loops, cycles with exits, merging paths,
unreachable cycles, and acyclic graphs with unsuccessful terminal nodes.

Cover P true initially and later becoming false; empty INIT; goal and non-goal
deadlocks; assumption-induced deadlocks; inputs, frozen values, hidden variables,
enum arrays, empty state vectors, and exact 64-bit values. Reject non-Markov
timed models and temporal/non-Boolean targets, including aliases. Mutate loop
indices, closure edges, goals, assumptions, ranks, successor lists, identities,
and missing state values. Inject cancellation and solver UNKNOWN in discovery,
enumeration exhaustion, cycle checks, certificate checking, and artifact replay.
Exercise exact limit boundaries, dense graphs, fresh workers and reused snapshots.

Release demonstrations:

1. Existing bounded-retry model: establish whether every execution eventually
   reaches `SUCCEEDED || EXHAUSTED`; independently enumerate to confirm the
   expected proof. The stronger `SUCCEEDED` target must expose a failure route.
2. Dedicated retry-forever model: produce a reachable loss/retry loop despite
   the existence of a successful delivery route. Use a finite retry abstraction
   whose counter does not accidentally wrap into an unrelated state.
3. Stalled worker: report a dead end before completion.
4. Too-small state or solver budget: UNKNOWN with no successful proof claim.
5. Persist/restart/replay each artifact and check the same conclusion.

Run focused native/query/analysis/CLI/session suites for the touched contracts,
then the repository's full local pre-commit gate and targeted ASan/UBSan checks.
Browser changes additionally require browser acceptance. Measure state/edge
counts, peak memory, enumeration time, and proof verification time on the example
models; set performance expectations from measurements, not source line count.

## 6. Follow-up: explicit fairness

M6 initially quantifies over all legal executions. A later proposal should add
state-based justice conditions: each supplied Boolean predicate must occur
infinitely often on an admissible infinite execution. These are query metadata,
never INVAR constraints. Weak/strong action fairness need separate definitions.

For this extension, search reachable non-goal strongly connected components that
contain a nonempty cycle and a witness for every justice predicate. Construct a
closed walk visiting all obligations; an arbitrary cycle inside such a component
may not suffice. Replay must check each obligation on the repeating segment.

Retain the explicit policy that an actual non-goal dead end is a failure; justice
does not excuse finite dead ends. Report whether any fair infinite executions
exist and distinguish finite successful executions from fairness-vacuous claims.
This requires analysis beyond the goal-pruned graph, since fairness concerns
behavior after a first goal visit too. Design this contract before exposing fair
proofs, and add an independent fairness oracle and no-fair-execution tests.

Only then consider symbolic lasso search, symbolic completeness/ranking methods,
recurring response properties, general temporal logic, or controller synthesis.
Each new backend must preserve this release's property and evidence semantics.
