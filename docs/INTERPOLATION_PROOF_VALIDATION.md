# Interpolation milestones 1–2: proofs and state predicates

The first [interpolation milestone](INTERPOLATION_PLAN.md) adds a standalone
CaDiCaL proof probe and a solver-independent resolution DAG. Milestone 2 adds
internal partitioned encoding, interpolant extraction, and fresh validation.
Reachability and query dispatch retain their existing defaults.

## Run the gate

With a configured yasmv build and the pinned installed dependency:

```sh
make cadical-proof-test interpolation-test
YASMV_HOME="$PWD" make -j3 test
```

The full test target includes the proof gate. To validate an explicit unmodified
CaDiCaL checkout and archive, including an assertion-enabled or sanitizer build:

```sh
python3 tools/test-cadical-api.py --source /path/to/cadical --suite all
python3 tools/test-cadical-api.py --source /path/to/cadical --suite proof \
  --build /path/to/instrumented-build \
  --cxxflags='-O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer'
```

`--suite api` remains the runner default; `make cadical-api-test` runs both
suites. The runner checks the checkout root, revision, modifications, required
headers, build artifacts, subprocess status, and timeouts. CI runs both suites
against assertion-enabled and release builds of revision
`c60730422e758ef1cebe7aeddf2dda31c996bf04`.

Setup installs `cadical.hpp` and `tracer.hpp` together. Configure checks the
matching callback interface and exercises attachment, clause notification,
conclusion, and disconnection. The tracer must be attached before variables or
clauses are added. Upstream types remain confined to the backend and standalone probe;
`sat::proof::ResolutionProof` and the public Engine API have no native solver
type dependency.

## What is checked

Original clauses retain their A/B origin by clause ID, including equal clauses
submitted under different partitions. Ordered RUP hints are checked by unit
propagation under the negated candidate clause. Starting from the conflict,
the checker reconstructs explicit binary resolution nodes in reverse reason
order. Irrelevant propagations are omitted. A strict subclause of the candidate
is represented by a separate weakening node. Deletions invalidate antecedent
IDs but preserve DAG nodes; restoration preserves the previous origin or
derivation. Only an empty clause can conclude a refutation.

The probe uses `plain`, `factor=0`, `lucky=0`, `walk=0`, and `seed=7`, and requests
antecedents from the tracer. This conservative configuration is the tested
starting point for interpolation, not a change to production SAT defaults.
It rejects RAT/extension steps, negative or absent hints, unknown/deleted IDs,
invalid propagation chains, tautological clauses, and native assumptions or
constraints. A callback error poisons the probe without unwinding through the
solver. Assumptions must instead be materialized as partitioned original units.
Incremental proof queries are deliberately unsupported.

The initial six proof test groups cover:

- Original empty clauses, duplicate originals, contradictory units, and root
  propagation, with A/B provenance preserved.
- Pigeonhole problems with two through five holes, requiring actual search.
- All 256 subsets of the two-variable unit/binary clause family, plus 120
  deterministic five-variable formulas, checked against exhaustive valuations.
- Weakening and synthetic deletion/restoration of both original and derived
  clauses, with retained DAG ancestry.
- Corrupt hints, clauses, IDs, conclusions, and lifecycle events; invalid
  steps cannot establish a proof fact.
- Materialized group assumptions and rejection of native assumption events.

A second checker verifies the emitted DAG's resolution and weakening rules
independently of RUP replay. Assertions are not used for test verdicts, so all
checks also run under `-DNDEBUG`.

## Recorded validation — 2026-09-29

- Autoreconf, configure with LLVM 18 enabled, and the normal build passed with
  warnings treated as errors.
- Full `make -j3 test` passed, including LLVM, all eight reliability CNF
  configurations, queries, sessions, workbench, and the new proof gate.
  The existing Python environment with jsonschema enabled was used; no tests
  were skipped and no assertions or timeouts were relaxed.
- Both API and proof suites passed against pinned release and assertion-enabled
  CaDiCaL archives. The release probe was compiled with `-O3 -DNDEBUG`.
- The proof suite passed with both it and CaDiCaL instrumented by ASan/UBSan,
  including leak detection.
- Chromium acceptance passed using Playwright 1.63.0 and Node 22.
- Source-distribution assembly passed; the packaged proof sources, runner,
  setup/configure support, and documentation matched the working tree.

## Milestone 2 implementation

`sat::Engine::Mode::record` preserves original clauses and snapshots the current
signed activation groups as units. Two distinct recording engines isolate all
encoder caches and auxiliary variables. `PartitionedCnf` merges only declared
semantic state bits at the selected cut, plus frozen parameters. It rejects
unexpected shared frames and excludes compiler temporaries from the interface.
Neither recording nor proof mode permits the optional CNF optimizer.

`Engine::Mode::proof` attaches the checked tracer before allocating variables.
Every original needs an A/B tag; the internal truth constant is an A unit.
Native assumptions, group operations, and a second native solve are rejected.
The production adapter and standalone probe now share `ProofTracer`, which
retains callback exceptions and rethrows only after returning from CaDiCaL.
Query checkpoints and explicit proof/circuit node caps bound construction and
traversal. Solver budgets are shared with the ordinary validation calls.

`sat::Circuit` uses hash-consed AND nodes and complemented edges. It supports
constants, sharing, state-atom renaming, evaluation, support enumeration, and
fresh definitional CNF for either polarity. Traversals are iterative.
`StatePredicate` separately compiles a deterministic Boolean state expression
and its semantic negation. Its eligibility check follows definitions,
parameters, and effective inputs, rejecting temporal or nondeterministic
constructs even when hidden by an alias.

`compute_interpolant` classifies variables against all original clauses and
uses McMillan's resolution labels. Only authorized shared semantic bits can
become leaves; weakening preserves its parent's label. Each result is checked
by fresh ordinary solvers for `A AND NOT J = UNSAT` and `J AND B = UNSAT`.
Only successful checks publish a verified interpolant. SAT, UNKNOWN, resource
limits, cancellation, and malformed proofs never publish one. Canonical state
bits can then be instantiated at another frame while preserving frozen bits.

The standalone suite now has eight groups. In addition to proof reconstruction,
it checks Craig conditions against exhaustive valuations, missing interface
authorization, circuit simplification/renaming, both CNF polarities, node limits,
and cancellation. Nine model-level test cases add:

- All 256 pairs of Boolean relations over one shared bit and one private bit on
  each side, checked against an independent existential-projection oracle.
- Compiled arithmetic, conditional muxes, array selection, and finite enums,
  including reusing the same compiler units in both partition namespaces.
- Both semantic predicate polarities, rejection of temporal/nondeterministic
  aliases, frame renaming, frozen parameters, and invalid cut rejection.
- An encoding-time ownership observer verifies that borrowing a shared compiled
  unit does not temporarily mutate CUDD reference counts.
- Materialized positive/negative groups, proof-engine lifecycle restrictions,
  and mutated/foreign interpolant rejection.
- Proof/circuit limits, interruption before each of the three SAT phases, and
  a successful fresh operation following cancellation.

### Shared DD ownership regression

The initial full run and a repeated Koenisberg run exposed an intermittent
CUDD garbage-collection assertion. The legacy parallel reachability path copied
compiled units and ADD wrappers during emission, mutating shared non-atomic
reference counts. Emission, DD walking, and mux access now borrow immutable
objects. Strategy threads borrow their target through the join, and constraint
units are also borrowed. This preserves parallel SAT solving while removing
these DD ownership mutations. A checkpoint observer tests reference counts
inside encoding, so the regression does not rely on reproducing thread timing.
After the fix, 100 consecutive Koenisberg runs passed with unchanged commands,
expected output, and the existing 60-second per-run timeout.

The broader sanitizer run also exposed a lifecycle-test race: the active-child
cancellation test could stop the previous query's child while the new request
was still fingerprinting the large instrumented binary. A diagnostic confirmed
cancellation occurred before `Session.query` admission. The test now waits for
the new lease and excludes previously observed child IDs, retaining the parent
and child reaping assertions and existing timeouts.

## Milestone 2 scope and remaining work

These APIs are internal building blocks. They do not yet implement the forward
search, invariant fixed-point checks, query dispatch, or serialized artifacts.
Milestone 3 will add the search and its explicit finite-graph oracle. Milestone
4 will expose strategy selection and result evidence.

Proofs retain the complete resolution DAG and clause history. Node caps are
not byte-accurate memory limits. General RAT proofs, incremental assumption
proofs, and default preprocessing still require additional reconstruction.
Craig validation shares the existing compiler/backend; it supplements proof
replay rather than providing an independently certified model checker.

## Milestone 2 recorded validation — 2026-09-29

- Full `YASMV_HOME="$PWD" make -j3 test` passed with LLVM 18 enabled after both
  regression fixes, including all eight reliability CNF configurations. The
  jsonschema-enabled Python environment was used; no tests were skipped.
- All six broader sanitizer targets passed: `reliability-test`, `query-test`,
  `workbench-test`, `developer-workflow-test`, `analysis-test`, and `cli-test`.
  The corrected cancellation case passed individually and in the full session
  suite; no assertions or timeout values were relaxed.
- Normal LLVM 18 build passed with warnings treated as errors.
- All nine native interpolation test cases passed, including the independent
  256-pair projection oracle and the shared-DD ownership observer.
- Both standalone API/proof suites passed against pinned release and
  assertion-enabled CaDiCaL builds; the release probe used `-O3 -DNDEBUG`.
- Standalone proof/circuit tests passed with ASan/UBSan and leak detection.
  A separate, fully instrumented yasmv/CaDiCaL build also passed all nine native
  interpolation cases. Core leak detection was disabled for the existing
  process-lifetime managers, as in the repository's sanitizer instructions.
- All 100 consecutive Koenisberg stress runs passed after the ownership fix.
- Chromium browser acceptance passed with Playwright 1.63.0 and Node 22.
- Source-distribution assembly passed and all changed distributed files matched
  their sources. The instrumented build used the full source tree: existing
  distribution omissions such as `src/utils/ctx.hh` were supplied from tracked
  files. This does not claim a clean distribution build.
- Build provenance was collected with `tools/build-provenance.py`.


## Milestone 3: internal forward search

`reach::interpolation::search` implements the increasing-horizon forward loop.
`ModelSystem` compiles the validated model hierarchy, effective inputs,
environment constraints, and state assumptions into I*, T*, and F*. Native
relations admit nondeterministic choices and references to the current/next
state; state predicates require deterministic Boolean expressions. Eligibility
expands defines, parameters, and effective inputs before checking time locality.

Module-generated enum membership is expanded to Boolean disjunctions before
negation. Recursive domain constraints also cover arrays of enums. This avoids
using the negation of an existential set choice as a semantic complement.

The initial circuit is obtained by interpolating I* against its independently
compiled semantic complement at frame zero. Both Craig obligations establish
exact equivalence. Image queries share only the next-state cut and frozen bits.
The suffix uses guarded continuation branches, admitting targets at every depth
up to its horizon, including deadlocked states. No simple-path constraints enter
the image proof.

An UNSAT image contributes a checked interpolant to the reached-state circuit.
A fresh ordinary solver tests image inclusion. A fixed point is accepted only
after three fresh checks of initial-state containment, transition closure, and
target exclusion against the original system. SAT after circuit growth causes a
restart from exact INIT with the next horizon. SAT on the initial iteration is
checked against incremental concrete search, which completes depths in order;
the shortest path is decoded and rechecked in another fresh solver before
publication. Empty INIT has an explicit, freshly verified vacuous result.

Image/horizon limits, proof/circuit node limits, solver UNKNOWN, and cancellation
produce no certificate. Observers and query checkpoints cover projection, image
construction, inclusion, growth, restarts, concrete search, and final validation.
Search statistics distinguish image iterations, spurious SAT, and actual
concrete checked depths. Query dispatch and serialized artifacts remain for
milestone 4; the internal API does not update query-result depth bookkeeping.

The independent graph oracle exhausts all 33,024 two- and three-state systems
(all transition relations, initial sets, and target sets), comparing outcomes
and shortest witnesses with breadth-first search and evaluating returned
invariants directly. The suffix oracle checks all 49,536 graph/start/target/
horizon combinations, including partial transitions. Native tests cover
arithmetic, enums, enum arrays, Boolean arrays, hierarchy and parameters,
frozen values, effective inputs, and assumptions creating dead ends. Damaged
invariants and paths fail fresh validation; limits and cancellation publish no
artifact and allow a subsequent search.

## Milestone 3 recorded validation — 2026-09-29

- Full `YASMV_HOME="$PWD" make -j3 test` passed with LLVM 18 enabled and the
  jsonschema-enabled Python environment; no tests were skipped. This includes
  all eight reliability CNF configurations and both interpolation suites.
- All six new native search cases passed, including the 33,024-system search
  oracle, 49,536 suffix checks, native model regressions, damaged certificates,
  and cancellation and resource limits. All nine existing interpolation cases
  also passed.
- The normal build passed with warnings treated as errors.
- Chromium browser acceptance passed with Playwright 1.63.0 and Node 22.
- Source-distribution assembly passed; changed distributed files were checked
  against their sources. This does not claim a clean distribution build (see
  the existing omissions recorded for milestone 2).
- Build provenance was collected with `tools/build-provenance.py`.
- All fifteen interpolation/search cases passed in the fully instrumented
  yasmv/CaDiCaL ASan/UBSan build, using the same production and test sources.
  UBSan halted on errors; core leak detection was disabled for existing
  process-lifetime managers, consistent with the repository's sanitizer setup.

## Milestone 4: query integration and evidence

Explicit `strategy: "interpolation"` selects the internal search for unbounded
reach and positive-depth property proofs. Bounded reach, shortest reach, and
bounded property checks reject this selection. Default dispatch is unchanged.
The workbench API, terminal property command, browser method selector, and
native/query/trace schemas carry the selection consistently.

The query adapter maps the internal result to reachability or safety outcomes.
A property depth cap D limits suffix horizons to D-1. Only a completed concrete
UNSAT prefix through D permits `holds_bounded`; other incomplete searches remain
UNKNOWN. Search statistics and concrete checked depths have separate fields.

Verified invariants are serialized as complemented AND graphs with an explicit
semantic bit dictionary, symbol catalog, model/configuration identity, target,
and assumptions. The three fresh-solver obligations, vacuity, and search sizes
are retained in the result. Circuit export walks only reachable gates in
topological order and checkpoints serialization. These inline artifacts are
inspection evidence; no external save/revalidate operation is introduced.

Concrete paths are pinned into another native solver for ordinary trace
decoding. The adapter resolves effective input expressions against that pinned
path using guarded SAT queries, including Boolean, signed/unsigned integer,
enum, and array values. This avoids copying an unevaluated input expression
into a trace value. Input decoding shares the query budgets and cancellation.
The default decoder behavior remains available to existing callers.

Cancellation and errors clear artifacts and proof-method labels, including
interruptions after verification or during circuit serialization, decoding, and
trace export. Native tests cancel at every solver boundary and sampled first,
middle, and final compilation/encoding/decoding boundaries, then repeat queries.
Integration tests compare public outcomes and shortest witnesses against finite
graphs, evaluate serialized invariants independently, replay typed traces,
exercise caps and shared budgets, and reopen persisted workbench evidence.

## Milestone 4 recorded validation — 2026-09-29

- Full `YASMV_HOME="$PWD" make -j3 test` passed with LLVM 18 enabled and the
  jsonschema-enabled Python environment; no tests were skipped. This includes
  all existing regressions and the six new interpolation query cases.
- All 25 native query/interpolation/search cases passed in the fully
  instrumented yasmv/CaDiCaL ASan/UBSan build. The sanitized `query-test` and
  `analysis-test` targets also passed, including all six new query integration
  cases and compiled-session regressions. The terminal interpolation selection
  test passed under instrumentation. UBSan halted on errors; leak detection
  remained disabled for the existing process-lifetime managers.
- Chromium browser acceptance passed with Playwright 1.63.0 and Node 22,
  including interpolation selection, verified evidence, persistence/reload,
  and the existing mobile and workflow checks.
- The normal build passed with warnings treated as errors. Build provenance
  was collected with `tools/build-provenance.py`.
- Source-distribution assembly passed; all changed distributed files matched
  their sources. This does not claim a clean distribution build (see the
  existing omissions recorded for milestone 2).

## Milestone 5: benchmark accounting and baseline

The benchmark runner compares bounded checks, forward simple-path exhaustion,
k-induction, and interpolation against identical models, inputs, assumptions,
and safety targets. It records each fresh process's elapsed time and Linux
`wait4` peak RSS, query statistics, proof sizes, and explicit outcome/scope.
Native UNKNOWN exit codes and hard timeouts remain incomplete samples. Every
counterexample must pass a separately timed fresh replay; interpolation proofs
must carry the three verified obligations and matching model identity.

The shared query context now counts actual native solver invocations. Calls
stopped by cancellation or a budget before entering the solver do not count.
Native tests check both a completed bounded query and cancellation before the
first solve. Runner tests cover problem/depth matching, outcome distinctions,
per-process RSS isolation, hard timeouts, native UNKNOWN handling, and real
safe/unsafe four-method runs.

The [baseline](INTERPOLATION_BENCHMARKS.md) contains 144 queries and 48 successful
counterexample replays. It supports keeping interpolation opt-in. No search
optimization or default change is selected without a demonstrated benefit.

## Milestone 5 recorded validation — 2026-09-29

- All 25 native query/interpolation/search cases passed in the fully
  instrumented yasmv/CaDiCaL ASan/UBSan build, including the solver-call
  accounting assertions. Production and test sources matched the normal
  build. UBSan halted on errors; leak detection remained disabled for the
  existing process-lifetime managers.
- Full `YASMV_HOME="$PWD" make -j3 test` passed with LLVM 18 enabled and the
  jsonschema-enabled Python environment; no tests were skipped. This includes
  all five new benchmark tests, the native solver-call accounting assertions,
  the exhaustive interpolation/search oracles, and existing regressions.
- The three-repetition benchmark completed all 144 queries, including nine
  cooperative timeouts retained as UNKNOWN. All 48 counterexample replays
  passed; every interpolation proof carried verified invariant obligations.
  Recorded binary, runner, manifest, and fixture hashes matched their sources.
- Chromium browser acceptance passed with Playwright 1.63.0 and Node 22.
- The normal build passed with warnings treated as errors. Build provenance
  was collected with `tools/build-provenance.py`.
- Source-distribution assembly passed, with all 21 changed distributed files
  checked against their sources. This does not claim a clean distribution
  build (see the existing omissions recorded for milestone 2).
