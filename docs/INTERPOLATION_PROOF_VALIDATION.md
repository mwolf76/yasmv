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
