# Interpolation milestone 1: resolution proof gate

The first [interpolation milestone](INTERPOLATION_PLAN.md) adds a standalone
CaDiCaL proof probe and a solver-independent resolution DAG. Production
reachability, solver options, and query results are unchanged.

## Run the gate

With a configured yasmv build and the pinned installed dependency:

```sh
make cadical-proof-test
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
clauses are added. Upstream types remain confined to the standalone probe in
this milestone; `sat::proof::ResolutionProof` has no solver dependency.

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

The six test groups cover:

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

## Scope for the next milestone

This is a feasibility gate, not a production interpolating solver. It retains
the complete DAG and clause history, without query budgets or memory limits.
Milestone 2 must add budgeted traversal, partition-safe model encoding, semantic
state-bit mapping, interpolant circuits, and Craig-condition checks. General
RAT proofs, incremental assumption proofs, and default preprocessing require
additional reconstruction before they can be admitted.
