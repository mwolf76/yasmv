# Correctness baseline and migration notes

This document describes the first implementation milestone from the
[implementation plan](IMPLEMENTATION_PLAN.md). It changes result handling and
validation before introducing the query protocol or workbench. The subsequent
M1 API and trace migration are documented in
[QUERY_AND_TRACE_CONTRACTS.md](QUERY_AND_TRACE_CONTRACTS.md).

## Build and test

The core requires a C++20 compiler, Autotools/libtool, ANTLR3 and its C runtime,
Boost, JsonCpp, readline, pinned CaDiCaL, and zlib. LLVM is optional for a core-only build.
See [the SAT backend guide](CADICAL_BACKEND.md) to build the external static solver.
On a system with those dependencies installed, run from the repository root:

```bash
autoreconf -vif
tar xfj microcode.tar.bz2
./configure --disable-llvm2smv --with-cadical-prefix=/path/to/cadical-prefix CXXFLAGS='-std=c++20 -O2 -g -Wall -Wno-deprecated-declarations -Werror'
make -j4
YASMV_HOME="$PWD" make test
```

Use `--enable-llvm2smv` to include the LLVM 18 frontend. M0 disables the old
unsound translator and tests IR inventory, diagnostics, and rejection without
SMV output. M1 adds internal typed-model fixtures, native writer validation,
and atomic bundle publication tests. M2 adds admitted scalar LLVM execution
and native semantic regressions. M3 adds acyclic direct calls, verifier hooks,
a controlled C driver, source projection, and native evidence replay.
M4 adds bounded byte memory, provenance, aggregates, and explicit memory coverage
obligations. M5 adds bounded call frames, recursion, and dynamic stack storage
with separate resource results. See [the frontend guide](../llvm2smv/README.md).

`make reliability-test` builds a separate C++ regression executable, exercises
incremental solving and injected UNKNOWN results under all eight combinations
of the supported CNF passes, and runs the Python process/harness regressions.
Python 3 is required for this test target. The existing short, unit, and
functional targets remain available.

## CI and local pre-commit gates

CI runs one optimized core build with LLVM disabled, followed by two smoke
checks: native CLI trace generation/replay and agent protocol recovery/discovery.
It does not run the full regression suite, sanitizer builds, LLVM translation,
Chromium acceptance, or provenance collection.

Before committing, run the full regression gate on the normal build:

```bash
YASMV_HOME="$PWD" make test
```

Keep the following checks local as well:

- LLVM: configure a normal build with `--enable-llvm2smv`, build it, and run
  `YASMV_HOME="$PWD" make test`. This includes the M0 frontend contract tests (`make llvm-test`).
- Sanitizers: use a fresh checkout containing the changes being tested, or a
  clean rebuild, to avoid mixing normal and instrumented objects. Configure
  and run the focused gate as follows:

```bash
./configure --disable-llvm2smv \
  CXXFLAGS='-std=c++20 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer'
make -j4
ASAN_OPTIONS=detect_leaks=0 \
UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
YASMV_HOME="$PWD" make reliability-test query-test workbench-test \
  developer-workflow-test analysis-test cli-test
```

Leak detection is deferred because managers still own objects for the lifetime
of the process; invalid accesses and undefined behavior remain enabled. Use
an optimized normal build for the full functional suite, whose per-case time
limits can be exceeded under sanitizers.

- Browser: run the Chromium acceptance commands in
  [WORKBENCH.md](WORKBENCH.md#verification) against a normal build.
- Provenance: run
  `python3 tools/build-provenance.py --output /tmp/yasmv-provenance.json`
  to record the source revision, toolchain, linked libraries, configuration,
  and SHA256 inventory of the actual arithmetic fragments.

## Supported CNF transformations

Tautology removal, duplicate removal, and subsumption remain supported. Each
can be enabled or disabled independently. Incremental tests cover changing
assumption polarities, clauses added after solving, and model values checked
against the original constraints.

The custom `--cnf-blocked-clause`, `--cnf-variable-elimination`, and
`--cnf-self-subsumption` options reject enabled values. The first two have known
correctness/indexing problems; the self-subsumption implementation also lacks
a validated literal-matching contract. The flags remain recognized, so scripts
receive an explicit error instead of silently changing behavior. These custom
passes are separate from the SAT solver's internal preprocessing.

Before a quarantined pass returns, it must preserve assumptions, committed and
future clauses, and observable assignments; protect externally used variables;
support reconstruction when needed; and pass incremental and sanitizer tests.

## Model validation and root selection

Queries require successful parsing, semantic/type analysis, and guard checks.
Overlapping assignment guards and asynchronous validation exceptions now fail
model loading. `--fsm-inertial-checks no` is rejected: validation is required.
The guard rule remains conservative and checks exclusivity without relying on
model invariants.

A model containing one module selects that module automatically. Multiple
modules require an explicit root:

```bash
YASMV_HOME="$PWD" ./yasmv --root controller system.smv
```

The root is stored explicitly, so reordering declarations does not change it.
Unknown roots fail with a diagnostic. Legacy models that depended on unordered
container iteration must specify the intended root.

One process supports one model-load attempt. A second `read-model` is rejected;
a previously valid model remains available. Following a failed first load,
start a new process. Transactional replacement and owned sessions remain later
milestones.

## Results, enumeration, and batch status

Solver UNKNOWN remains inconclusive. `last` reports `INCONCLUSIVE`, and `on`
does not execute either its success or failure branch for that result. EOF and
`quit` cannot erase an earlier batch execution error. Empty/long command lines
are handled without a fixed-size input buffer.

| Batch exit | Meaning |
| --- | --- |
| 0 | Commands completed; a legitimate UNSAT/unreachable outcome is allowed |
| 2 | Invalid input, failed validation, or invalid command execution |
| 3 | Inconclusive/interrupted computation or an incomplete limited enumeration |
| 4 | Unexpected standard-library exception during command execution |

The first recorded batch execution failure is retained across later successful
commands. Interactive sessions continue to permit recovery between commands.
The future structured query API will carry per-request status independently.
Compound `do` commands stop on an inconclusive result. Failed environment
lookups and trace loads also set the batch error status.

Trailing model/command tokens are rejected instead of silently ignored. The maze
example now explicitly runs plain reachability, preserving what its old script
actually executed. To add a timed reachability constraint use `-c`; the retired
`-f` spelling is rejected.

`pick-state` reports a discovered state as **at least one** rather than claiming
uniqueness. Counting and enumeration cover the whole state valuation, including
unconstrained and frozen variables. A supplied positive limit saves the final
witness before stopping. Reaching the limit reports an incomplete result;
exhaustion is claimed only after UNSAT. Zero limits are rejected by both
`pick-state` and `check-trans`.

## Regression coverage

The regressions retain the original mixed-signedness relational crash and
smaller positive comparisons, widening casts, contradictory initial states,
invalid/overlapping guards, explicit root selection, batch errors, incomplete
enumeration, and exact counts for small models. The test harness itself is
exercised with fake checkers that emit `KO`, crash, return nonzero, or time out.
Such failures can no longer be reported as passing semantic tests.

## Local verification (2026-09-26)

A clean core-only build with GCC, C++20, `-O2`, and warnings treated as errors
passes `make test`:

- 32 existing C++ unit tests;
- all 43 active short cases and 13 functional cases;
- 23 Python process and harness regressions;
- 3 focused C++ regression cases under each of 8 supported CNF configurations.

The LLVM-enabled build also passes the full suite, including three subsequently
added command-propagation regressions (26 Python tests total). The translator
was rebuilt and its counter translation smoke test ran with LLVM/clang 18.1.3.
Hosted CI execution remains separate from these local results.

ASan/UBSan runs also pass the unit tests, all active short cases, the initial
23 process regressions, and the focused C++ configuration matrix. The full functional
suite exceeded its 60-second per-case limit in the unoptimized sanitizer build;
functional coverage above uses the clean optimized build. These are local
acceptance results; the current CI policy is the lightweight gate described
above.

The packaged arithmetic inventory contains 2,432 fragments. Its manifest
SHA256 is
`3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.
Regenerate the provenance report for each checkout and build; this digest
identifies the tested fragments, not a proof of their arithmetic semantics.
