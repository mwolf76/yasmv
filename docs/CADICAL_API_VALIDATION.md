# CaDiCaL milestone 2: pinned API validation

This milestone adds a standalone test of the public C++ API required by the
[integration plan](../cadical_integration.md). The production checker still
links MiniSat. No arithmetic microcode, solver adapter, CLI tuning option, or
query contract changes in this milestone.

## Reproduce

The gate requires an explicit, unmodified Git checkout at
`c60730422e758ef1cebe7aeddf2dda31c996bf04` (`rel-3.0.1`) and its prebuilt static
library. The runner checks the checkout root, revision, tracked modifications,
and required files before compiling. The executable also checks the linked
library's runtime version. It neither downloads nor installs dependencies.

From the yasmv repository root:

```sh
cadical_work=$(mktemp -d /tmp/yasmv-cadical.XXXXXX)
git clone --depth 1 --branch rel-3.0.1 \
  https://github.com/arminbiere/cadical.git "$cadical_work/cadical"
test "$(git -C "$cadical_work/cadical" rev-parse HEAD)" = \
  c60730422e758ef1cebe7aeddf2dda31c996bf04
(cd "$cadical_work/cadical" && ./configure -c -fPIC && \
  make -C build -j4 libcadical.a)
python3 tools/test-cadical-api.py --source "$cadical_work/cadical"
```

After regenerating the yasmv makefiles, the equivalent target is:

```sh
make cadical-api-test CADICAL_SOURCE="$cadical_work/cadical"
```

The direct runner also accepts `--build` for an alternative library directory,
`--cxx`, `--cxxflags`, and a finite positive `--timeout` for the test executable
(60 seconds by default). Compilation has a separate 120-second limit. Builds
and executions use a temporary directory which is cleaned up afterwards.

To instrument both the library and the probe with sanitizers:

```sh
mkdir "$cadical_work/cadical/build-sanitize"
(cd "$cadical_work/cadical/build-sanitize" && \
  ../configure -g -O1 -fPIC -fsanitize=address,undefined \
    -fno-omit-frame-pointer && make -j4 libcadical.a)
ASAN_OPTIONS=detect_leaks=1 UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
  python3 tools/test-cadical-api.py --source "$cadical_work/cadical" \
    --build "$cadical_work/cadical/build-sanitize" \
    --cxxflags='-g -O1 -fsanitize=address,undefined -fno-omit-frame-pointer'
```

This is an explicit gate rather than an unconditional dependency of `make test`
until the production backend is replaced. A separate CI job builds the pinned
library with assertions enabled and runs the gate. The probe and runner are
included in source distributions.

Eight runner unit tests cover successful command construction and temporary
cleanup, wrong revision/root, modified tracked sources, missing build files,
compiler failures, executable failures/timeouts, and invalid timeout values.
These need no CaDiCaL installation and run as part of the normal `make test`
gate as well as `make cadical-api-test` and the dedicated CI job.

## Contracts exercised

The tests use explicit checks, not C assertions, so `-DNDEBUG` cannot disable
them. Small formulas have directly checkable semantics; pigeonhole formulas
exercise search and stopping without relying on elapsed-time sleeps.

| Check | Integration consequence |
| --- | --- |
| Runtime version and option validation | Verify the linked release and reject unknown options/statistics |
| Explicit allocation and reference-counted freezing | Map internal zero-based IDs to allocated backend IDs; balance freeze/melt calls |
| Incremental selectors and an empty clause | Preserve SAT/UNSAT transitions, selector polarity, and unconditional contradictions |
| Positive/negative failed assumptions and core recheck | Copy the signed core before changing state; reapply assumptions on every solve |
| Enumeration of two unused variables | Obtain complete Boolean valuations and block all four models exactly once |
| Preprocessing with `factor` enabled and later clauses | Read reconstructed models; allocate through the solver and reuse unfrozen variables incrementally |
| Repeated conflict limits and cumulative counter deltas | Reapply limits per solve and accumulate job-wide usage outside the backend |
| Pre-requested termination and solver reuse | A callback can stop search and a later solve can resume after clearing the request |
| Cross-thread cancellation handshake | The cancelling thread need only write an atomic flag; solver access stays on its owner thread |
| Propagation threshold via callback | Read the search counter while solving and stop cooperatively, allowing overshoot |

The factor-enabled test checks allocation against the solver's reported maximum
and enforces declared-variable contracts. It does not require a particular
preprocessing heuristic to introduce extension variables on its small fixture.
The cancellation handshake establishes that a request arrives during a callback;
it is not a wall-clock latency benchmark or a production callback implementation.

## Findings to carry into the adapter

- The pinned header defines `CADICAL_PATCH` as `0`, despite runtime
  `Solver::version()` returning `3.0.1`. Do not use that macro alone for the
  release identity or a patch-level version check.
- Backend variable zero is not a literal: zero terminates a clause. The first
  allocated backend variable is 1, whereas yasmv reserves internal variable 0
  for its main group/constant convention.
- Declaring a variable after SAT invalidates the current model state. Allocate
  observable bits before solving and avoid allocating in witness decoding.
- `val()` returns a signed satisfying literal, including for unused declared
  variables. Translate it to a Boolean; do not interpret it as MiniSat's
  three-valued integer encoding.
- Failed assumptions and models must be read in the appropriate result state.
  Copy failed groups before assumptions or clauses are changed. Cores need not
  be minimal, so retain yasmv's independent core recheck.
- There is no `limit("propagations", ...)`; it returns false. The public
  propagation statistic counts search propagations. The probe's threshold of
  1 stopped at 7 in the tested build; that number is an observation, not an
  asserted bound or a portable expectation.
- The callback should only inspect atomic cancellation state and safe counters.
  Preserve the adapter's pre-solve zero-budget/cancellation checks and post-solve
  stop-reason precedence: a trivial answer need not enter the search loop.
- The public conflict-limit argument is `int`; the later adapter must handle
  yasmv's 64-bit query budgets without narrowing or inventing a propagation-limit
  mapping to another resource such as decisions.

Upstream references:

- [Public API](https://github.com/arminbiere/cadical/blob/c60730422e758ef1cebe7aeddf2dda31c996bf04/src/cadical.hpp)
- [Counter implementation](https://github.com/arminbiere/cadical/blob/c60730422e758ef1cebe7aeddf2dda31c996bf04/src/solver.cpp)
- [Limit implementation](https://github.com/arminbiere/cadical/blob/c60730422e758ef1cebe7aeddf2dda31c996bf04/src/limit.cpp)

## Verification

Local checks on 2026-09-28 used GCC 14.2 and the exact pinned checkout:

- `autoreconf -vif` and `make -j4`: passed.
- `make cadical-api-test`: all 10 API checks and eight runner tests passed.
- Probe compiled with `-O2 -DNDEBUG`: all 10 API checks passed.
- Library and probe compiled with AddressSanitizer and UndefinedBehaviorSanitizer:
  all 10 API checks passed with leak detection enabled, without diagnostics.

The first full `make -j3 test` run failed after 1467.349 seconds because
`StackTests.test_recursive_local_objects` exceeded its existing 180-second
subprocess limit. The isolated test then passed unchanged in 24.729 seconds.
The rebuilt `yasmv` and `llvm2smv` binaries have the same SHA-256 hashes as the
[milestone 1 baseline](benchmarks/cadical-m1-minisat.md); neither production code
nor existing test limits/assertions changed. This is evidence of timing
variability, not a diagnosis of its underlying cause.

The complete rerun passed with exit status 0 in 1165.799 seconds, including all
18 stack tests and with no skipped tests:

```sh
PATH="/tmp/yasmv-cadical-m1.vYtNeq/venv/bin:$PATH" YASMV_HOME="$PWD" make -j3 test
```

The isolated Python environment supplies `jsonschema` 4.26.0 so the optional
schema validation is exercised. Core, reliability (all eight CNF-option
combinations), query, workbench, progress, and all LLVM suites pass, as do the
eight new runner tests included in this gate.

Local logs are under `/tmp/yasmv-cadical-m2.2WkdyH/`: `api-test.log`,
`release-api-test.log`, `sanitize-test.log`, the initial `test.log`,
`stack-focused.log`, and the passing `test-rerun.log`. These temporary paths are
local evidence, not prerequisites for reproducing the tests.
