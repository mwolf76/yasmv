# CaDiCaL migration validation (milestone 5)

This milestone audits the production adapter and evidence paths introduced in
[milestone 4](CADICAL_BACKEND.md). With approval, narrowly scoped solver tuning
was brought forward to address the full-suite deadline failures. The broader
performance comparison and remaining dependency cleanup stay in milestone 6.

## Coverage

| Contract | Validation |
| --- | --- |
| Packed literals, variable zero, empty clauses | Standalone literal round trips/bounds and adapter main-group/empty-clause tests |
| Arithmetic artifacts | Packed microcode loader checks, full arithmetic regressions, unchanged fragment manifest |
| Incremental groups and later clauses | SAT/UNSAT/SAT regressions and 384 independently enumerated small-formula cases per CNF configuration |
| Model and failed-core correctness | Check every SAT assignment against the original clauses; check UNSAT and each signed core against exhaustive truth tables and replay the core |
| Result lifetime | Allocation, clauses, and group updates invalidate models/cores; rejected group updates leave the prior result intact |
| Unconstrained bits | Enumerate all 16 four-bit assignments without imposing solver order |
| Observable model completion | Count 24 mixed Boolean/array/enum states and replay a reachability witness under all eight supported CNF configurations |
| Budgets | Zero/nonzero conflict and propagation limits, 64-bit limits, reconfiguration, multiple solves and engines, first-stop precedence |
| Cancellation/recovery | Cross-thread interruption around active solving, fresh-context reuse, cached-session budget recovery, existing process/session cancellation gates |

The small-formula oracle uses a fixed random seed to build guarded clauses, then
enumerates all 256 assignments independently. It tests every group-polarity
tuple after each of three incremental clause batches. It does not depend on
CaDiCaL's chosen models, core size, or enumeration order.

## Audit finding: mutable groups bypassed invalidation

Previously `groups()` returned a mutable reference. Although obtaining that
reference invalidated the current result, retaining it across a solve allowed
later edits without invalidating the new model/core. Read-only access also
invalidated results unnecessarily.

The interface now provides read-only `groups()` and copy-in `set_groups()`.
The setter validates the entire update before changing any state and invalidates
results only for accepted updates. The explanation service uses this explicit
mutation boundary. A compile-time check prevents reintroducing a mutable getter;
runtime checks cover SAT and UNSAT invalidation and invalid signed IDs.

Model-reading paths in reachability, simulation, trace decoding, and enumeration
use lookup-only access to preallocated semantic bits. The normal explanation
service continues to verify extracted cores before publishing them.

## Verification

Local validation used GCC 14.2, LLVM/Clang 18.1.8, and pinned CaDiCaL 3.0.1:

- Normal build passed with warnings treated as errors.
- All 11 adapter reliability cases passed for each of the eight supported CNF
  configurations, including 3,072 small-formula/assumption combinations and
  independent failed-core checks.
- The new mixed-type enumeration/replay and cached-session budget-recovery
  tests passed. The new session fixture initially omitted required request IDs;
  that fixture error was corrected before the full gate.
- The isolated ASan/UBSan build, rebuilt with the final tuning policy, passed
  the literal tests, all eight adapter runs, eight native query cases, six
  focused process-query tests, cached-session recovery, and arithmetic core
  reproduction. No sanitizer diagnostics occurred.
- The standalone instrumented CaDiCaL API gate passed all 10 checks with leak
  detection enabled.
- All 2,432 microcode fragments are unchanged. Manifest SHA-256:
  `3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.

The first full core/LLVM run overlapped the sanitizer compilation and timed out
in the existing 16×16 maze functional test (exit 124, unchanged 60-second limit).
All LLVM suites passed. The isolated maze rerun passed unchanged. A second full
run passed the maze and all core-side tests, but the LLVM C workflow's
`test_safe_unsafe_source_evidence_and_native_execution` hit its existing
60-second tool deadline. That test then passed unchanged in isolation in
39.208 seconds. A serial full-suite run also timed out in that same C test;
the initial full-suite acceptance gate was therefore not satisfied. No existing
assertions or per-test timeouts were relaxed.

Focused reruns with the same Python environment and working directory passed,
so changing only concurrency does not resolve the variability. A diagnostic
run on a saved safe-model artifact timed out during bounded property checking.
A sampled stack was inside CaDiCaL's congruence/gate-rewriting inprocessing.
Disabling only congruence for one diagnostic process did not fix the deadline:
it returned UNKNOWN after checking depths 0 through 42 of the requested 45,
with approximately 57.5 seconds solving, 0.76 seconds encoding, and 0.12 seconds
compiling. No production option change was made from that experiment.

### Incremental-workload tuning

With approval to bring tuning forward, the saved bounded LLVM job was tested
with `CADICAL_INPROBING=0`. All four diagnostic runs completed through depth 45
with `holds_bounded`, taking 18.5, 15.5, 25.6, and 47.9 seconds respectively
(the last run overlapped compilation). The upstream `inprobe` schedule includes
congruence extraction, probing, sweeping, vivification, and related passes;
disabling congruence alone did not avoid the timeout.

The production adapter now explicitly sets `inprobing=0`, disabling that
schedule while preserving other native optimizations, frozen variables,
incremental assumptions, and all budget/cancellation semantics. This is a
workload-specific policy, not a claim that inprobing is generally slower.
Query/trace identities and `--solver-info` record `settings.inprobing: false`.
The native seed remains independently configurable. Other `CADICAL_*`
environment overrides are unsupported and were absent during validation.

With that policy compiled into the adapter, the first complete serial core/LLVM
gate passed (exit 0) in 1,660.372 seconds, with no skipped tests. This includes
all 11 LLVM C workflow tests, 19 memory tests, 18 stack tests, the 16×16 maze,
24 process-query tests, and eight session tests. There was no concurrent build
or sanitizer workload. This is full regression runtime, not a solver benchmark
or a timing comparison with the parallel milestone 4 run.

The full gate uses the baseline Python environment with `jsonschema` 4.26.0:

```sh
PATH="/tmp/yasmv-cadical-m1.vYtNeq/venv/bin:$PATH" YASMV_HOME="$PWD" make -j1 test
```

CI now runs the adapter reliability executable under all eight CNF combinations,
matching the local `make test` gate.

### Focused sanitizer reproduction

Use a fresh source tree containing this milestone, with the packaged microcode
extracted. Build CaDiCaL with the instrumentation flags in
[the API validation guide](CADICAL_API_VALIDATION.md), and install its header and
sanitized archive into a separate prefix. Do not mix normal and instrumented
C++ objects:

```sh
./configure --disable-llvm2smv --with-cadical-prefix=/path/to/sanitized-prefix \
  CXXFLAGS='-std=c++20 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -Wno-deprecated-declarations'
make -j3
make -j3 yasmv_reliability_tests yasmv_query_tests sat_literal_tests
export ASAN_OPTIONS=detect_leaks=0
export UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1
export YASMV_HOME="$PWD"
./sat_literal_tests
for settings in 000 001 010 011 100 101 110 111; do
  YASMV_TEST_CNF="$settings" ./yasmv_reliability_tests --log_level=error || exit 1
done
./yasmv_query_tests --log_level=error
python3 tests/test_query.py \
  QueryTests.test_cadical_provenance \
  QueryTests.test_unconstrained_states_and_replay_all_cnf_modes \
  QueryTests.test_exact_integer_array_enum_roundtrip \
  QueryTests.test_backward_trace \
  QueryTests.test_continuation_branch_and_deadlock \
  QueryTests.test_limits_and_cancellation_are_inconclusive
python3 tests/test_sessions.py SessionTests.test_solver_budget_does_not_poison_cached_session
python3 tests/test_explanations.py ExplanationTests.test_shared_arithmetic_definitions_and_disabled_selectors
```

This instruments yasmv's C++ code and CaDiCaL, not the external system libraries
or the legacy C components. Leak detection is disabled for the application gate
because process-lifetime managers retain objects, as documented in the existing
correctness baseline. The standalone CaDiCaL API gate runs separately with leak
detection enabled. No sanitizer-specific suppression of invalid accesses or
undefined behavior is used.
