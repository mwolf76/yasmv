# CaDiCaL integration plan

Status: approved for milestone-by-milestone implementation on 2026-09-28.

Each milestone must pass the full test suite before its relevant changes are
staged and committed. Commit messages describe only the staged changes, with no
left margin or attribution.

## Objective and scope

Replace MiniSat with CaDiCaL without changing the verification algorithms or
the arithmetic microcode format. Keep `sat::Engine` as the integration boundary,
remove MiniSat-specific types from its public interface, and implement a small
CaDiCaL adapter behind it.

The proposed end state is a CaDiCaL-only backend, not a runtime-selectable
multi-solver framework. This document records the inspection findings and
approved work. Progress and verification evidence are recorded below.

## Existing integration

The main implementation is in [src/sat/engine.hh](src/sat/engine.hh) and
[src/sat/engine.cc](src/sat/engine.cc). `Engine` owns a
`Minisat::SimpSolver` and provides:

- Incremental clause addition and repeated solving.
- Assumption-based formula groups, including polarity changes.
- Model values and failed-assumption groups.
- Interruption, conflict/propagation budgets, and statistics.
- Variable freezing and optional yasmv-side CNF transformations.

The dependency extends beyond that class:

| Area | Existing coupling |
| --- | --- |
| Types and CNF generation | `Var`, `Lit`, `vec`, and literal operations come from MiniSat |
| Arithmetic microcode | JSON stores packed literals, decoded through `Minisat::toLit()` |
| Algorithms and witnesses | Construct clauses and read solver assignments |
| Query runtime | Accumulates solver budgets across solves and handles cancellation |
| CLI | Exposes 18 MiniSat tuning parameters |
| Build and provenance | Links MiniSat, installs it in CI, and identifies it in query results |

The microcode coupling is particularly important: this must not become a
migration of the arithmetic artifact format.

## CaDiCaL API and release selection

Pin upstream `rel-3.0.1`, inspected at commit
`c60730422e758ef1cebe7aeddf2dda31c996bf04`, rather than following `master`.
Its release notes include improved termination responsiveness and changes
relevant to incremental variable allocation.

The C++ interface provides the necessary primitives:

| Current operation | CaDiCaL equivalent |
| --- | --- |
| Add clause | `add(literal)`, terminated by `add(0)` |
| Allocate variable | `declare_one_more_variable()` |
| Solve with assumptions | `assume()` followed by `solve()` |
| SAT / UNSAT / UNKNOWN | Return codes `10` / `20` / `0` |
| Read assignment | `val()` |
| Extract assumption core | Test submitted assumptions with `failed()` |
| Freeze variable | `freeze()` / `melt()` |
| Stop solving | Connected `Terminator` callback |
| Conflict budget | `limit("conflicts", ...)` |

Assumptions and limits must be reapplied for subsequent solves. Model values
and failed assumptions have strict state requirements. Use the native C++ API
rather than plain IPASIR because the integration also needs variable management,
configuration, and statistics.

References:

- [Release notes](https://github.com/arminbiere/cadical/blob/rel-3.0.1/NEWS.md)
- [C++ API](https://github.com/arminbiere/cadical/blob/rel-3.0.1/src/cadical.hpp)

## Integration design

### 1. Own SAT types and preserve microcode

Replace the MiniSat aliases in
[src/sat/typedefs.hh](src/sat/typedefs.hh) with small yasmv-owned types and
standard containers.

Preserve:

- Zero-based internal variable IDs.
- Packed literal encoding: `2 * variable + sign`.
- Existing microcode files and their checksums.
- `MAINGROUP == 0` and existing group activation semantics.

Translate literals only at the backend boundary. Maintain an explicit mapping
from yasmv variables to CaDiCaL's allocated IDs; do not assume a permanent
`variable + 1` relationship. CaDiCaL's extension-variable machinery makes
explicit allocation important.

This requires mechanical changes in CNF generation, simulation, logging, and
tests, but no arithmetic regeneration.

### 2. Preserve incremental and evidence semantics

Introduce a concrete CaDiCaL backend owned by `Engine`, keeping its headers out
of algorithm-facing interfaces. A runtime-selectable multi-solver framework is
unnecessary for this replacement.

The adapter will:

- Reapply the current group assumptions on every solve.
- Capture failed groups immediately after UNSAT, preserving their signs.
- Invalidate stale models and cores when the formula changes.
- Initially preserve semantic-variable freezing and protect selectors.
- Ensure all witness/state variables are allocated before solving.
- Handle unconstrained variables consistently in witness decoding and
  enumeration.

The current explanation code already rechecks extracted cores; retain that
validation. Audit model-reading paths because allocating a new backend variable
after SAT can invalidate the assignment.

### 3. Handle budgets and cancellation explicitly

This is the main compatibility decision.

CaDiCaL exposes conflict and propagation counters, but its public limit
interface does not offer a propagation limit. Its propagation counter measures
search propagations, not every preprocessing propagation.

Proposed behavior:

- Preserve query-wide accounting using counter deltas across solves.
- Apply native conflict limits where representable.
- Use a termination callback for propagation-budget checks and cancellation.
- Let timer/cancellation threads set an atomic flag; keep ordinary solver
  access on the solving thread.
- Preserve zero-budget behavior, interruption before solving, and existing
  stop-reason precedence.
- Handle the mismatch between yasmv's 64-bit budgets and CaDiCaL's `int` limit
  argument explicitly.

Propagation limits would become cooperative thresholds, with possible overshoot
between callbacks. Document that change rather than claiming exact
MiniSat-equivalent enforcement. If exact propagation-limit behavior is required,
that needs a separate decision before implementation.

References:

- [Limit implementation](https://github.com/arminbiere/cadical/blob/rel-3.0.1/src/limit.cpp)
- [Statistics implementation](https://github.com/arminbiere/cadical/blob/rel-3.0.1/src/solver.cpp)

### 4. Replace configuration and reporting

Use CaDiCaL defaults initially, with solver output suppressed so machine-readable
responses remain clean.

For CLI compatibility:

- Retain `--sat-random-seed` with explicit integer/range validation.
- Reject other explicitly supplied MiniSat-only tuning flags with migration
  guidance.
- Add only a small, documented CaDiCaL option set initially.
- Keep the supported yasmv CNF passes unchanged; do not re-enable quarantined
  transformations.

Update statistics logging and replace the hard-coded
`yasmv-0.0.10/minisat` identity in [src/query/query.cc](src/query/query.cc).
Record the actual solver version and build revision in provenance. Historical
benchmark records should remain historical.

### 5. Replace the build dependency

Replace `AC_MINISAT` with a CaDiCaL compile/link capability check, and update
executable/test linkage, CI, dependency instructions, and SAT documentation.

Use an external, pinned dependency with static linkage initially:

- Support a custom installation prefix.
- Build the pinned release in CI.
- Verify the actual APIs used, not merely the presence of a header.
- Keep dependency downloads outside normal `configure`.

Upstream builds `libcadical.a` and supplies `src/cadical.hpp`; no change from
Autotools is required. See the
[upstream build instructions](https://github.com/arminbiere/cadical/blob/rel-3.0.1/BUILD.md).

## Implementation sequence and acceptance gates

Execute in order, completing the test and commit gate for each milestone:

1. Capture the MiniSat baseline: test outcomes and representative timings.
2. Validate the pinned API with focused checks for allocation, incremental
   assumptions, model completion, counters, and termination.
3. Introduce owned SAT types while preserving packed literals and existing
   behavior.
4. Implement and wire CaDiCaL: backend, budgets, configuration, build, and
   provenance.
5. Run migration validation:
   - Literal conversion, variable zero, empty clauses, and microcode constants.
   - SAT to UNSAT to SAT with changed groups and later clauses.
   - Failed-core reproduction and stale-result prevention.
   - Unconstrained-state enumeration and witness replay.
   - Nonzero budgets, cumulative accounting, cancellation, and session recovery.
   - All eight supported CNF-option combinations.
   - Full core and LLVM suites, plus focused sanitizer checks.
6. Compare performance and remove remaining active MiniSat dependencies.

Different valid witnesses, core subsets, and enumeration orders are expected.
Tests should verify correctness rather than require MiniSat's particular
choices.

## Approved decisions

- CaDiCaL-only backend, pinned to `rel-3.0.1`.
- External dependency with static linkage initially.
- Unchanged arithmetic microcode and packed literal format.
- Explicit retirement of MiniSat tuning flags, retaining the validated seed
  option.
- Cooperative propagation budgets with documented counter semantics and
  possible overshoot.

## Milestone progress

| Milestone | Status | Evidence |
| --- | --- | --- |
| 1. MiniSat baseline | Complete | [Full regression gate, provenance, and representative timings](docs/benchmarks/cadical-m1-minisat.md) |
| 2. Pinned CaDiCaL API validation | Complete | [Standalone API contracts, sanitizer checks, full regression gate, and integration findings](docs/CADICAL_API_VALIDATION.md) |
| 3. Owned SAT types | Pending | |
| 4. CaDiCaL integration | Pending | |
| 5. Migration validation | Pending | |
| 6. Performance comparison and dependency cleanup | Pending | |
