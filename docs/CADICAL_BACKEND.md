# CaDiCaL backend (migration milestone 4)

The production engine uses CaDiCaL 3.0.1 at revision
`c60730422e758ef1cebe7aeddf2dda31c996bf04`. MiniSat is no longer linked.
This implements milestone 4 of the [integration plan](../cadical_integration.md).
The broader migration audit and performance comparison remain later milestones.

## Build the external dependency

Use a C++ compiler compatible with the one used for yasmv. From the repository:

```sh
cadical_work=$(mktemp -d /tmp/yasmv-cadical.XXXXXX)
git clone --depth 1 --branch rel-3.0.1 \
  https://github.com/arminbiere/cadical.git "$cadical_work/cadical"
test "$(git -C "$cadical_work/cadical" rev-parse HEAD)" = \
  c60730422e758ef1cebe7aeddf2dda31c996bf04
(cd "$cadical_work/cadical" && ./configure -c -fPIC && \
  make -C build -j4 libcadical.a)
mkdir -p "$cadical_work/prefix/include" "$cadical_work/prefix/lib"
install -m 644 "$cadical_work/cadical/src/cadical.hpp" "$cadical_work/prefix/include/"
install -m 644 "$cadical_work/cadical/build/libcadical.a" "$cadical_work/prefix/lib/"
./setup.sh --with-cadical-prefix="$cadical_work/prefix"
make -j4
YASMV_HOME="$PWD" make -j3 test
```

The prefix defaults to `/usr/local`. Normal configure/build never downloads
dependencies. Configure links the archive explicitly, exercises the APIs used,
and checks runtime version, signature, and the full revision reported by
`Solver::build()`. It rejects missing libraries, incompatible builds, and
cross-compilation environments that cannot run the check. Use a prefix without
spaces, as its path is passed through compiler/linker flags.

CI builds the same pinned archive before compiling yasmv. The standalone
`make cadical-api-test CADICAL_SOURCE=...` gate remains available for validating
an explicit upstream checkout; normal `make test` exercises the actual adapter.

## Incremental semantics

The public API still uses zero-based yasmv variables and packed literals.
Every allocation calls CaDiCaL's explicit variable allocator and saves its
returned ID. This does not assume `native = internal + 1`: preprocessing may
introduce additional native variables. The main-group zero convention and all
arithmetic microcode files are unchanged.

Semantic bits and group selectors are frozen. Each solve reapplies signed group
assumptions. Failed groups are copied immediately after UNSAT. Adding clauses,
allocating variables, or changing groups invalidates models and cores; model
reads without a current SAT result fail explicitly. Witness decoding and state
enumeration use lookup-only access to bits allocated before solving.

CaDiCaL supplies complete values for declared unused variables. Model values,
witness order, and nonminimal core membership may differ from MiniSat; evidence
must still pass independent replay/core validation.

## Budgets and cancellation

- Query budgets use cumulative counter deltas across solves and engines.
- A zero remaining budget stops before solving, even for trivial formulas.
- Conflict limits use CaDiCaL's native interface when they fit in an `int`.
  Larger 64-bit limits are checked by the termination callback, without narrowing
  or overflowing an absolute-counter addition.
- Propagation limits are cooperative thresholds on **search propagations**,
  not all preprocessing work. They can overshoot between callbacks and are not
  a strict work cap. Large conflict limits have the same callback granularity.
- Cancellation/timer threads only set an atomic request. Native solver calls,
  including counter reads in callbacks, stay on the solving thread.
- Post-solve cancellation and exhausted budgets suppress SAT/UNSAT evidence.
  The query context keeps the first stop reason; failed cores are never exposed
  for UNKNOWN. New query/session jobs get fresh engines, so cancellation does
  not poison the next job.

`Engine::configure` retains relative, cumulative per-engine budgets. Reconfiguring
starts a new allowance at current counters; `-1` is unlimited. Query-wide limits
are combined with these allowances using the tighter remaining budget.

Statistics report owned variables, submitted clauses, conflicts, and search
propagations. Submitted-clause counts are not CaDiCaL's current simplified clause
count. MiniSat-only activity/restart statistics are no longer reported.

## Options and provenance

Only `--sat-random-seed` is retained: an integer in `0..2000000000`, default
`0` (CaDiCaL's default). All other old `--sat-*` tuning flags are recognized
and rejected with migration guidance, including explicitly supplied old defaults.
The supported yasmv CNF options are unchanged. See
[SAT parameters](SAT_SOLVER_PARAMETERS.md).

`./yasmv --solver-info` prints linked solver version, signature, verified full
revision, and static linkage as JSON. The provenance script records it. Query
and trace identities include the same solver identity and the new counter/budget
semantics; their engine identity no longer names MiniSat.

## Verification

Local verification on 2026-09-28 used GCC 14.2, LLVM/Clang 18.1.8, and the
assertion-enabled pinned CaDiCaL archive (`./configure -c -fPIC`):

- `autoreconf -vif`, configure with a custom prefix, and `make -j4`: passed
  with warnings treated as errors.
- Isolated configure checks: the pinned archive passed; missing and unusable
  archives were rejected with actionable diagnostics.
- All six reliability cases passed for all eight supported CNF combinations,
  including model invalidation, signed groups, complete unused bits, nonzero
  search budgets, cumulative accounting, and pre-requested interruption.
- Focused CLI checks passed for all 17 retired options and seed boundaries;
  query checks cover linked solver provenance and cancellation/budgets.
- `make cadical-api-test`: all 10 upstream API checks and eight runner tests
  passed against the pinned checkout.
- The production link line uses the explicit static archive. `ldd` and symbol
  inspection show no MiniSat dependency or symbols. `--solver-info` reports the
  pinned full revision and static linkage.
- Full core/LLVM gate: passed on the first run, exit status 0, in 900.867 seconds.
  No tests were skipped and no existing assertions or timeouts were relaxed.

The 2,432 arithmetic fragments remain unchanged, with manifest SHA-256
`3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`,
matching the MiniSat baseline.

The full gate used the baseline's isolated Python environment with `jsonschema`
4.26.0, so optional schema checks ran:

```sh
PATH="/tmp/yasmv-cadical-m1.vYtNeq/venv/bin:$PATH" YASMV_HOME="$PWD" make -j3 test
```
