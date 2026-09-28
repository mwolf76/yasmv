# CaDiCaL milestone 3: owned SAT types

This preparatory milestone keeps MiniSat as the production solver while removing
its types and headers from the public SAT interface. It implements milestone 3
of the [integration plan](../cadical_integration.md), not the backend switch.

## Interface and representation

- `sat::Var` remains a signed, zero-based integer. `MAINGROUP` remains zero.
- `sat::Lit` owns its packed integer representation, `2 * variable + sign`.
  Negation toggles the low bit; ordering and microcode decoding are unchanged.
  Construction rejects negative packed literals and variable IDs that would
  overflow the representation, including in release builds.
- `sat::Lits`, `sat::LitsVector`, and `sat::Groups` use standard vectors.
  Algorithm, witness, CNF, and microcode code use these project-owned types.
- `Engine::add_clause` takes a const vector and does not alter the caller's
  clause. Conversion to native literals happens only when committing clauses or
  submitting assumptions. Failed assumptions are converted back at that boundary.
- The concrete MiniSat instance is owned through an incomplete private backend
  type. MiniSat includes, model/result decoding, configuration, and statistics
  access are confined to `engine.cc`. The unused public MiniSat `lbool` logging
  overload is removed; engine statistics retain their existing output format.

Solver options, incremental semantics, freezing, query budgets, cancellation,
CNF transformations, and build dependency/provenance remain MiniSat-based. There
is no new runtime backend selection or CaDiCaL production linkage.

## Checks

`make sat-types-test` builds and runs a standalone executable without linking any
SAT solver or yasmv library. Its checks stay active under `-DNDEBUG` and cover
65,538 packed-literal round trips, variable zero, both signs, negation, maximum
IDs, invalid bounds, ordering, and vector copy/empty-clause behavior.

The normal reliability suite adds checks for the main-group zero convention,
negative failed groups and later reactivation, non-mutating clause submission,
empty/nonempty logging, and packed microcode loading for signed/unsigned
addition, multiplication, and comparison. These run under all eight supported
CNF-option combinations. A compile-time guard rejects transitive MiniSat headers
in engine client code.

The 2,432 arithmetic fragments remain unchanged, with manifest SHA-256:
`3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.
This matches the [MiniSat baseline](benchmarks/cadical-m1-minisat.md).

Standalone release and sanitizer checks can be reproduced from the repository
root without an installed solver:

```sh
type_work=$(mktemp -d /tmp/yasmv-sat-types.XXXXXX)
c++ -std=c++20 -O2 -DNDEBUG -Wall -Wextra -Werror -I src \
  tests/test_sat_literals.cc -o "$type_work/literal-release"
"$type_work/literal-release"
c++ -std=c++20 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer \
  -Wall -Wextra -Werror -I src tests/test_sat_literals.cc \
  -o "$type_work/literal-sanitize"
ASAN_OPTIONS=detect_leaks=1 UBSAN_OPTIONS=halt_on_error=1 \
  "$type_work/literal-sanitize"
```

## Verification

Local verification on 2026-09-28 used GCC 14.2 and LLVM/Clang 18.1.8:

- `autoreconf -vif` and `make -j4`: passed with warnings treated as errors.
- `make sat-types-test`: passed; dependency inspection confirms the standalone
  executable links no solver library.
- Standalone release (`-DNDEBUG`) and ASan/UBSan builds: passed, with leak
  detection enabled and no sanitizer diagnostics.
- Expanded reliability tests: all four cases passed for each of the eight
  supported CNF-option combinations.
- `make cadical-api-test`: all 10 pinned API checks and eight runner tests passed.
- Full core/LLVM gate: passed on the first run, exit status 0, in 1188.426 seconds.
  No tests were skipped and no existing timeouts or assertions were relaxed.

The full gate used the same isolated Python environment as the baseline, with
`jsonschema` 4.26.0 installed to exercise optional schema checks:

```sh
PATH="/tmp/yasmv-cadical-m1.vYtNeq/venv/bin:$PATH" YASMV_HOME="$PWD" make -j3 test
```

All core, query, workbench, explanation, scenario, analysis, session, CLI,
progress, and LLVM suites pass. The latter include frontend, typed-model,
scalar, C, memory, and stack tests. A final provenance check confirms the
microcode manifest still matches the baseline.

Local logs and provenance are under `/tmp/yasmv-cadical-m3.HmiyPD/`, including
`build.log`, `focused-build.log`, `focused.log`, `literal-release.log`,
`literal-sanitize.log`, `cadical-api.log`, `test.log`, and
`provenance-final.json`. These paths record this local run, not reproduction
prerequisites.
