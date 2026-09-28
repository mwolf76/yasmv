# CaDiCaL milestone 6: performance comparison and dependency cleanup

This completes the remaining work in the [migration plan](../../cadical_integration.md).
The production solver is pinned CaDiCaL 3.0.1 at
`c60730422e758ef1cebe7aeddf2dda31c996bf04`, with the `inprobing=0` policy
validated in [milestone 5](../CADICAL_MIGRATION_VALIDATION.md).

## Matched end-to-end comparison

The unchanged `tools/benchmark-sessions.py` runner collected five fresh-process
and five warm-session samples per model, plus a separately recorded initial
session sample. Cases ran sequentially with no competing build or test workload.
The compared [MiniSat baseline](cadical-m1-minisat.md) and CaDiCaL runs have the
same machine/platform, Python 3.13.5, GCC 14.2, C++ flags, model source SHA-256,
query/depth, root, inputs, microcode revision, word width, and CNF settings.

| Case | MiniSat fresh (ms) | CaDiCaL fresh (ms) | Change | MiniSat warm (ms) | CaDiCaL warm (ms) | Change |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Faulty retry protocol | 1522.52 | 1525.58 | +0.20% | 607.39 | 608.85 | +0.24% |
| Deduplicating retry protocol | 1531.34 | 1547.30 | +1.04% | 612.63 | 620.35 | +1.26% |

Entries are medians. Both backends return the same semantic results: reachable
with certified shortest depth 5 for the faulty protocol, and unreachable through
depth 12 for the deduplicating protocol. The latter is not an unbounded proof.
The runner also requires matching status, outcome, optimality, and identity
between fresh and cached runs within each backend.

The measurements are broadly similar on these small end-to-end workloads; five
samples do not establish a statistically significant change or general SAT
scalability. Fresh timings include startup/model loading, and warm timings
include session fingerprinting/request overhead. Solver identity and native
defaults intentionally differ: the old MiniSat seed is 91648253, while the
CaDiCaL seed is 0. The identity's `model_revision` also changes because it hashes
solver/options provenance, not just source. This compares the shipped backend
configurations, not two algorithms under equivalent internal heuristics.

Raw samples, exact compiler flags, binary/model hashes, and complete identities:

- [CaDiCaL reachable](cadical-m6-reachable.json) and [MiniSat reachable](cadical-m1-minisat-reachable.json).
- [CaDiCaL bounded-unreachable](cadical-m6-unreachable.json) and [MiniSat bounded-unreachable](cadical-m1-minisat-unreachable.json).

The measured solver implementation is commit `43671d2f`; this milestone changes
build cleanup, comments, and documentation, not solving behavior. Historical
baseline files remain unchanged. The clean rebuild after cleanup reproduced
the measured checker SHA-256 exactly:
`73e89a06d675f5beac760494965568ce605361c66a27731fe3f176c7ecf2ee9f`.

Reproduce after building with the milestone 1 compiler flags and pinned solver:

```sh
python3 tools/benchmark-sessions.py \
  --model examples/retry-protocol/faulty.smv --target DUPLICATE --depth 12 \
  --runs 5 --output /tmp/cadical-reachable.json
python3 tools/benchmark-sessions.py \
  --model examples/retry-protocol/deduplicating.smv --target DUPLICATE --depth 12 \
  --runs 5 --output /tmp/cadical-unreachable.json
```

Unset unsupported native `CADICAL_*` overrides, as in the recorded runs.

## Dependency cleanup

- Remove the unused `AC_MINISAT` configure macro and obsolete Trusty installer
  that still installed MiniSat. The README now uses the actual core CI package
  list and links the pinned external CaDiCaL build instructions.
- Remove stale MiniSat `sat/core` and `sat/mtl` include paths from four build
  definitions and update active solver comments/developer guidance.
- Update the SAT manual to describe the fixed inprobing policy and provenance.
- Keep retired-option diagnostics and dependency guards, which intentionally
  mention MiniSat. Preserve historical benchmarks and review findings, with
  explicit pointers to current CaDiCaL documentation.
- Add the integration plan and both baseline/comparison reports to the source
  distribution manifest alongside the migration documentation.

## Acceptance

- Clean rebuild: `make clean`, `autoreconf -vif`, explicit LLVM-enabled configure,
  and `make -j4`, including all four native test executables, passed. C++ warnings
  are treated as errors, using the same flags as the MiniSat baseline.
- Configure validates the pinned static archive and exposes only the CaDiCaL
  dependency prefix. The link command names `libcadical.a`; `ldd` reports no
  MiniSat library, `nm -C` shows CaDiCaL solver symbols and no MiniSat symbols,
  and generated compiler dependency files contain no MiniSat headers. Existing
  system packages were not uninstalled for this audit.
- All 2,432 arithmetic fragments remain unchanged. Manifest SHA-256:
  `3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.
- Full core/LLVM regression gate: passed on the first run after cleanup, exit 0,
  in 872.593 seconds with three make jobs. No tests were skipped and no assertions
  or timeouts were relaxed. This includes all eight adapter CNF configurations,
  the full query/session suites, and all LLVM scalar, C, memory, and stack tests.
- The standalone pinned API gate passed all 10 native checks and eight runner
  tests. Focused sanitizer evidence is recorded in milestone 5; this cleanup
  does not change runtime implementation or the resulting binary.

The full gate used the baseline's isolated Python environment with `jsonschema`
4.26.0 so optional schema checks ran:

```sh
PATH="/tmp/yasmv-cadical-m1.vYtNeq/venv/bin:$PATH" YASMV_HOME="$PWD" make -j3 test
make cadical-api-test CADICAL_SOURCE=/path/to/pinned/cadical
```

An additional `make dist` check failed before archive creation because the
unchanged `src/common/Makefile.am` lists a nonexistent `logging.hh`. That
pre-existing general packaging defect is outside this solver migration and is
not repaired or counted as a passing check here. The new report files are listed
in the distribution manifest, but no working source archive is claimed.
