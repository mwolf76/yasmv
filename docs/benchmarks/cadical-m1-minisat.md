# CaDiCaL milestone 1: MiniSat baseline

Recorded on 2026-09-28 before changing the solver implementation. This is the
baseline for the [CaDiCaL integration plan](../../cadical_integration.md).

## Source and build identity

- Source revision: `a526d22b7a3615955466a70afceb44b1604ca78c`.
- Platform: `Linux-6.12.107+deb13-amd64-x86_64-with-glibc2.41`.
- Compiler: `c++ (Debian 14.2.0-19) 14.2.0`.
- MiniSat package: `1:2.2.1-8`, dynamically linked as `libminisat.so.2`.
- LLVM and Clang: 18.1.8; LLVM tests enabled.
- Python: 3.13.5. The test environment adds `jsonschema==4.26.0` so the optional
  schema-validation test runs rather than skips.
- `yasmv` SHA256:
  `f92816ea950047eae7fd5efc0c0d1b57f86c61790eec9c71ad6069459725b639`.
- `llvm2smv/llvm2smv` SHA256:
  `ec34c8a9352f50c6b8fd0dfd7243b3cbca2c3dd5ecae93c6c4816520c47f9c66`.
- Arithmetic fragments: 2,432 files. Manifest SHA256 from
  `tools/build-provenance.py`:
  `3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.

The existing build configuration is:

```sh
./configure --prefix=/usr/local CC=gcc CXX=g++ CFLAGS=-O2 \
  CXXFLAGS='-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -DPIC -fPIC -std=c++20 -O2 -Wall -Wno-deprecated-declarations -Werror'
```

LLVM was automatically detected. For reproduction, explicitly add
`--enable-llvm2smv` to ensure the LLVM gate is not omitted on another machine.
`make -j4` completed successfully before collecting timings and running tests.
No solver, model, microcode, or test source was changed for this milestone.

## Representative timings

The existing `tools/benchmark-sessions.py` runner collected five fresh-process
and five warm-session samples per case, plus one separately recorded initial
session sample. Both cases ran sequentially, before the regression suite, with
no concurrent test workloads from this task. The runner requires completed
results and matching status, outcome, identity, and optimality across fresh
and cached runs.

| Model and target | Result | Fresh median (ms) | Warm-session median (ms) |
| --- | --- | ---: | ---: |
| `retry-protocol/faulty.smv`, `DUPLICATE` | Reachable; certified shortest depth 5 | 1522.52 | 607.39 |
| `retry-protocol/deduplicating.smv`, `DUPLICATE` | Unreachable through depth 12 | 1531.34 | 612.63 |

The second result is bounded, not an unbounded safety proof. These small cases
are end-to-end smoke baselines, not solver scalability claims. Fresh timings
include process startup and model loading; warm timings include the session
fingerprint and request overhead. They are not isolated SAT solve timings.

Raw samples, model hashes, binary hashes, query parameters, effective options,
and result identities are preserved in:

- [Reachable case](cadical-m1-minisat-reachable.json).
- [Bounded-unreachable case](cadical-m1-minisat-unreachable.json).

Reproduce from the repository root, using new output names to retain this
historical baseline:

```sh
python3 tools/benchmark-sessions.py \
  --model examples/retry-protocol/faulty.smv \
  --target DUPLICATE --depth 12 --runs 5 \
  --output /tmp/yasmv-reachable.json
python3 tools/benchmark-sessions.py \
  --model examples/retry-protocol/deduplicating.smv \
  --target DUPLICATE --depth 12 --runs 5 \
  --output /tmp/yasmv-unreachable.json
python3 tools/build-provenance.py --output /tmp/yasmv-provenance.json
```

For a later backend comparison, compare semantic results and certified depths,
not solver identity fields, particular witnesses, or backend-specific options.
Keep the machine, build flags, models, query limits, and microcode fixed.

## Full regression gate

The final full gate passed with exit status 0 and no skipped tests. Wall time
was 1210.165 seconds (20 minutes 10 seconds), using three parallel make jobs.
This is regression-gate runtime, not a solver performance measurement.

The first full-gate attempt reached the memory suite but failed
`MemoryTests.test_c_alias_workflow_and_source_memory`: the safe C aliasing check
returned `unknown` with `reason: tool_wall_timeout` after its 60-second per-tool
limit. The stack suite was consequently not reached. A focused rerun of that
test passed in 38.713 seconds for the entire test. No timeout, assertion, or
production code was changed. The complete gate was then rerun unchanged and
passed, including all 19 memory tests and all 18 stack tests. The initial timeout
remains a baseline observation, not a claimed fixed defect.

| Suite | Tests | Result |
| --- | ---: | --- |
| Short regressions | 43 | Passed |
| Functional examples | 13 | Passed |
| C++ unit tests | 32 | Passed |
| Python reliability/process regressions | 26 | Passed |
| C++ reliability | 3 in each of 8 CNF configurations | Passed |
| C++ query tests | 8 | Passed |
| Python query tests | 22 | Passed |
| Workbench | 16 | Passed |
| Explanations | 11 | Passed |
| Scenarios | 9 | Passed |
| Analysis | 6 | Passed |
| Sessions | 7 | Passed |
| CLI | 20 | Passed |
| Progress, including schema validation | 14 | Passed |
| LLVM frontend contract | 19 | Passed |
| LLVM typed-model C++ self-tests | Self-test executable | Passed |
| LLVM typed-model Python tests | 15 | Passed |
| LLVM scalar | 15 | Passed |
| LLVM C workflow | 11 | Passed |
| LLVM memory | 19 | Passed on full-gate rerun |
| LLVM stack | 18 | Passed |

The command is `YASMV_HOME="$PWD" make -j3 test`, using the isolated Python
environment described above. It includes all core test targets, all eight
supported CNF-option combinations, and all enabled LLVM suites. Browser and
sanitizer checks are separate from `make test`; this baseline does not claim
those checks were run.

To reproduce the test environment without changing the system Python:

```sh
baseline_env=$(mktemp -d /tmp/yasmv-baseline.XXXXXX)
python3 -m venv "$baseline_env/venv"
"$baseline_env/venv/bin/python" -m pip install \
  jsonschema==4.26.0 attrs==26.1.0 jsonschema-specifications==2025.9.1 \
  referencing==0.37.0 rpds-py==2026.6.3
PATH="$baseline_env/venv/bin:$PATH" YASMV_HOME="$PWD" make -j3 test
```
