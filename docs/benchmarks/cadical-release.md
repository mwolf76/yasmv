# CaDiCaL release build validation

Production builds now use `./configure -fPIC` for the pinned CaDiCaL 3.0.1
revision `c60730422e758ef1cebe7aeddf2dda31c996bf04`. Upstream supplies
`-O3 -DNDEBUG`; the previous `-c` build already used `-O3` but kept assertions.
API contract checks remain enabled. The solver's `inprobing=0` policy and seed
are unchanged. The separate assertion-enabled CI job and sanitizer recipe remain.
CI also checks the release archive with the standalone API probe, whose checks
do not depend on C/C++ assertions.

## Build provenance

Local validation on 2026-09-28 uses a fresh dependency checkout/build directory and a clean
LLVM-enabled yasmv rebuild. GCC is 14.2.0, LLVM/Clang is 18.1.8, and Python is
3.13.5. The dependency's generated `build/build.hpp` reports:

```text
-Wall -Wextra -O3 -DNDEBUG -fPIC
```

CaDiCaL archive SHA-256:
`2351c3c3a3569b55836b44612a0fcc16c813059900e91033f17248c0f6d486b4`.

yasmv executable SHA-256:
`fc8daecbadf97ecd29f69035670f135d7c3bf1181ace512ea212c1663522ee5e`.
The link commands for yasmv and its native test executables name the new static
archive explicitly. `--solver-info` still reports the pinned revision and
`inprobing=false`. The LLVM translator binary is unchanged from milestone 6.

yasmv retains the previous benchmark's compiler flags:

```text
-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -DPIC -fPIC -std=c++20 -O2 -Wall -Wno-deprecated-declarations -Werror
```

## Validation

The standalone API gate passed all 10 checks against each of the release,
assertion-enabled, and ASan/UBSan archives. The sanitizer run enabled leak
detection and reused the separately instrumented pinned archive from the
migration validation. All eight API runner tests passed. The release probe
itself was compiled with `-O3 -DNDEBUG`.

The 2,432 arithmetic fragments are unchanged; manifest SHA-256:
`3b9c55919bc04cdfa1e51064a17feb473b95ee362a2e226163d6c28a9728cf1c`.

The clean rebuild, including all four native test executables, passed with C++
warnings treated as errors. The full core/LLVM regression gate passed on its
first run, exit 0, in 854.838 seconds using three make jobs. This includes all
eight native adapter CNF configurations and all LLVM scalar, C, memory, and
stack suites. No tests were skipped and no test assertions or timeouts were
relaxed. The baseline's isolated Python environment includes `jsonschema`
4.26.0 so optional schema checks ran:

```sh
PATH="/tmp/yasmv-cadical-m1.vYtNeq/venv/bin:$PATH" YASMV_HOME="$PWD" make -j3 test
```

This validates the release-linked application. The separate sanitizer run
above covers the native API probe, not a new full-application sanitizer run.

## Matched end-to-end benchmarks

The unchanged benchmark runner collected five fresh-process and five warm-session
samples per model, plus a separately recorded initial session sample. Cases ran
sequentially after the rebuild, before the full test suite, with no competing
build or test workload. Machine/platform, Python/compiler versions, yasmv flags,
model source hashes, query/depth, and complete result identities match the
[assertion-enabled milestone 6 runs](cadical-m6.md). Status, outcome, and
optimality are identical both across these builds and between fresh/warm runs.

| Case | M6 assertions fresh (ms) | Release fresh (ms) | Change | M6 assertions warm (ms) | Release warm (ms) | Change |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Faulty retry protocol | 1525.58 | 1520.81 | -0.31% | 608.85 | 601.72 | -1.17% |
| Deduplicating retry protocol | 1547.30 | 1533.49 | -0.89% | 620.35 | 618.28 | -0.33% |

Entries are medians. The faulty protocol remains reachable at certified shortest
depth 5; the deduplicating protocol remains unreachable through depth 12 (not an
unbounded proof). Results remain broadly similar to the historical
[MiniSat baseline](cadical-m1-minisat.md) as well. These small differences across
five samples do not demonstrate a statistically significant speedup or general
SAT performance. Fresh timings include startup/model loading; warm timings
include session fingerprinting/request overhead.

Raw samples, binary/model hashes, and complete results:
[reachable](cadical-release-reachable.json) and
[bounded-unreachable](cadical-release-unreachable.json).
Historical benchmark files are unchanged.

Reproduce with the [release build](../CADICAL_BACKEND.md) and the yasmv flags
above, leaving unsupported native `CADICAL_*` overrides unset:

```sh
python3 tools/benchmark-sessions.py \
  --model examples/retry-protocol/faulty.smv --target DUPLICATE --depth 12 \
  --runs 5 --output /tmp/cadical-release-reachable.json
python3 tools/benchmark-sessions.py \
  --model examples/retry-protocol/deduplicating.smv --target DUPLICATE --depth 12 \
  --runs 5 --output /tmp/cadical-release-unreachable.json
```
