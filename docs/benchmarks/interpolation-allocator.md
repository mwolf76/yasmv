# Interpolation allocator-retention milestone

Interpolation now requests release of free glibc allocator pages at completed
proof and image destruction boundaries. `YASMV_IMC_HEAP_RELEASE=auto` is the
default; `off` preserves ordinary destruction without explicit page release.
The policy works independently of diagnostic logging. It does not change proof
storage, interpolation rules, circuit construction, or fresh Craig checks.

`auto` calls `malloc_trim(0)` only when the allocator reports at least 64 MiB
of free arena storage. Native calls follow destruction of the proof solver and
graph, including SAT/UNKNOWN returns, and destruction of the initial/image CNF.
Replay calls follow proof destruction and completion of both Craig checks.
Small obligations avoid allocator scans. Exceptions and cancellation still
free objects normally but need not reach an explicit release boundary.

This is a process-wide, best-effort operation, without changes to allocator
tuning parameters. Non-glibc builds do not attempt it; interposed allocators
may not implement the glibc operations. Free arena storage is not the same as
reclaimable resident memory. `malloc_trim` reports a boolean success, not a
byte count. Paired diagnostic samples record current RSS before and after the
call, as well as its duration. These semantics follow the
[glibc allocation statistics documentation](https://sourceware.org/glibc/manual/latest/html_node/Statistics-of-Malloc.html)
and [Linux malloc_trim documentation](https://man7.org/linux/man-pages/man3/malloc_trim.3.html).

## Fixed-obligation comparison

Measurements use the same sealed query-35 artifact as the
[metadata/traversal milestone](interpolation-traversal.md). Three event replays
per policy ran in alternating off/auto order using the same executable, then
one fresh-solve replay per policy. All runs were sequential, without concurrent
builds or tests, under an 8,000,000,000-byte cgroup cap with no swap and a
300-second wall budget. Sizes below use decimal MB.

| Measurement | Release off | Release auto |
| --- | ---: | ---: |
| Median event-replay wall time | 23.63 s | 23.72 s |
| Median event-replay peak RSS | 369.27 MB | 369.09 MB |
| Median RSS after proof release boundary | 240.93 MB | 142.95 MB |
| Median RSS after verification release boundary | 346.44 MB | 145.12 MB |
| Fresh-solve wall time (one run) | 36.07 s | 36.03 s |
| Fresh-solve peak RSS (one run) | 573.52 MB | 573.23 MB |
| Fresh-solve RSS after proof release boundary | 418.41 MB | 170.55 MB |

Median post-proof RSS fell 40.7%, and post-verification RSS fell 58.1%.
The earlier process peak was effectively unchanged, as expected: page release
cannot lower a high-water mark established before destruction. Median runtime
increased 0.35%, within the observed trial spread. Individual off/auto times
were 23.38/23.68, 23.63/24.13, and 23.77/23.72 seconds. The two release calls
together took about 54 ms per event replay (median); this excludes subsequent
page-fault costs, which are included in total runtime.

These results justify retaining `auto` as the default for this workload:
substantially less resident memory between phases at little measured runtime
cost. They do not establish a universal performance improvement for other
allocators, fragmentation patterns, or workloads.

All eight replays completed both fresh Craig checks. Every final proof and
circuit counter matches the preceding milestone: 2,416,088 proof nodes,
244,355,151 expanded literals, 18,929,172 retained literal payload bytes, and
79,900 allocated/reachable interpolant nodes. The policy reduces resident
memory retained after destruction; it does not reduce the live proof graph.

The [machine-readable report](interpolation-allocator.json) includes artifact
and executable hashes, individual times, phase samples, release-call timings,
resource limits, and outcomes. RSS, allocator allocation, and cgroup charged
memory are separate measurements.

## Native search companion

| Measurement | Release off | Release auto |
| --- | ---: | ---: |
| Wall time | 187.94 s | 167.78 s |
| Peak RSS | 734.08 MB | 556.70 MB |
| RSS at final image release boundary | 542.02 MB | 131.04 MB |
| Reported verified-projection proof nodes | 18,210,530 | 15,770,015 |
| Maximum reported reached circuit nodes | 200,609 | 123,897 |
| Selected query 35 | Verified UNSAT | SAT, not verified |

Both reached horizon 10 with 10 restarts and 25 enlargements, but proof counts,
circuit counts, and the selected capture hashes differ. Consequently their
lower time and peak RSS with `auto` do not isolate the effect of allocator
release. The off run's largest sampled RSS was in a SAT attempt at query 34;
the auto run's was during proof construction in query 35, which also returned
SAT. Native aggregate proof-node statistics cover verified projections, not
archives accumulated by SAT attempts.

The auto run made 57 release attempts across 72 destruction boundaries. All
reported release, totaling 0.604 seconds inside `malloc_trim` (maximum 41 ms
per call). The largest immediate RSS drop was 225.43 MB. At the final image
boundary, release reduced RSS from 179.58 MB to 131.04 MB. These within-run
paired samples directly demonstrate page reclamation, even though overall
native performance remains confounded by different proof work.

Both native runs stop after 35 images and report **UNKNOWN**, with
`image_limit_reached=true`, no invariant certificate, and no trace. Neither
run proves the 15-puzzle target unreachable. Their 600-second wall budget and
8 GB cap are unchanged. The original verified replay artifact remains sealed
and unchanged regardless of the new captures' SAT/UNSAT status.

## Validation

All ten capture/replay regression cases pass. New controls exercise both
policies in both replay modes, reject an invalid policy without diagnostics,
check release ordering after destruction and before verification, and preserve
native reachable/unreachable outcomes and UNKNOWN without a certificate at
the image limit. SAT proof archives are released without being marked verified.
Existing corruption, interface, hash-sealing, and trace-validation tests pass.

ASan/UBSan with leak detection passed eight replay checks: a hand-written
fixture and three native lockstep captures, each in events and solve mode.
The pinned CaDiCaL static library is not instrumented. ASan interposes memory
allocation, so actual glibc page release is established by the paired benchmark
measurements above, not by the sanitizer run alone.

The complete `PATH="/tmp/yasmv-imc-schema-env/bin:$PATH" YASMV_HOME="$PWD" make -j3 test`
suite passed with LLVM 18 and jsonschema 4.26.0 enabled, with no skips. This
includes the standalone proof/circuit groups, native interpolation/search
cases, all capture/replay controls, and the query, model, and translation suites.
The machine-readable report records the full-suite and sanitizer log paths
and SHA-256 hashes. Both tested executables match the measured benchmark hashes.

The remaining structural bottleneck is proof construction before destruction.
In particular, SAT image attempts can build large proof archives without
producing an interpolant. Deferring graph expansion or retaining a clausal
proof until UNSAT is the next separate milestone; allocator release cannot
remove that peak live storage.
