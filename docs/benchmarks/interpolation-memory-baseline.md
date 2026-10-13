# Interpolation memory baseline — 2026-09-30

The 15-puzzle supplies a completed interpolation obligation that reproduces
substantial proof-storage overhead in under a minute. No memory optimization
is included in this milestone. The puzzle's opposite-parity target remains
unproved by these experiments: replay verifies one image obligation, and the
whole-search companion deliberately stops after a fixed number of images.

## Fixed input and repeated results

The retained artifact is query 35 of the calibration search, locally at
`.yasmv-benchmarks/interpolation-memory/capture-pilot/diagnostics/query-000035`.
It contains 946,869 partitioned original clauses and about 125 MB of files.
The [machine-readable record](interpolation-memory-baseline.json) contains
SHA256 hashes of every artifact file, the model and measured executables,
plus the environment, phase samples, and resource outcomes. Large captures
and raw logs remain in the ignored `.yasmv-benchmarks` directory.

Each row ran in a fresh process, sequentially, without concurrent builds or
tests, under an 8,000,000,000-byte cgroup limit with swap disabled. Replay had
a 300-second wall budget plus the runner's ten-second shutdown allowance.
All sizes below are decimal MB/GB; RSS is distinct from cgroup memory.

| Work | Wall time | Peak process RSS | Fresh Craig checks |
| --- | ---: | ---: | --- |
| Recorded events, run 1 | 47.99 s | 1.561 GB | both UNSAT |
| Recorded events, run 2 | 47.12 s | 1.562 GB | both UNSAT |
| Recorded events, run 3 | 47.19 s | 1.561 GB | both UNSAT |
| Fresh SAT solve on captured CNF | 69.91 s | 1.673 GB | both UNSAT |

Median event-replay time is 47.19 seconds. All three event replays store
2,416,088 proof nodes, 244,355,151 literals, and an interpolant with 79,900
allocated and reachable nodes. Fresh solving happened to produce the same
counts; only event replay guarantees identical proof callbacks as an input.

The initial target was 2–4 GB. Native query 35 reached a process high-water
RSS of 2.052 GB during calibration; isolated replay is smaller because it
omits model compilation, A/B recording engines, and the reached set. Its
nearly 1 GB of literal storage is sufficient to measure improvements without
making the benchmark larger or slower.

## Whole-search companion

The companion completed 35 images in 185.77 seconds, with peak process RSS
of 0.881 GB, under the same 8 GB cap and a 600-second query deadline. Native
status is **UNKNOWN**, `image_limit_reached` is true, and both proof and trace
are null. The runner marks only the requested search prefix complete.

```sh
python3 tools/benchmark-interpolation-memory.py capture \
  --model examples/sliding-puzzle-experiment/puzzle-15.smv \
  --images 35 --capture 35 --wall-seconds 600 --memory-gb 8 \
  --output .yasmv-benchmarks/interpolation-memory/new-prefix35
```

This fresh run's query-35 capture differs from the calibration artifact.
Its smaller peak is not a memory improvement: no optimization was made, and
it did different proof work. The sealed calibration artifact is the primary
comparison workload. Native prefixes remain useful for observing retention
between images, but require their own proof/work counters when comparing runs.

## What the measurements establish

At the end of replay verification:

| Retained structure | Measurement |
| --- | ---: |
| Full clauses in proof nodes | 977,420,604 bytes |
| Proof-node vector capacity | 234,881,024 bytes |
| Proof-ID value payload | 30,496,944 bytes |
| Interpolant node/hash-key payload | 3,056,160 bytes |
| Stored proof nodes | 2,416,088 |
| Nodes in the empty clause's ancestry | 499,107 |
| Original literals | 3,520,361 |

The interpolant is small relative to the proof archive. About 963 MB of
literal payload belongs to derived/intermediate proof nodes, rather than
original clauses. Only 20.7% of stored nodes are ancestors of the final empty
clause. That does not mean the other nodes were unnecessary while checking
earlier callbacks; deletion and restoration semantics still have to hold.

RSS after destruction is not a measure of live proof storage. In event run 1,
after the proof is destroyed, glibc reports 44 MB in allocated arena blocks,
42 MB in mmap allocations, and 1.338 GB in free arena blocks; RSS is still
1.425 GB. In native calibration query 35, after both proof and A/B engines
are destroyed, allocated arena blocks are about 85 MB, mmap allocations
9 MB, and free arena blocks 1.757 GB, while RSS remains 1.856 GB. These samples
show allocator retention as well as substantial live proof storage earlier;
they do not establish a leak. No `malloc_trim` is used.

These results make separating the checked clause store from the interpolation
proof DAG a concrete next optimization candidate. In particular, intermediate
resolution nodes currently retain full clauses. Any change must preserve
checked derivations, deletion/restoration behavior, and both fresh Craig
checks. Compare identical event artifacts first, then repeat the native search
prefix to measure overlapping solver lifetimes and allocator retention.

## Calibration and reproduction

The original 64-image calibration hit its 600-second query deadline during
query 42 and returned UNKNOWN. It is recorded as incomplete. Its earlier
query 35 was complete and verified, so the runner sealed that artifact.
Query 40 reached approximately 3.95 GB RSS but returned SAT: it is not a
verified interpolation replay fixture. This distinction is why the harness
records solver status and requires a completed, verified UNSAT capture.

For the exact baseline, replay the retained artifact with:

```sh
python3 tools/benchmark-interpolation-memory.py replay \
  --artifact .yasmv-benchmarks/interpolation-memory/capture-pilot/diagnostics/query-000035 \
  --mode events --wall-seconds 300 --memory-gb 8 \
  --output .yasmv-benchmarks/interpolation-memory/new-events-run
```

Use a fresh output directory for every run. The runner rejects changed hashes.
See the [benchmark guide](../INTERPOLATION_MEMORY_BENCHMARK.md) for generating
a new capture and for `solve` mode. Regenerating a native query with the same
index does not guarantee identical formulas across processes/builds; preserve
the sealed artifact and compare its hashes when evaluating an optimization.

The correctness suite covers native safe and reachable controls, witness
validation, bounded UNKNOWN with no certificate, both replay modes, proof
corruption, incomplete captures, unauthorized shared variables, hash changes,
and telemetry truncated by termination. It is separate from the large workload.

Validation: `YASMV_HOME="$PWD" make -j3 test` passed, including all eight new
benchmark tests. The two optional schema checks skipped by the system Python
were subsequently run and passed in an isolated environment with jsonschema
4.26.0. The recorded UNKNOWN prefix also validates against the response
schema, which includes the new `image_limit_reached` boolean.
