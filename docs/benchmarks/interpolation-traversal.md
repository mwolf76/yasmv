# Interpolation metadata and traversal milestone

The proof node packs byte-sized rule/partition tags next to its signed pivot.
On the measured 64-bit build its record shrinks from 40 to 32 bytes. Graph and
retained-clause indices keep their existing `size_t` width, and solver clause
IDs remain signed 64-bit values. This adds no new index limit or narrowing.

Interpolation now uses byte marks and a direct label array indexed by internal
proof-node ID. Ancestors are marked when queued, so a shared parent is queued
once. The work stack is released before label allocation. Labels are still
constructed in ascending node order, with the same rules and pivots. Variable
ownership is still classified against every original clause, including unused
originals and originals appended after the selected empty-clause root. External
variable IDs and interface atoms retain sparse mappings.

Circuit traversal similarly uses indexed marks and values, with compact
32-bit reachable-node IDs. Sorting reachable IDs preserves the former ascending
visitor and CNF allocation order. Constant edges, complemented edges, and
self-import retain their existing behavior. Scratch arrays are bounded by the
requested root's index, rather than by later unrelated nodes. A sparse ancestor
set below a high root index can use more scratch memory than the old trees;
array sizes track the already-allocated graph prefix, not external IDs.

No proof pruning, changes to interpolation rules, or allocator trimming are
included. Proof and recording engines retain the shorter lifetimes introduced
in the preceding milestone. Both fresh Craig checks remain required.

## Fixed-obligation comparison

Three sequential fresh event replays and one fresh-solve replay used the exact
sealed query-35 artifact from the [lifetime milestone](interpolation-lifetimes.md),
with an 8,000,000,000-byte memory cap, no swap, and a 300-second wall budget.
No builds or tests ran concurrently with benchmark measurements. Sizes below
use decimal MB.

| Measurement | Shorter lifetimes | Compact metadata/traversal |
| --- | ---: | ---: |
| Median event-replay wall time | 25.39 s | 23.23 s |
| Median event-replay peak RSS | 413.06 MB | 369.58 MB |
| Fresh-solve wall time (one run) | 36.59 s | 36.11 s |
| Fresh-solve peak RSS | 605.77 MB | 572.59 MB |
| Proof-node record size | 40 B | 32 B |
| Proof-node vector capacity | 167,772,160 B | 134,217,728 B |
| Proof nodes | 2,416,088 | 2,416,088 |
| Expanded literals | 244,355,151 | 244,355,151 |
| Retained literal payload | 18,929,172 B | 18,929,172 B |
| Interpolant allocated/reachable nodes | 79,900 | 79,900 |

Median event-replay peak RSS fell 10.5%, and median time fell 8.5%. Individual
runtimes were 23.08, 23.23, and 23.53 seconds; peak RSS ranged from 369,426,432
to 369,590,272 bytes. Fresh solving used 5.5% less peak RSS and took 1.3% less
time in its single run. All four replays passed both fresh Craig checks. Every
final proof/circuit counter matches the preceding milestone except for the
intentionally reduced node-vector byte count.

The same 499,107 proof nodes are ancestors of the empty clause. Marks occupy
2,416,088 bytes and labels occupy 9,664,352 bytes, covering the entire prefix
through the root. The pending stack peaks at 1,024 bytes and is destroyed
before labels are allocated. These counts exclude ownership/interface maps,
circuit storage, and allocator overhead. The preceding tree representation
has no equivalent instrumented scratch-byte counter, so these are direct
new measurements rather than an estimated before/after heap comparison.

In event trial 1, peak RSS had already reached 369,426,432 bytes by proof
completion. Current RSS was 350,867,456 bytes after interpolation and
241,762,304 bytes after proof destruction. Eliminating traversal trees lowers
that phase's storage, but overall peak RSS is now set earlier in the run.
The [machine-readable report](interpolation-traversal.json) records artifact
and executable hashes, counters, phase samples, resource limits, and outcomes.
RSS, allocator allocation, and cgroup charged memory remain separate measures.

## Native search companion

The same 35-image limit completed in 197.91 seconds under an 8 GB cap and a
600-second wall budget, with peak RSS of 693,313,536 bytes. The preceding
companion took 185.38 seconds and peaked at 600,600,576 bytes. This run therefore
used more peak memory and time, but also followed a different search path:
horizon 10, 10 restarts, and 25 enlargements, versus horizon 9, 9 restarts, and
26 enlargements. Reported proof nodes were 18,111,569 and reached-set circuit
nodes were 186,342. Those proof statistics cover the verified initial projection and UNSAT
images; they do not account for nodes archived during SAT attempts.

The largest RSS sample was in query 35, which returned SAT. Its proof engine
recorded 1,062,707 originals and 1,834,269 graph nodes at solver return. The
preceding run's query 35 was UNSAT, with 884,567 originals and 1,763,038 graph
nodes. The new capture is explicitly marked `not-verified` and cannot be used
as a verified UNSAT replay fixture. The original sealed query-35 artifact used
for all isolated comparisons remains unchanged.

The native result remains **UNKNOWN**, with `image_limit_reached=true`, no
invariant certificate, and no trace. This does not prove the 15-puzzle target
unreachable. Native counts and capture hashes differ, so these two companions
do not isolate the effect of this storage change. The controlled fixed replay
shows an improvement; the native companion does not demonstrate a whole-search
memory improvement.

## Validation

All 11 standalone proof/circuit groups passed in both the normal build and an
ASan/UBSan build with leak detection. The new regressions cover near-maximum
external clause/variable/atom IDs, shared variables in unused originals after
the root, unreachable circuit prefixes/suffixes, exact visitor and CNF emission
order, complemented edges, and self-import that reallocates the source graph.
Existing exhaustive/random truth-table oracles, independent graph
reconstruction, malformed proof rejection, limits, and cancellation still pass.
The pinned CaDiCaL static library is not instrumented in the sanitizer check.

All nine native interpolation cases and eight capture/replay cases passed,
including the 256-pair projection oracle, fresh Craig validation, capture
corruption rejection, and UNKNOWN without a certificate at the image limit.

The full `PATH="/tmp/yasmv-imc-schema-env/bin:$PATH" YASMV_HOME="$PWD" make -j3 test`
suite passed with LLVM 18 and jsonschema 4.26.0 enabled, with no skips. The
machine-readable report records full-suite and sanitizer log paths and SHA-256
hashes. Both tested executables match the measured benchmark hashes.
