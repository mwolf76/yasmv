# Interpolation object-lifetime milestone

Native reachability now releases the A/B recording engines after copying their
clauses and shared interface into the owned `PartitionedCnf`, before starting
the proof solver. Once the interpolant is built, both native interpolation and
replay release the proof graph and proof-producing solver before fresh Craig
verification. Only the circuit, semantic interface, and scalar work counters
survive. The owned CNF remains available for both verification obligations and
is released before importing the image into the reached set.

Both Craig checks remain mandatory. Cancellation, budgets, SAT results, and
failed checks cannot publish a verified interpolant. Proof construction,
interpolation rules, and allocator policy are unchanged; there is no explicit
heap trimming or proof garbage collection in this milestone.

## Fixed-obligation comparison

The comparison uses the exact sealed query-35 artifact from the previous
[clause-storage milestone](interpolation-clause-storage.md). Three sequential
fresh event replays and one fresh-solve replay completed under an 8,000,000,000
byte memory cap, no swap, and a 300-second wall budget. No concurrent builds or
tests ran during the measurements. Sizes below use decimal GB.

| Measurement | Clause storage | Shorter lifetimes |
| --- | ---: | ---: |
| Median event-replay wall time | 22.56 s | 25.39 s |
| Median event-replay peak RSS | 0.578 GB | 0.413 GB |
| Fresh-solve wall time (one run) | 35.96 s | 36.59 s |
| Fresh-solve peak RSS | 0.692 GB | 0.606 GB |
| Proof nodes | 2,416,088 | 2,416,088 |
| Expanded literals | 244,355,151 | 244,355,151 |
| Retained literal payload | 18,929,172 B | 18,929,172 B |
| Interpolant allocated/reachable nodes | 79,900 | 79,900 |

Event replay uses 28.5% less peak RSS, with a 12.5% increase in median runtime.
Individual times were 25.00, 25.70, and 25.39 seconds; peak RSS ranged from
412,037,120 to 413,581,312 bytes. Fresh solving used 12.5% less peak RSS and
took 1.8% longer in its single run. All four runs passed both fresh Craig
checks and preserved every final proof/circuit counter from the preceding
milestone. The [machine-readable report](interpolation-lifetimes.json) records
the exact artifact hashes, executable hashes, phase samples, limits and results.

In event trial 1, process-wide glibc allocated arena plus mmap bytes fell from
434,105,344 at `interpolant_complete` to 85,852,352 after proof destruction.
RSS fell from 413,831,168 to 284,131,328 bytes at those boundaries. The allocator
retained some freed pages; freeing an object does not guarantee returning all
its storage to the OS. Peak RSS now occurs while constructing the interpolant,
before the proof graph can be released. Timings include the additional phase
samples. The additional runtime is concentrated in fresh verification; these
measurements do not establish its cause.

Phase RSS comes from `/proc/self/statm`; peak RSS uses `getrusage`. Small
accounting differences can make a sampled current RSS slightly exceed the
reported high-water value. Cgroup peaks include charged file cache and are
recorded separately. Allocator figures describe the entire process, not an
individual proof object's exact allocation.

## Native search companion

The same 35-image prefix completed in 185.38 seconds under an 8 GB memory cap
and 600-second wall budget. Peak process RSS was 600,600,576 bytes, versus
838,393,856 bytes for the preceding milestone's companion. The result remains
**UNKNOWN**, with `image_limit_reached=true`, no invariant certificate, and no
trace. This benchmark does not prove the 15-puzzle target unreachable.

The native companion reached horizon 9 with 9 restarts and 26 enlargements,
but reported 18,871,025 proof nodes and reached 225,943 circuit nodes, versus
17,947,612 and 119,754 previously. Its CNF/proof capture differs from the
preceding native run. The lower observed RSS and longer runtime therefore
cannot be treated as a controlled comparison of identical proof work. The
sealed replay remains the primary comparison.

For native query 35, allocated arena plus mmap bytes fell from 530,595,648
before proof-engine destruction to 159,181,504 afterward, while the 98,267-node
image circuit survived for Craig verification. This directly measures the
lifetime boundary within one execution, without comparing different proofs.

## Validation

The 256-pair native Boolean projection oracle now computes each interpolant
after both recording engines have been destroyed. Compiled arithmetic, mux,
array, and enum predicates also exercise this ownership boundary and re-emit
the verified result at other frames. All nine native interpolation cases pass,
including cancellation during solving and verification and node-budget failure.
Capture/replay regressions check the destruction phase order in both replay
modes and native search, preserve circuit counts across destruction, and ensure
Craig phases do not report already-destroyed proof allocations. All eight
memory benchmark tests pass, including faulty artifacts, fresh trace validation,
and UNKNOWN without a certificate at the image limit.

Eight ASan/UBSan replay checks passed with leak detection: event and solve
modes for a hand-written delete/restore fixture and three verified captures
from a native lockstep model. These instrument the replay tool, proof checker,
circuit builder and diagnostics; the pinned CaDiCaL static library and native
capture executable are not instrumented in this check.

The full `PATH="/tmp/yasmv-imc-schema-env/bin:$PATH" YASMV_HOME="$PWD" make -j3 test`
suite passed with LLVM 18 and jsonschema 4.26.0 enabled, with no skips. The
machine-readable report includes the retained full-suite and sanitizer log
paths and SHA-256 hashes. Both tested executables match the measured hashes.
