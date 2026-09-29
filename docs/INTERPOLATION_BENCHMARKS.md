# Interpolation benchmark baseline

Run the four-method comparison from a built tree on Linux:

```sh
python3 tools/benchmark-interpolation.py --runs 3 --wall-ms 5000 \
  --hard-timeout 15 --output /tmp/interpolation.json
```

The default manifest is `tests/benchmarks/interpolation/cases.json`. Use repeated
`--case ID` options to select cases. `--binary`, `--home`, and `--translator`
select another build; LLVM cases require the optional translator. The runner
never downloads a dependency. Each sample starts a fresh checker, with seed 0,
and uses the same model bytes, root, effective inputs, assumptions, and safety
target across methods. Method order rotates across repetitions. Run without
competing builds or tests when collecting timings.

| Method | Query | Meaning of depth D |
| --- | --- | --- |
| Bounded | `check-property` | Concrete checks through D; a negative is bounded |
| Simple path | `reach`, `strategy: forward` | No depth cap; exhaustive simple-path termination or a concrete witness |
| K-induction | `prove-property`, `strategy: auto` | Base checks through D and the induction step at D |
| Interpolation | `prove-property`, `strategy: interpolation` | Concrete search cap D, suffix horizons at most D-1; may prove safety earlier |

All methods share the same cooperative wall budget. There is also a common
outer process deadline. UNKNOWN and `holds_bounded` remain distinct from
unbounded proofs; a timeout is never treated as a proof or a completed timing.
Medians include all samples and must be read alongside their outcomes. The
runner checks known safe/unsafe expectations, requires verified interpolation
evidence, compares model/configuration identities, and replays every concrete
counterexample in another checker process. Replay must complete successfully.
An interrupted benchmark report has `complete: false`.

`process_wall_ms` measures process startup through output serialization,
including model loading, encoding, proof processing, internal validation, and
trace decoding. Linux `wait4` reports `peak_rss_kib` for each individual child;
it is not the cumulative maximum across previously run methods. Replay times
and RSS are recorded separately. LLVM translation time is also separate: all
four methods receive the same translated model. These LLVM cases measure the
checker on a generated transition system, not equivalence to source execution.

The report retains each sample, exact query, source/model/binary/runner hashes,
solver identity, build flags, outcomes, checked depths, and query statistics.
`solver_calls` counts native solver invocations, including fresh verification.
Interpolation statistics include horizon, image queries, enlargements, restarts,
and cumulative resolution proof nodes. `circuit_nodes` is the maximum reached
circuit arena size observed during search; `invariant_nodes` counts the live
gates in the final serialized invariant. `invariant_bytes` measures its compact
JSON encoding. None of these node counts substitutes for measured process RSS.

The fixed cases cover safe and faulty retry protocols, a constrained retry
query, safety reachability in progress examples (including a deadlock), safe
and faulty arithmetic recurrences, LLVM assertion models, and three counter
cycles. The counter family has an independent, initially false `bad` latch;
the unsafe region is closed under predecessors while the reachable safe cycle
has 16, 256, or 4096 states. This separates proof abstraction from simple-path
length. Progress examples here are safety targets, not liveness benchmarks.

## Recorded baseline — 2026-09-29

[Raw samples](benchmarks/interpolation-m5.json) record three repetitions of all
12 cases (144 queries), with a 5-second cooperative budget and a 15-second
outer deadline. Measurements ran serially without concurrent project builds or
tests on an Intel Xeon E3-1230 v5, x86-64 Linux, GCC 14.2.0, and the pinned
CaDiCaL 3.0.1 revision. The binary and compiler flags are identified in the report.

All eight safe cases were proved by interpolation and k-induction; all four
unsafe cases yielded counterexamples under every method. All 48 counterexample
replays passed. Simple-path search reached the cooperative deadline on the
256-state cycle, 4096-state cycle, and safe LLVM model in all repetitions. No
outer deadline fired. Bounded negatives remain bounded, even for known safe
fixtures.

Median process seconds below include every repetition. `P` is an unbounded
proof, `V` a concrete violation, `B` a bounded negative, and `U` UNKNOWN at the
wall deadline. A U entry is censored, not a completed proof time.

| Case | Bounded | Simple path | K-induction | Interpolation |
| --- | ---: | ---: | ---: | ---: |
| retry-deduplicating | 1.551 B | 1.552 P | 1.682 P | 2.169 P |
| retry-faulty | 1.531 V | 1.537 V | 1.522 V | 1.954 V |
| retry-constrained | 1.534 B | 1.536 P | 1.631 P | 1.578 P |
| progress-deadlock | 1.511 B | 1.507 P | 1.517 P | 1.522 P |
| progress-completion | 1.511 V | 1.512 V | 1.507 V | 1.522 V |
| long-cycle-4 | 1.527 B | 1.522 P | 1.541 P | 1.522 P |
| long-cycle-8 | 1.523 B | 5.047 U | 1.542 P | 1.521 P |
| long-cycle-12 | 1.522 B | 5.056 U | 1.557 P | 1.526 P |
| arithmetic-safe | 1.527 B | 1.537 P | 1.558 P | 2.035 P |
| arithmetic-unsafe | 1.517 V | 1.520 V | 1.517 V | 1.522 V |
| llvm-safe | 1.557 B | 5.027 U | 1.797 P | 2.294 P |
| llvm-unsafe | 1.546 V | 1.547 V | 1.542 V | 1.949 V |

Interpolation measurements below use maximum observed process RSS and ranges
for work counts across the three repetitions. The fixed solver seed does not
guarantee identical proof construction across fresh processes: retry and LLVM
proof sizes varied. Proof nodes are cumulative; invariant gates count only the
final live graph. A dash means no invariant was published.

| Case | Peak MiB | SAT calls | Images | Restarts | Horizon | Proof nodes | Invariant gates |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| retry-deduplicating | 368.2 | 80 | 14 | 3 | 3 | 126968–128476 | 961–1149 |
| retry-faulty | 368.3 | 62 | 11 | 4 | 4 | 56589 | — |
| retry-constrained | 368.3 | 38 | 2 | 0 | 0 | 9933 | 47 |
| progress-deadlock | 368.2 | 24 | 3 | 0 | 0 | 867 | 14 |
| progress-completion | 368.1 | 18 | 3 | 1 | 1 | 200 | — |
| long-cycle-4 | 366.5 | 17 | 2 | 0 | 0 | 510 | 11 |
| long-cycle-8 | 367.6 | 17 | 2 | 0 | 0 | 928 | 19 |
| long-cycle-12 | 367.5 | 17 | 2 | 0 | 0 | 1346 | 27 |
| arithmetic-safe | 367.7 | 61 | 13 | 0 | 0 | 93053 | 1439 |
| arithmetic-unsafe | 367.3 | 9 | 1 | 0 | 0 | 160 | — |
| llvm-safe | 369.3 | 95–99 | 16–17 | 3 | 3 | 143415–163728 | 705–888 |
| llvm-unsafe | 369.4 | 73 | 12 | 4 | 4 | 55777–73529 | — |

## Optimization decision

Keep interpolation opt-in. It avoids simple-path exhaustion on the larger
cycles and the safe LLVM case, but k-induction already proves these fixtures.
On the larger cycles interpolation uses 17 solver calls versus k-induction's
36; their process times are close. On the safe retry, arithmetic, and LLVM
models, interpolation takes longer and constructs substantially more proof
nodes. Peak RSS across all methods and cases stays between 366.1 and 369.4 MiB;
no case establishes a material peak-memory advantage. Three repetitions of
these small workloads do not justify a default or portfolio change.

No search optimization is selected from this baseline. It identifies image
proof processing and repeated enlargement as candidates for further profiling,
but does not isolate a change with a demonstrated end-to-end benefit. Preserve
fresh proof engines and independent verification. Circuit simplification,
frontier images, or suffix reuse should be separate experiments with this
baseline, the exhaustive small-system oracles, and unchanged evidence checks.
