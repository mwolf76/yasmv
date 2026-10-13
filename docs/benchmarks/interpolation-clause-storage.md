# Interpolation clause-storage milestone

The resolution proof now separates graph topology from retained clauses.
Original clauses and named derivation endpoints own normalized literal buffers.
Intermediate resolution nodes retain only their rule, parents, and signed
pivot, plus an absent-clause marker. Checking a hint chain uses two reusable
resolvent buffers; a sorted merge preserves duplicate elimination, pivot
checks, and rejection of complementary literals.

Deleted named clauses remain available for exact restoration checks. Aliased
solver IDs share the endpoint's clause without changing its original partition
or derivation. An intermediate node without a retained clause cannot be passed
off as an empty-clause conclusion. Proof-node limits still count all graph
nodes, including intermediate nodes.

Interpolation still classifies variables against every original clause and
uses the same graph traversal and labelling rules. Solver and recording-engine
lifetimes, fresh Craig verification, reachability search, and allocator policy
are unchanged. No proof garbage collection or `malloc_trim` was introduced.

## Measurement definitions

Three sequential fresh replays of the unchanged artifact all passed both Craig
checks under the same 8,000,000,000-byte cap and 300-second wall budget.

| Measurement | Original baseline | Clause storage |
| --- | ---: | ---: |
| Median event-replay wall time | 47.19 s | 22.56 s |
| Median peak process RSS | 1.561 GB | 0.578 GB |
| Retained literal payload | 977,420,604 B | 18,929,172 B |
| Original literal payload | 14,081,444 B | 14,081,444 B |
| Named derived literal payload | included above | 4,847,728 B |
| Graph-node and clause-object capacity | 234,881,024 B | 218,103,808 B |
| Proof-ID value payload | 30,496,944 B | 30,496,944 B |
| Proof nodes | 2,416,088 | 2,416,088 |
| Expanded literals | 244,355,151 | 244,355,151 |
| Interpolant allocated/reachable nodes | 79,900 | 79,900 |

Runtime fell by about 52%, median peak RSS by 63%, and retained literal payload
by 98%. Individual times were 22.67, 22.28, and 22.56 seconds; peak RSS ranged
from 574,545,920 to 577,859,584 bytes. No concurrent builds or tests ran during
these measurements. The [machine-readable report](interpolation-clause-storage.json)
records artifact and executable hashes, counters, phase samples, and outcomes.

The graph still contains the same resolution steps. The reduction removes
239,622,858 stored intermediate literals; it does not remove proof work or
change interpolation rules. Only 4,732,293 literals remain in retained originals
and named endpoints. Exact restoration data remain available for deleted IDs.

Reusable buffers alone retained the memory benefit but regressed replay time
to about 65 seconds. The final rolling step merges normalized clauses directly
instead of rebuilding a tree at every resolution. The independent set-based
test checker and fresh Craig obligations validate this construction.

Fresh solving of the same captured CNF also passed both Craig checks. This
single run took 35.96 seconds and peaked at 692,043,776 bytes RSS, compared
with 69.91 seconds and 1,673,441,280 bytes in the baseline. It produced the
same proof-node, expanded-literal, and interpolant counts. The solver remained
alive through verification, as in the baseline. The rolling buffers peaked
at 8,192 bytes on this obligation; other temporary allocations are excluded
from that buffer-only counter.

The native companion completed 35 images in 164.56 seconds at 838,393,856 bytes
peak RSS, returning UNKNOWN with `image_limit_reached: true` and no proof or
trace. It reached horizon 9 with 9 restarts and 17,947,612 reported proof nodes.
The original native baseline reached horizon 10 with 10 restarts and 17,268,854
reported proof nodes, and the query-35 artifact hashes differ. This companion
checks completion of a bounded search prefix; its timing and RSS differences
are not a controlled comparison of identical proof work. Neither run proves
the puzzle's target unreachable.

`proof_literal_bytes` counts retained literal capacity. Original and named
derived storage are reported separately. `proof_node_bytes` now excludes clause
objects; `proof_clause_slot_bytes` accounts for those objects in their separate
vector. Compare their sum with the old node-vector measurement when comparing
metadata costs. Map/tree and allocator overhead remain excluded from payload
counts and included in process RSS.

`proof_expanded_literals` counts the literals that the former fully materialized
graph would have retained for the same steps. `proof_temporary_literal_bytes_peak`
measures only the two rolling resolvent buffers, not all temporary allocations.
See the [benchmark guide](../INTERPOLATION_MEMORY_BENCHMARK.md) for the complete
counter definitions and capture/replay commands.

## Correctness checks

The proof tests reconstruct all intermediate clauses independently using sets,
checking every resolution edge, signed pivot, retained endpoint, and weakening.
This reconstruction is confined to tests. The new regression exercises a long
resolution chain, a named endpoint reused by later derivations, aliased IDs,
deletion/restoration, changed restoration contents, and an invalid root.
Existing exhaustive and random truth-table checks, proof corruption tests,
node limits, cancellation, and native safe/reachable controls remain required.

Validation completed with `make -j3 test`, using the jsonschema-enabled Python
environment: the full suite passed with no skips, including all eight memory
benchmark tests and LLVM 18 tests. All nine standalone proof/circuit test groups
also passed AddressSanitizer and UndefinedBehaviorSanitizer with leak detection
enabled. The pinned CaDiCaL static library was not instrumented in that sanitizer
run. Commands, log locations, and log hashes are recorded in the JSON report.

## Reproduction

Use the exact sealed query-35 artifact from the
[original baseline](interpolation-memory-baseline.md). Compare its file hashes;
the query number alone does not identify a fixed workload. Run three fresh
event replays sequentially, then fresh solving and the native 35-image companion,
with the same 8 GB cgroup cap and no concurrent builds/tests. The companion's
completed prefix must remain UNKNOWN unless native reachability actually proves
or refutes the target.
