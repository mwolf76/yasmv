# Interpolation memory benchmark

This benchmark measures the current proof representation and its lifetimes.
Enabling instrumentation does not change proof retention, interpolation rules,
or invariant checking.
The small correctness suite is separate from the memory workload.

The [initial measured baseline](benchmarks/interpolation-memory-baseline.md)
records the retained puzzle obligation, three event replays, fresh solving,
and the observed proof-storage and allocator-retention costs.
The [clause-storage milestone](benchmarks/interpolation-clause-storage.md)
documents the first optimization and compares the same captured obligation.

Build and validate:

```sh
make -j4
make interpolation-memory-test
```

The runner requires Linux cgroup v2 and a user systemd manager with memory
controller delegation. It creates a separate transient service for each run,
with an 8,000,000,000-byte memory cap by default, no swap, a finite process
runtime limit, and fresh output files. It never modifies a previous run.
Its runtime limit is the requested wall budget plus ten seconds; captures
also give that wall budget to the native cooperative query timer. An OOM,
timeout, malformed artifact, or failed verification is not successful work.
The service continues if the controlling terminal disappears; its runtime
limit still applies. Interrupting the runner explicitly stops its service.

## Whole-search capture

```sh
python3 tools/benchmark-interpolation-memory.py capture \
  --model examples/sliding-puzzle-experiment/puzzle-15.smv \
  --images 35 --capture 35 --wall-seconds 600 --memory-gb 8 \
  --output .yasmv-benchmarks/interpolation-memory/capture
```

The image count is a fixed-work stop, not a proof bound. Reaching it returns
native UNKNOWN, no invariant and no trace, with
`statistics.interpolation.image_limit_reached: true`. The runner can mark
`work_completed: true` for that completed search prefix while preserving the
native UNKNOWN. A run that proves the property before the limit is also
complete. A partially executed image is not a completed prefix benchmark.

Each call to `compute_interpolant` gets a zero-based query index. Index 0 is
initial-state projection; subsequent indices identify image queries. Use
`--capture 0,20,21` to record only selected queries while retaining telemetry
for the whole run. The default captures all. An index identifies a query in
that run, not a universal formula: solver seeds alone do not fix proof search
or formula construction across processes and builds.

Each selected query writes:

- `input.cnf`: partitioned, native-variable CNF, including the engine's initial
  control unit; originals include proof IDs.
- `interface.json`: authorized shared native variables, canonical atoms, and
  their original state-symbol/bit/frozen coordinates.
- `proof.events`: original, derived, deleted, restored, and UNSAT-conclusion
  callbacks. Derived clauses include their ordered RUP hints and witness.
- `complete`: `verified-unsat` only after interpolation and both fresh Craig
  checks have succeeded. Other outcomes cannot be replayed as verified work.
- `hashes.json`: SHA256 of those four files, sealed by the capture runner.

The runner retains and seals completed queries even if a later image exceeds
a resource budget. The overall run stays incomplete in that case. This lets
calibration failures supply useful, complete smaller obligations.

## Fixed-obligation replay

```sh
python3 tools/benchmark-interpolation-memory.py replay \
  --artifact .yasmv-benchmarks/interpolation-memory/capture/diagnostics/query-000035 \
  --mode events --wall-seconds 600 --memory-gb 8 \
  --output .yasmv-benchmarks/interpolation-memory/replay-events
```

`events` executes the recorded callbacks through the production resolution
proof checker, constructs the interpolant through the production circuit
builder, and checks `A => J` and `J AND B = false` in fresh ordinary CaDiCaL
solvers. It rejects missing conclusions, invalid derivations, mismatched
originals, and incomplete or aliased shared-variable mappings. This isolates
proof storage and interpolation from SAT search variability. Each comparison
must use the same artifact hashes.

`--mode solve` instead runs the pinned proof-producing solver on the same CNF
and then checks the interpolant. It measures SAT search plus proof generation,
but may produce a different proof. Both replay modes release the proof graph
before fresh Craig verification; solve mode also releases its solver, matching
the native interpolation path. The replay tool
excludes model compilation, A/B recording engines and reached-set storage;
compare replay against replay, not its absolute RSS against a whole search.

A replay's scope is **one interpolation obligation**. It does not establish
unreachability of the original target. The whole-search companion is needed
to measure retention between images and across horizon restarts. A full-model
proof still requires the native final invariant obligations.

For direct replay without the cgroup runner:

```sh
YASMV_IMC_DIAGNOSTICS=/tmp/fresh-imc-replay \
  ./interpolation_replay PATH_TO_CAPTURE events
```

The direct executable checks semantics and artifact structure. The Python
runner additionally requires and verifies the sealed file hashes. Neither
interface accepts an unverified capture as completed replay work.

## Measurements and interpretation

`diagnostics/telemetry.jsonl` is flushed at phase boundaries and about once per
second during proof construction and interpolation, checked every 4,096 proof
or labelled nodes. Long individual operations can delay a sample. A killed
run retains prior samples; it need not retain a complete final event record.

Samples include current RSS, process high-water RSS, and, on glibc, allocated
arena bytes, free arena bytes, and mmap allocation bytes. Proof measurements
include stored nodes and node-vector capacity, literal count/capacity,
active clause IDs, archived clause IDs, and separately attributed node,
literal, and ID-value payload bytes. Archived IDs include active IDs.

The clause-storage milestone separates graph nodes from retained clauses.
`proof_literals` and `proof_literal_bytes` now count retained originals and
named derivation endpoints, including deleted clauses that may be restored.
Their separate counts and literal bytes are reported as `proof_original_*`
and `proof_derived_*`. These count unique storage owners: multiple solver IDs
can alias one endpoint without copying its clause. `proof_clause_slot_bytes`
counts the retained-clause vector's capacity in clause objects, separately
from graph capacity and the literal buffers.

`proof_expanded_literals` is a cumulative work counter: the sum of clause
lengths for all appended originals, resolutions, and weakenings. On identical
events it equals the old representation's stored literal count; it is not
current allocation. `proof_temporary_literal_bytes_peak` counts the largest
combined capacity of the old and new rolling resolvent buffers while checking
a chain. It excludes the candidate clause, normalization scratch structures,
and unrelated solver allocations. RSS and allocator measurements include them.

`proof_ancestry` records how many stored nodes are ancestors of the empty
clause, plus original-node and original-literal counts. An unused ancestor
is not necessarily dispensable during earlier proof checking. `proof_sat`,
`proof_unsat`, and `proof_unknown` record the archive at solver return: SAT
attempts can accumulate large proof archives even though no interpolant is
constructed. A SAT callback does not mark a capture verified.

Payload counts are not total heap measurements: map/tree links, allocator
headers, fragmentation and unrelated solver/encoding data are excluded.
`allocator_inuse_bytes` excludes the separately reported mmap bytes. These
are process-wide glibc figures, not attribution to an individual component.
Cgroup peak memory includes charged file cache and is reported separately
from RSS; proof capture can add substantial file cache.

Circuit samples distinguish allocated nodes from nodes reachable from the
reported root. Reachability is measured at stable phase boundaries, not for
an incomplete interpolant. Periodic construction samples report allocation
only. Native `image_cnf_destroyed` and `reached_growth` circuit fields
refer to the reached-set circuit; Craig phases refer to the image interpolant.

Destruction samples deliberately do not call `malloc_trim`: they show what
the current implementation returns to its allocator and what RSS retains.
Native `initial_engines_destroyed` and `image_engines_destroyed` now occur
before `query_begin`: the partitioned CNF owns the clauses and interface, so
its A/B recording engines can be released before proof construction.
`interpolant_complete` records the proof and circuit before destruction.
`proof_engine_destroyed` (native) and `replay_proof_destroyed` (replay) occur
before `craig_verification_begin`, with only the surviving circuit reported.
Craig phases contain no live proof counters. Replay's final proof counters
are snapshots taken at `interpolant_complete`, not retained proof allocations.
`query_temporaries_destroyed` occurs at query exit, after proof and verification
solvers are gone. Native `image_cnf_destroyed` follows release of the owned CNF;
the image and reached circuits remain. These phase semantics supersede the
older baseline reports, whose proof and recording engines survived longer.
Reachability counting itself uses temporary traversal storage; the diagnostic
build is the baseline for subsequent instrumented comparisons.

`run.json` records the command, binary/model or artifact hashes, resource
limits, service outcome, completed-work status and telemetry maxima. Per-query
maxima are local to samples of that query, except `peak_rss_bytes`, which is a
process-wide high-water mark. Counts are not cumulative across queries unless
explicitly reported by the original native statistics.

Use a calibration run to select a **completed** obligation with substantial
proof storage, finishing within minutes under the 8 GB ceiling. The initial
target was 2–4 GB RSS; the selected case reaches about 2 GB in native search
and 1.56 GB in isolated event replay, with almost 1 GB of literal storage.
This already exposes the overhead without needing a larger puzzle. Keep the exact
capture for subsequent comparisons. Run at least three fresh replay processes
without concurrent builds/tests for a timing baseline. Record censored runs;
do not count an OOM as a fast execution. Retain small correct/faulty model
controls and require both Craig checks for every successful sample.

The diagnostic environment variables are opt-in developer instrumentation:
`YASMV_IMC_DIAGNOSTICS`, `YASMV_IMC_CAPTURE`, `YASMV_IMC_IMAGES`. Existing telemetry
files and selected capture directories are rejected to prevent mixing runs.
No variable enables a memory optimization or disables proof checking.

Measured optimization reports: [clause storage](benchmarks/interpolation-clause-storage.md)
and [shorter object lifetimes](benchmarks/interpolation-lifetimes.md).
