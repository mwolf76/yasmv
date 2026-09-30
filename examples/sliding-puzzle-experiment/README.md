# The 63-puzzle: a large unreachable goal

An 8×8 version of the classic unsolvable 15-puzzle. Start with the numbered
tiles in order and the blank at bottom right. The target exchanges 62 and 63
and keeps every other tile, including the blank, in place.

![Initial and target boards](board.svg)

[The generated SMV model](puzzle-63.smv) has 64 six-bit cells (384 board bits),
a four-valued move variable, 2,016 pairwise distinctness constraints, 64 legal
move guards, and 224 directed adjacent-swap commands. Cells are inertial.
Each command moves one nonzero tile into the blank; all other cells retain
their values. There is no idle move, artificial history, dummy state padding,
or supplied parity lemma. All valid board configurations have legal moves.

The reachable board component contains `64! / 2`, approximately
`6.344346609 × 10^88`, configurations. This count excludes the move variable.
The labels fit exactly in six bits; pairwise distinctness therefore says that
the board contains every label 0–63 exactly once.

## Why GOAL is unreachable

Johnson and Story's 1879 *Notes on the “15” Puzzle*, parts I and II, establish
the parity obstruction and the two components for rectangular sliding puzzles.
A modern research account with the original references is Karpman and Roldán,
[*Parity Property of Hexagonal Sliding Puzzles*, introduction, pp. 2–3](https://arxiv.org/pdf/2201.00919).

For this encoding, define the mathematical invariant

```
chi(board) = parity(permutation of all 64 labels, including 0)
             XOR ((blank_row + blank_column) mod 2)
```

Every adjacent slide swaps two labels and changes the blank's checkerboard
color, so both terms flip and chi stays fixed. The initial board has chi=1.
The goal has chi=0: its two numbered tiles were exchanged while its blank
stayed put. Thus no path reaches GOAL. This is our external mathematical
argument; the model contains no expression or constraint for chi.

## Why plain k-induction fails for every k

Let G be the goal board. Let A be G after sliding its blank LEFT; let B be A
after sliding its blank UP. All three are valid boards in the goal's parity
component. There are legal moves

```
A --UP--> B --DOWN--> A --RIGHT--> G
```

Both A and B satisfy `!GOAL`. For any k>=1, alternate A and B for exactly k
states, ending at A, then enter G. Start at A when k is odd and at B when k is
even. Set each state's move variable to the next slide; the final state's move
can be any legal move. This satisfies the induction step's transition relation
and all k preceding copies of `!GOAL`, then violates the property at step k.
It never needs INIT, which is absent from the step obligation.

Consequently the step is SAT for **every finite k**. This is a constructive
all-k argument, not an extrapolation from a few failed solver runs. Adding a
suitable auxiliary invariant, such as chi=1, could make induction succeed;
the claim concerns plain k-induction on `!GOAL`, as currently implemented.

## What was checked

`check.py` uses its own grid-coordinate slide evaluator. On the 2×2 instance
it exhausts all 24 permutations and four move choices: 48 legal successors
match the SMV transition relation exactly, and 48 boundary moves are rejected.
A separate breadth-first search finds 12 reachable boards and excludes GOAL.
It also checks generated 8×8 induction-step paths at k=1,2,3,4,8,16,63,64,127,
and 1024; the argument above covers arbitrary k.

The large model has a satisfiable initial state and a one-slide reachable
control target whose trace passed fresh replay. Native k-induction step
assignments for k=1,2,4 were checked against the independent slide evaluator:
all boards are permutations, all transitions are legal, and only the last
board is GOAL. The 2×2 instance also returned a verified interpolation proof,
with fresh initial-containment, transition-closure, and target-exclusion checks.

## Recorded large-model run

The run used the binary/model hashes in [the summary](results/summary.json),
seed 0, and fresh checker processes. Controls and induction probes had a
30-second cooperative wall budget. Unbounded interpolation had 120 seconds;
the outer process deadline was 140 seconds. Time includes model validation,
compilation, search, and evidence construction. Peak RSS is per-child Linux
`wait4` memory. The separate one-slide replay is outside its search timing.

| Query | Result | Process seconds | Peak MiB |
| --- | --- | ---: | ---: |
| initial | satisfiable | 3.487 | 382.6 |
| one-slide | reachable | 4.047 | 383.4 |
| induction-1 | holds_bounded; step SATISFIABLE | 5.851 | 384.0 |
| induction-2 | holds_bounded; step SATISFIABLE | 7.473 | 383.3 |
| induction-4 | holds_bounded; step SATISFIABLE | 11.767 | 692.2 |
| interpolation | UNKNOWN / deadline | 121.667 | 2286.9 |

**The large run did not prove unreachability.** It returned UNKNOWN at the
cooperative deadline, with no invariant or trace. It reached suffix horizon
3, attempted 9 image queries, made 5 enlargements and 3 restarts,
and recorded 11,229,513 cumulative resolution proof nodes. The peak
reached-circuit arena size was 6,143 nodes; this was not a verified invariant.
The 1,425 native solver calls include model guard checks (the initial-state
control already uses 1,393 calls), so they are not 1,425 image queries.

The independent parity proof establishes the answer. Interpolation currently
proves the small control but does not scale to this large instance within the
recorded budget. The result demonstrates a useful limitation, not an
interpolation success claim.

The large run completed concrete negative checks at depths 0–3. The separate
2×2 control proved unreachability in 9.943 seconds of reported query time,
using 26 image queries and suffix horizon 6. Its invariant passed all three
fresh-solver obligations.

## Reproduce

From a built repository:

```sh
python3 examples/sliding-puzzle-experiment/generate.py --side 8 \
  --output examples/sliding-puzzle-experiment/puzzle-63.smv
python3 examples/sliding-puzzle-experiment/check.py
python3 examples/sliding-puzzle-experiment/run.py --wall-ms 120000
```

The runner writes named request/result JSON files and `results/summary.json`.
The small verified proof is in `results/small-control.json`. A direct native
request for the large experiment is:

```json
{
  "version": 1,
  "model": "examples/sliding-puzzle-experiment/puzzle-63.smv",
  "query": {
    "operation": "reach",
    "strategy": "interpolation",
    "target": "GOAL",
    "limits": {"wall_ms": 120000}
  }
}
```

Run it with `YASMV_HOME="$PWD" ./yasmv --quiet --query-file request.json`.
Exit code 3 with `status: "unknown"` means incomplete search, not a proof.

## Half-size rerun: the 31-puzzle

After the unlimited-time 63-puzzle attempt, the user reported a host crash.
Its last saved sample recorded 55,278,809,088 bytes of current cgroup memory
(51.48 GiB), with no cgroup OOM event at that sample. No final checker result
was saved. The old run's `status: running` is a stale pre-crash snapshot;
it does not mean the process survived the reboot. The old artifacts are kept
in `results-unlimited-60gb`.

The [31-puzzle model](puzzle-31.smv) halves the cell count to a **4×8 board**.
It has 32 five-bit cells (160 board bits), 496 pairwise distinctness constraints,
32 legal-move guards, and 104 directed adjacent slides. INIT is `1..31,0`;
GOAL swaps tiles 30 and 31, leaving the blank fixed. The same parity argument
and the same A/B induction-step construction above apply to this rectangle.
Its reachable board component contains `32! / 2`, about `1.316 × 10^35`, boards.
No parity lemma is supplied to the checker.

Generate it with:

```sh
python3 examples/sliding-puzzle-experiment/generate.py --rows 4 --columns 8 \
  --output examples/sliding-puzzle-experiment/puzzle-31.smv
python3 examples/sliding-puzzle-experiment/check.py
```

The checks also cover all 32 blank positions and all four directions on
representative rectangular boards: 104 legal successors match the independent
oracle and 24 boundary moves are rejected. The rectangle has a satisfiable
initial state and a reachable one-slide control with fresh trace replay.
Generation, opposite parity, and induction-step paths through k=1024 are
checked for both large models; the original exhaustive 2×2 checks and verified
small interpolation proof are retained.

The new interpolation run was launched on 2026-09-30 with seed 0 and no query
limits. Its persistent user service is `yasmv-puzzle31-unlimited-32gb.service`.
`MemoryMax=32000000000` caps cgroup memory at 32 decimal GB (29.80 GiB), and
`MemorySwapMax=0` disables swap. Wall-clock and CPU time limits are both
infinite. The separate `yasmv-puzzle31-monitor.service` records resources every
30 seconds and the eventual exit status. Both services run independently of
the interactive session; they do not restart the experiment after a reboot.

The new artifacts are in `results-puzzle31-unlimited-32gb`: `request.json`
holds the exact query, `run.json` contains hashes, the boot ID and latest status,
`resources.jsonl` contains resource samples, `stdout.json` receives the final
native result, and `stderr.log` receives diagnostics. Check the sample timestamp
and service state when reading a saved status. While it is running there is
no new reachability result; memory exhaustion without a verified result is
an incomplete attempt.

```sh
systemctl --user show yasmv-puzzle31-unlimited-32gb.service \
  -p ActiveState -p SubState -p Result -p MemoryCurrent -p MemoryPeak \
  -p CPUUsageNSec -p ExecMainStatus
```

The 31-puzzle run ended on 2026-09-30 at 12:02:05 CEST after 8,671.336 seconds
(2 hours 24 minutes 31 seconds). Systemd recorded `Result=oom-kill`, signal 9,
and a peak of exactly 32,000,000,000 bytes. The boot ID was unchanged: the host
stayed up while the memory cap terminated the checker. Both native output
files were empty, so this attempt produced no reachability result or proof.

## Halved again: the 15-puzzle

The [15-puzzle model](puzzle-15.smv) halves the cell count again, from 32 to 16,
on a **4×4 board**. It uses 16 four-bit cells (64 board bits), 120 pairwise
distinctness constraints, 16 legal-move guards, and 48 directed adjacent slides.
INIT is `1..15,0`; GOAL exchanges tiles 14 and 15 with the blank unchanged.
Its reachable board component contains `16! / 2 = 10,461,394,944,000` boards.
The same parity obstruction and all-k induction-step construction apply,
and no parity lemma is supplied to interpolation.

```sh
python3 examples/sliding-puzzle-experiment/generate.py --side 4 \
  --output examples/sliding-puzzle-experiment/puzzle-15.smv
python3 examples/sliding-puzzle-experiment/check.py
```

The independent checks now also cover every blank position and direction
on representative 4×4 boards: 48 exact legal successors and 16 rejected
boundary moves. The initial state, a one-slide reachable target, and fresh
trace replay are checked, as are generation, parity, and induction-step paths
through k=1024. Checks for the previous board sizes remain in place.

The new run uses seed 0, the same checker binary, and no query limits. Its user
service is `yasmv-puzzle15-unlimited-32gb.service`, with
`MemoryMax=32000000000`, `MemorySwapMax=0`, and unlimited wall-clock and CPU time.
Artifacts are kept separately in `results-puzzle15-unlimited-32gb` using the
same file layout as the 31-puzzle run. The separate
`yasmv-puzzle15-monitor.service` saves resource samples every 30 seconds and
records the eventual exit status. These services persist independently of the
interactive session, but do not restart the experiment after a reboot.
No interpolation result is claimed until the checker returns verified output.

```sh
systemctl --user show yasmv-puzzle15-unlimited-32gb.service \
  -p ActiveState -p SubState -p Result -p MemoryCurrent -p MemoryPeak \
  -p CPUUsageNSec -p ExecMainStatus
```
