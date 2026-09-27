# Scalar C safety workflow (M3)

M3 compiles admitted sequential scalar C with matched Clang/LLVM 18, translates
it into a validated finite model, and invokes the existing checker. It adds
acyclic direct calls, verifier hooks, basic C locations, and replayed evidence
to the [scalar execution model](SCALAR_MODEL.md).

## Run a check

Build with LLVM enabled, extract the checker microcode, then run from the source
tree:

```sh
python3 tools/verify-c.py tests/llvm2smv/safety/unsafe.c \
  --output /tmp/unsafe-model --depth 45 --timeout 60 > /tmp/unsafe-result.json
python3 tools/verify-c.py tests/llvm2smv/safety/safe.c \
  --output /tmp/safe-model --depth 45 --timeout 60 > /tmp/safe-result.json
```

The unsafe example admits input 2 and fails its assertion at line 9. The safe
example holds through the requested transition depth. That bounded result is
not an unbounded proof. `--prove` additionally tries the backend's safety
induction; it reports `proven_for_model` only for a verified unbounded result.
`--check termination` uses universal progress toward normal exit or explicit
assumption exclusion. It has a separate `--states` exploration budget.

Accept multiple `.c` translation units, `--entry` for a zero-argument function,
`-I` include directories, and `-D` macro definitions. Arbitrary optimization and
link flags, `compile_commands.json`, C++, system-library models, and installed
SDK packaging are outside this milestone. `--clang`, `--llvm-link`,
`--translator`, and `--checker` select binaries; the corresponding `CLANG`,
`LLVM_LINK`, `LLVM2SMV`, and `YASMV` environment variables are also recognized.
Clang, llvm-link, and the translator's LLVM library must have identical 18.x.y
versions. The admitted target remains little-endian Linux x86_64/aarch64 with
64-bit pointers.

The driver preprocesses each unit using `-std=c11 -O0 -g -fno-finite-loops`,
rejects source pragmas, and compiles the exact expanded snapshot. This snapshot
includes header expansions and line directives and is stored, with its digest,
in bundle provenance. Include paths, defines, runtime header hashes, tool
versions/banners, and frontend policy are also recorded. Link the resulting
bitcode without a general optimization pipeline. Filenames in source mappings
refer to compilation inputs; the captured snapshot is authoritative if a file
subsequently changes.

A new output directory is published only after native model validation. Existing
destinations are preserved. A query timeout can leave a valid published model,
but cannot turn it into a successful verification result. Results and evidence
are emitted as JSON on stdout; redirect that output to retain them. The timeout
applies separately to each tool/query, not to the entire workflow.

## Hooks and assertions

Include `<yasmv.h>` for these declaration-only models:

| Hook | Meaning |
| --- | --- |
| `__VERIFIER_assert(int)` | False enters a persistent assertion-failure location. |
| `__VERIFIER_error(void)` | Always enters an assertion-failure location. |
| `__VERIFIER_assume(int)` | False exits to `ASSUMED_OUT`; poison is a runtime error. |
| `__VERIFIER_nondet_bool/char/uchar/short/ushort/int/uint/long/ulong/longlong/ulonglong(void)` | Fresh, defined value of the declared scalar type on every execution. |

The driver supplies `<assert.h>` as a checked adapter to `__VERIFIER_assert`.
Assertions are enabled: command-line `NDEBUG` and `NDEBUG` active when this header
is included are rejected. Existing IR that calls libc `__assert_fail`, LLVM's
`llvm.assume`, unknown externals, or user-defined replacements for model hooks
is rejected. Harness assumptions are distinct from LLVM optimizer assumptions.
The driver cannot restore an assertion that the supplied source explicitly
removed or replaced through other preprocessing.

Nondeterministic values are sampled at the call and stored in SSA state. Reusing
a result reuses that value; another call, including a later loop iteration,
samples afresh. Values in evidence use the backend's unsigned bit patterns.

## Calls, errors, and progress

Inspect every block in the syntactic direct-call closure before normalization,
including unreachable blocks. Reject recursion, indirect calls, pointer
arguments/results, exceptional calls, bundles, and unhandled attributes. Promote
scalar locals in each function, then inline by copying blocks and wiring incoming
arguments and return PHIs. No constant folding or dead-code pruning is performed
by this inliner: even an unused division by zero remains an error site.
`noundef` arguments/results retain explicit definedness checks across function
and call-site boundaries. Integer `signext`/`zeroext` ABI attributes are supported.
Debug locations retain their inline call chain. Translation rejects expansion
beyond 10,000 calls or 100,000 entry instructions and call-graph depth 256; these
are translation budgets, never assumptions that remove executions.

Export `safe`, `assertion_failed`, per-site `assertion.*`, `runtime_error`,
`terminated`, `assumed_out`, and `progress_goal` definitions in properties.json.
Assertions never become invariants that remove failures. `progress_goal` is
normal exit or `ASSUMED_OUT`; error sinks do not count as normal termination.
False assumptions are explicit excluded executions, not accidental deadlock or
infinite stutter on an admitted path. A separately replayed universal-exclusion
proof can report `no_admitted_execution`. A bounded absence of normal exit cannot
establish vacuity. Safety results leave admission coverage `unknown`.

## Results and evidence

| Status | Interpretation | Exit |
| --- | --- | --- |
| `violation` | A natively replayed safety trace or progress counterexample. | 1 |
| `holds_through_depth` | Safety holds through the requested model-transition depth; unbounded outcome unknown. | 0 |
| `proven_for_model` | Backend proof for this precise model and hook assumptions. | 0 |
| `no_admitted_execution` | Every execution is eventually excluded by an assumption, proven and replayed. | 0 |
| `unknown` | Time, state, proof, or replay analysis was inconclusive. | 3 |
| `error` | Build, admission, artifact, or checker failure. | 2 |

Always inspect `status`; exit zero alone does not mean unbounded safety.

Before returning a safety violation, replay its complete native trace against
the generated model. Check the bundle digest before associating results with
source locations. The result retains native evidence and a basic source
projection: instruction text, C file/line/column, inline chain, global bits and
poison, and sampled nondeterministic inputs. Optimized/promoted local variable
reconstruction is explicitly unavailable. Progress evidence uses the backend's
native proof/counterexample format and `validate-progress` replay.

Model replay validates the generated path, not compiler correctness. The result
explicitly records `translation_certified: false`. The error scope is admitted
LLVM UB uses; this does not detect all ISO C undefined behavior or undo frontend
optimizations. Full executable counterexample replay, addressable memory,
recursive frames, heap bounds, and workbench source views remain later work.
The regression suite independently executes the defined safe/unsafe C examples
with a native harness and compares their behavior with the model witness.

Run `make llvm-test` for frontend, writer, scalar semantics, and C-workflow gates.
