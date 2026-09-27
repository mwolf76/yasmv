# Bounded call frames (M5)

M5 adds direct recursive and mutually recursive calls, per-frame registers and
stack objects, direct LLVM aggregate arguments/results, and bounded dynamic
stack allocation. It builds on the [memory contract](MEMORY_MODEL.md) and uses
the same [C driver](C_WORKFLOW.md), native validation, and trace replay.

```sh
python3 tools/verify-c.py tests/llvm2smv/stack/recursive.c \
  --output /tmp/recursive-model --stack-depth 3 --depth 30
python3 tools/verify-c.py tests/llvm2smv/stack/vla.c \
  --output /tmp/vla-model --memory-bytes 2 --dynamic-stack-bytes 2 \
  --depth 30 --timeout 120
```

Reducing the recursive example's stack depth to 2 produces a replayed resource
result. These safety checks are bounded by model transitions, not unbounded proofs.

## Configuration and representation

Both drivers and the translator accept `--stack-depth` (default 8, range 1–64)
and `--dynamic-stack-bytes` (default 16, range 1–4096). The entry occupies depth
1; verifier hooks and memory intrinsics do not occupy frames. An ordinary call
from the last admitted depth reaches `STACK_BOUND`, including tail calls.
There is no implicit recursion assumption or replacement return value.

The implementation specializes frames by static call path up to the depth
limit. Each specialization has separate SSA registers and stack objects;
arguments are wired from the caller, return PHIs deliver results, and explicit
CFG edges encode return continuations. `stack.depth` records active depth.
A frame specialization can be invoked repeatedly by a loop. Its registers are
assigned by the original SSA control flow on every invocation; globals, including
function statics, remain shared. Returns expire only that frame's stack objects.

This is a finite call-stack representation using specialized control locations,
rather than a reusable array of runtime return addresses. It preserves caller
state across admitted nested calls, but branching recursion can cause exponential
model growth. Expansion is rejected above 10,000 calls or 100,000 instructions;
call-graph inspection also has a depth budget of 256. All blocks in the original
direct-call closure are checked before specialization, including callees beyond
the runtime depth cutoff. Unsupported instructions never disappear at that cutoff.
No branch pruning or LLVM optimization pipeline is used to expand calls.

## Arguments, results, and ABI

Ordinary C-convention direct calls admit integers, data pointers, and recursively
composed LLVM arrays/structures as arguments and results. Simultaneous return
PHIs preserve aggregate fields and poison. Function and call-site `noundef`
boundaries remain explicit checks; integer `signext`/`zeroext` remain admitted.
Entry points still take no arguments and return void or an integer.

This admits ABI coercions already expressed using supported LLVM values; it is
not a complete C aggregate ABI implementation. Special attributes such as
`byval`, `sret`, `inalloca`, and `noalias` fail admission, as do variadic,
exceptional, indirect, and unknown external calls. Support for a source-level
structure therefore depends on its Clang-lowered signature. User-defined
`__llvm2smv_` names are reserved and rejected.

## Stack allocation and restoration

Fixed allocas may occur in any block. Dynamic allocas use a positive integer
count with 1–64 bits, multiplied by the target DataLayout element stride. Each
surviving allocation site in each specialized frame reserves its fixed size, or
`min(dynamic-stack-bytes, memory-bytes)` bytes for dynamic storage. All reserved
storage, including globals, must fit the static `--memory-bytes` budget. Dynamic
objects track their actual extent; bounds checks use that extent, not capacity.

There is **one outstanding allocation per site per specialized frame**. Executing
that site again while its allocation remains outstanding, or requesting more
than its dynamic capacity, reaches `STACK_ALLOCATION_BOUND`. In particular, loop
allocas do not silently overwrite or reclaim earlier live allocations. Raising
stack depth does not increase a site's outstanding-allocation capacity. Programs
requiring multiple simultaneously outstanding allocations at one site need a
future allocation-pool extension; they receive an honest resource result today.

Return and `llvm.stackrestore` release allocation capacity. `llvm.lifetime.end`
ends accessibility but does not release allocation capacity. Every successful
allocation increments a nonwrapping generation; the existing generation bound
still applies even after release. A stale dereference is a runtime error.
Inbounds GEP or comparisons involving an older dynamic-object generation reach
`UNSUPPORTED_MEMORY`, because that generation's former extent is not retained.
A poison allocation count is a runtime error. A zero dynamic count reaches
`UNSUPPORTED_MEMORY`; fixed zero counts are rejected. This release does not
supply zero-sized stack-object semantics.

`llvm.stacksave` snapshots allocation generations in its own frame;
`llvm.stackrestore` expires allocations made since that snapshot, preserving
older objects and all caller objects. After promotion, save tokens must flow
directly to same-frame restore calls. Token PHIs, escaping tokens, ordinary pointer
uses of tokens, and cross-frame restoration are rejected. The intrinsic's
[LLVM 18 contract](https://releases.llvm.org/18.1.8/docs/LangRef.html#llvm-stacksave-intrinsic)
is the semantic baseline. This handles ordinary Clang VLA scopes without treating
opaque stack tokens as observable memory addresses.

## Results and evidence

Safety queries include all five obligations: `safe`, `memory_supported`,
`memory_within_bound`, `stack_within_bound`, and `stack_allocation_within_bound`.
Direct model clients must do the same. Replayed depth or allocation-capacity
failures produce `resource_bound_reached` (exit 3) with failure kinds
`stack_depth_bound` or `stack_allocation_capacity`. Bounds are absorbing failure
locations for progress too. Solver timeouts remain `unknown`; bounded checks
remain scoped to model transition depth.

Source maps record the frame tree, instruction ownership, depth limit, per-object
frame, capacity, and dynamic status. Projected evidence exposes the active call
chain, stack depth, allocation status, generation, and actual extent. Terminal
sinks have no instruction owner; their preceding trace frame identifies the
failure site and active call chain. C local-variable reconstruction and automated
executable counterexample replay remain M7 work.

Artifact scopes are `llvm18-scalar-v3` and `llvm18-memory-v2`, with normalization
`bounded-frames-v1`. Model identity covers bounds and frame metadata. Native trace
replay checks the generated model path, not compiler or translation correctness.
Use tight justified memory capacities for small models: unused capacity expands
byte state and offset circuits, and even small recursive/VLA programs can exceed
solver budgets. Resource limits never count as verification success.
