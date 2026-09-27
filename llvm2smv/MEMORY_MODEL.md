# Bounded addressable memory (M4–M5)

M4 extends the [scalar contract](SCALAR_MODEL.md) and [C workflow](C_WORKFLOW.md)
with fixed-size arrays and structures, addressable globals and stack objects,
integer and pointer loads/stores, GEP, aggregate operations, and memory intrinsics.
It retains the LLVM 18, little-endian Linux x86_64/aarch64 baseline, [bounded call frames](CALL_STACK.md), and mandatory native model validation. This is an explicitly bounded
model with strict memory diagnostics, not a complete ISO C verifier.

```sh
python3 tools/verify-c.py tests/llvm2smv/memory/alias.c \
  --output /tmp/alias-model --depth 30 --timeout 60 \
  --memory-bytes 128 --allocation-generations 4
```

The historical `--emit-scalar-bundle` option also emits memory candidates. Both
`verify-c.py` and `llvm2smv_translate.py` forward the memory options. The source
map records the policy, budgets, object layout, and internal offset width.

## Storage and pointers

LLVM DataLayout determines structure offsets, array strides, allocation size,
and alignment. Every object has a stable identity, size, writability, liveness,
and allocation generation. Each byte carries data and initialized/poison bit
masks. Integer accesses use little-endian bytes; partial writes update aliases.
Integer widths remain 1–64 bits. Typed aggregate operations recursively flatten
arrays/structures; typed loads ignore padding, while byte copies preserve it.
Global initialization supports integers, zero aggregates, arrays, structures,
and data-pointer relocations. Explicit `undef` initializers are rejected.

Pointers carry object identity, signed byte offset, and allocation generation.
They are opaque addresses, not invented machine addresses. Pointer stores attach
ordered provenance fragments to eight bytes. `memcpy`/`memmove` copy those tags;
an integer byte write erases the overwritten tags. Pointer loads reconstruct a
pointer only from matching fragments or an all-zero null representation.
Incomplete fragments produce poison; using that poison as an address fails.
Integer inspection of tagged pointer bytes reaches `UNSUPPORTED_MEMORY`.

GEP follows target strides and signed indices, including inbounds range and
arithmetic-overflow poison. One-past pointers may be formed but not dereferenced.
The internal signed offset width covers the byte budget and is independent of C
integer widths. A defined displacement outside that representation reaches
`UNSUPPORTED_MEMORY`; it is never silently wrapped into a usable object offset.
Non-inbounds arithmetic retains LLVM's 64-bit index wrap before this coverage
check. Out-of-range constant relocations are rejected during translation.

Equality supports same-object/generation pointers and null comparisons with
in-range pointers. Unsigned ordering supports offsets within the same object,
including one-past. Comparisons between different non-null objects/generations
reach `UNSUPPORTED_MEMORY`, because numeric address relationships are unmodeled.
Signed pointer ordering, pointer/integer casts, function pointers, nonzero
address spaces, and pointer/aggregate freeze are rejected.

## Access and lifetime policy

Accesses check non-poison address, live allocation generation, bounds,
writability, and alignment. Alignment must be guaranteed by the object's declared
alignment and offset. The model diagnoses an access claiming stronger alignment;
it does not choose extra incidental alignment for an underaligned object.

Reading uninitialized required bits enters `ERROR`. This is a **strict diagnostic
policy**, stronger than LLVM's general `undef` semantics; a diagnostic is not by
itself a claim of ISO C undefined behavior. Padding starts uninitialized. An i1
store initializes only its low bit. Poison bits propagate through loads and
stores, failing at the admitted uses described in the scalar contract.

Fixed and bounded dynamic allocas in any block are admitted under the
[M5 allocation policy](CALL_STACK.md#stack-allocation-and-restoration). Special ABI allocation flags and GEP `inrange` restrictions are rejected. The inliner preserves their execution and inserts object expiration
at function returns. Reusing an inlined allocation site increments its generation,
so a pointer escaping an earlier call cannot alias the next allocation. Whole
object `llvm.lifetime.start/end` is supported for directly named allocas, with
exact size or -1. An object with a lifetime-start marker begins dead; start
clears its initialized state, and end makes it inaccessible.

The supported nonvolatile intrinsics are `llvm.memcpy`, `llvm.memmove`, and
`llvm.memset`. Copies preserve data, masks, and provenance. `memmove` uses a
snapshot for overlapping ranges. `memcpy` permits equal addresses but diagnoses
other overlap. A zero length ignores the addresses and changes no storage;
poison length fails. Poison memset fill propagates poison into destination bytes.
Volatile/atomic operations, other memory-intrinsic variants, and extra intrinsic
declaration attributes are rejected. Call-site alignment attributes are checked.

## Bounds and result obligations

The byte budget defaults to 128 (maximum 4096), covers all modeled global and
stack storage, and permits at most 255 objects. Oversized or zero-sized storage
and zero-sized typed accesses are rejected before publication. Allocation generations default to 4 per site
(maximum 255). A further allocation enters `MEMORY_BOUND` before wraparound.
Neither limit silently removes an execution.

Safety queries conjoin `safe`, `memory_supported`, `memory_within_bound`,
`stack_within_bound`, and `stack_allocation_within_bound`.
A replayed coverage counterexample yields `unsupported` (exit 2) or
`resource_bound_reached` (exit 3), rather than safety or an assertion violation.
These absorbing states also fail the progress goal. Direct model clients must
check all coverage properties alongside their requested safety property.
Ordinary time/depth/state limits retain their existing result scopes.

Source projections include frame ownership, allocation status, dynamic extent,
object liveness, generation, bytes, initialized masks,
and poison masks. Full pointer fragments remain available in native model traces.
Models preserve declared trace slots while substituting inductively constant
values in generated expressions. Dynamic byte reads combine disjoint address
cases, and statically provable GEP ranges reduce internal arithmetic widths.
These transformations do not prune instructions or UB sites.

Heap allocation, special aggregate ABI attributes, arbitrary pointer
representations, and library models remain later milestones. Recursive calls and
dynamic stack sizes follow the M5 contract. Large models may still exhaust checker resources; such results are
inconclusive. Native replay validates a generated model path, not translation
correctness or source-level equivalence.

Semantics references: [LLVM 18 language reference](https://releases.llvm.org/18.1.8/docs/LangRef.html)
and the target DataLayout captured in each artifact.
