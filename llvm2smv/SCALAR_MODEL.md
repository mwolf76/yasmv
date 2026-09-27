# Scalar LLVM execution (M2)

M2 translates an admitted LLVM 18 entry into the typed model introduced in M1.
It is an LLVM execution model with explicit error instrumentation. It is not a
complete C verifier: the C driver, assertion hooks, calls, and source evidence
are later milestones. [LLVM 18 semantics](https://releases.llvm.org/18.1.8/docs/LangRef.html)
govern the admitted bitvectors and poison operations.

## Generate and check a bundle

After building the LLVM-enabled repository and extracting microcode:

```sh
./llvm2smv/examples/simple/compile.sh llvm2smv/examples/simple/counter.c /tmp/counter.ll
python3 tools/llvm2smv_translate.py /tmp/counter.ll -o /tmp/counter-model
```

The destination is a new directory. Existing directories, files, and symlinks
are preserved. The publisher calls `llvm2smv --emit-scalar-bundle`, checks its
manifest, runs native `validate-model`, and atomically publishes the bundle only
on success. Its `translated` result is not a property verification result.
`--translator`, `--checker`, `--entry`, and `--timeout` select tools, entry, and
per-process wall limits. Tool execution and validation failure return nonzero.

`--emit-scalar-bundle` alone writes an **unpublished candidate** JSON container to
stdout. It never writes `-o` or promises native model validity. `--analyze`
continues to expose the conservative M0 inventory, with `inventory_only: true`;
its diagnostics do not perform scalar admission and its per-instruction
`supported` fields are null. The capability field `scalar_candidate_available`
advertises M2 separately from the disabled legacy direct-SMV output path.

Use the existing query interface on the published `model.smv`. Stable properties
are named by the M1 hexadecimal encoding: `p_7465726d696e61746564` is `terminated`,
`p_72756e74696d655f6572726f72` is `runtime_error`, and
`p_72657475726e5f646566696e6564` is `return_defined` for non-void entries.
`source-map.json` decodes variable keys such as `pc`, `return`, `global.counter`,
and `ssa.b2.i1`. Every integer has a Boolean poison companion: `global-poison.<name>` for
globals and `<key>.poison` for SSA registers and the return value. Integer bits are not meaningful while their companion is true.
Source-level trace projection is not part of M2.

For the counter, search for `terminated`, inspect `global.counter` in the trace,
and check the forbidden target `global.counter == 99` through a sufficient
transition bound. A depth-bounded result remains bounded; reaching normal exit
is not a proof that every possible execution terminates.

## Admission and normalization

The entry must be a defined zero-argument, non-variadic C-convention function,
returning void or an integer of 1–64 bits. The baseline requires an explicit
little-endian Linux aarch64/x86_64 triple and DataLayout with 64-bit pointers.
There are no external calls or linker interposition in the modeled environment.
All blocks of the entry are inspected, including unreachable blocks. Calls
other than recognized debug intrinsics are rejected, including calls on dead
branches. Other functions cannot execute; all module globals are checked.

Globals must be initialized scalar integer definitions with ordinary external,
internal, or private linkage. Thread-local, externally initialized, sectioned,
COMDAT, aliased, and indirect-resolver storage is rejected. Loads/stores access
one whole directly named object of the same integer type, with an alignment the
object guarantees. Volatile/atomic access and stores to constants are rejected.
No GEP, pointer arithmetic, byte reinterpretation, aggregate, vector, or floating
point operations are admitted.

The versioned pipeline `checked-scalar-mem2reg-v1` checks instructions, flags,
attributes, and metadata before promoting scalar entry-block allocas with
LLVM's `PromoteMemToReg`. It then verifies and checks the normalized module.
This deliberate normalization applies even with `optnone`; no general optimizer
or CFG simplifier is run. Eligible locals become SSA slots and PHIs.

Unhandled semantic attributes and metadata are rejected, including
`mustprogress`, `willreturn`, range annotations, and loop progress assumptions.
Debug metadata and debug-only loop locations are retained as non-executable
information. Supported entry attributes are `noinline`, `optnone`, `nounwind`,
`uwtable`, return `noundef`, and the enumerated Clang target/frame/code-generation
string attributes in the admission code. Module flags and compiler/debug
identification are recorded through the IR hashes, not applied as link passes.

The compile helper now uses `-O0 -g -fno-finite-loops` with matched Clang 18.
This avoids introducing progress assumptions that would undermine checking an
intentional infinite loop. The model describes the supplied IR; it cannot
restore source checks or behavior erased by prior optimization.

## Execution and definedness

Each non-PHI, non-debug instruction occupies one program location. Branches and
switches select the successor; incoming PHIs update simultaneously on that edge.
Loops remain cycles without an unrolling bound. Every executing location has a
normal successor or an error transition. `DONE` and `ERROR` stutter, preserving
persistent state. Return bits and poison are retained at normal exit.

Integer registers use unsigned bit patterns, including `i1`. Comparisons and
sign extension introduce signed views explicitly. Arithmetic wraps at its LLVM
width. Signed division/remainder use unsigned magnitudes and explicit signs;
arithmetic right shift fills sign bits explicitly. This avoids relying on the
backend's signed remainder or right-shift conventions.

The admitted flags are `nsw`, `nuw`, `exact`, `or disjoint`, and `zext nneg`.
Overflow and invalid shifts produce poison, propagated through ordinary
operations. `select` propagates only its selected value's poison, plus condition
poison. PHIs copy both bits and poison. Scalar memory preserves poison across
stores/loads. `freeze` samples a fresh choice when poisoned and stores a defined,
stable register value for that execution of the instruction.

Immediate UB enters `ERROR`: poisoned branch/switch conditions, zero or poisoned
divisors, signed division/remainder overflow, execution of `unreachable`, and
poison returned from a `noundef` entry. A poisoned signed dividend with divisor
minus one can trigger overflow and also enters `ERROR`. Ordinary poison return
is retained at `DONE` with `return_defined` false. `undef` is rejected, including
when introduced into observable uses by local promotion; it is never replaced
by zero or an incorrectly stabilized choice.

All normal/error guards partition execution. Error instrumentation describes
admitted execution prefixes; it does not model arbitrary behavior after LLVM
undefined behavior. No source-level safety or termination claim is implied by
successful translation.

## Identity and tests

Bundles use scope `llvm18-scalar-v1`. Provenance records the entry, target,
DataLayout, closed environment, normalization/semantic policy, and SHA-256 hashes
of input and normalized serialized IR. The module identifier is excluded;
source/debug filenames, including LLVM's default source filename when absent,
are retained. The M1 manifest
covers this provenance together with the model, properties, and source keys.

`make llvm-test` adds the scalar process suite to M0/M1 gates. Tests cover the C
counter, conditional stores, promoted nested loops, intentional nontermination,
PHI swaps, switch cases, poison selection/memory/freeze, integer boundaries,
admission failures, and publication. A separate Python mathematical interpreter
checks every pair of two-bit operands for integer operations and flags, plus
one-bit cases. Constant-multiply bounds have their own exhaustive checks.
