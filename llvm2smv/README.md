# LLVM to SMV frontend

M4 extends the C safety workflow with bounded addressable memory, arrays,
structures, and opaque pointers. See the [memory contract](MEMORY_MODEL.md).
The workflow includes direct-call inlining, verifier
hooks, source locations, and replayed model evidence. Start with the
[C workflow guide](C_WORKFLOW.md). The [scalar contract](SCALAR_MODEL.md)
describes integer operations, control flow, scalar memory, and poison semantics;
the [implementation plan](../docs/LLVM2SMV_IMPLEMENTATION_PLAN.md) tracks general calls and heap support.

The historical incorrect writer remains excluded. The M0 inventory interface
and M1 [typed model foundation](MODEL_FORMAT.md) remain available. Direct raw
SMV output through `-o` is disabled; publication requires native validation.

## Build

Use LLVM **18** development libraries and matching Clang, `opt`, and `llvm-link`
versions, plus the repository's C++20 and Autotools dependencies. On Debian/Ubuntu
the LLVM packages are `llvm-18-dev` and `clang-18`. The rest of the build
requirements are in the [core build guide](../docs/CORRECTNESS_BASELINE.md).

From the repository root:

```sh
autoreconf -vif
./configure --enable-llvm2smv --with-llvm-config=/usr/bin/llvm-config-18
make
make llvm-test
```

`./llvm2smv/build.sh` performs those steps; arguments are passed to configure.
Configure discovers `llvm-config-18` before unversioned `llvm-config`. It selects
Clang, opt, and llvm-link from that installation's binary directory and requires
all three version strings to match `llvm-config --version`. Explicit `CLANG`,
`LLVM_OPT`, and `LLVM_LINK` environment overrides undergo the same checks.
Unknown LLVM majors and mismatched/missing tools fail configuration.

`--disable-llvm2smv` keeps the core independent: configure does not discover or
execute LLVM tools. `make llvm-test` then reports that LLVM testing is disabled.

## Inspect C-generated IR

```sh
CLANG=/usr/lib/llvm-18/bin/clang ./llvm2smv/examples/simple/compile.sh \
  llvm2smv/examples/simple/counter.c /tmp/counter.ll
./llvm2smv/llvm2smv --capabilities
./llvm2smv/llvm2smv --analyze /tmp/counter.ll
```

The compile helper uses `CLANG` (default `clang-18`), checks major version 18,
compiles with `-O0 -g -fno-finite-loops`, and propagates compiler failures. It only generates IR;
these flags do not establish a source-level verification guarantee.

`--analyze` prints a version-1 JSON report to stdout and returns **2** because
the inventory operation does not authorize translation. It accepts textual IR and bitcode,
verifies the module, selects a defined `main` by default, and traverses every
block in its direct call-graph closure, including statically infeasible branches.
Use `--entry=name` to select another defined function. Missing entries never
fall back to an arbitrary function.

The inventory records functions, signatures and attributes, instruction types
and text (including flags), direct call targets, operand-bundle counts, source
locations, globals/initializers, aliases, indirect resolvers, named metadata,
types, opcode counts, target triple, and DataLayout. Unresolved/indirect calls
remain unsupported. Module globals are conservatively inventoried even if not
referenced by the selected entry. An inventory is not a supported-feature claim;
`translation_available` is false and `supported` is null in inventory reports.
Scalar admission runs separately through `--emit-scalar-bundle`; see the scalar
contract for its target baseline. Neither path infers layout from the host.

## Diagnostics and output preservation

```sh
./llvm2smv/llvm2smv /tmp/counter.ll -o /tmp/counter.smv --diagnostics=json
```

A legacy direct-output request emits diagnostics to stderr, leaves stdout empty, and
returns 2. It never opens the SMV destination, so an existing file or symlink is
preserved and a missing file is not created. `--analyze` cannot be combined with
`-o`; its JSON report is not an SMV artifact. The old `--word-width` and `-v`
options are removed rather than suggesting that the old translation still works.

Reports have `version`, `status`, `translation_available`, and `diagnostics`.
Verified-module reports additionally contain `llvm_version`, `entry`,
`target_triple`, `data_layout`, and `inventory`. Each diagnostic has `severity`,
`code`, `message`, and nullable `source`; contextual `function`, `global`, `type`,
`attributes`, and `instruction` fields are included where relevant. Source
locations come from LLVM debug metadata and may be absent. Their columns follow
LLVM debug locations and can be zero when unavailable.

| Exit status | Meaning |
| --- | --- |
| 0 | Capability/help/version output completed; also successful scalar candidate emission (not native validation). |
| 1 | LLVM command-line syntax error (LLVM's text diagnostic). |
| 2 | Invalid input/options or unsupported translation. |

`status: error` indicates input/option/IR verification failure.
`status: unsupported` in inventory mode marks a verified module without scalar admission,
including invalid-entry or missing-layout diagnostics. `--diagnostics=json`
selects a single structured report on stderr for translation failures;
`--analyze` always writes that report on stdout. Neither claims a verification
result or proof.

## Scalar translation

```sh
python3 tools/llvm2smv_translate.py /tmp/counter.ll -o /tmp/counter-model
```

This publishes `model.smv` and four sidecars only after native model validation.
It reports translation success separately from any verification result. All
subsequent queries use the existing yasmv interface on the published model.
The capabilities fields `scalar_candidate_available` and `scalar_features`
describe the admitted features through M4. The older `translation_available: false` and empty
`supported_features` retain their conservative meaning for legacy direct output.

## Tests

`make llvm-test` and `make -C llvm2smv test` run the process contracts and toolchain
checks, typed-model self-tests, writer/publication integration, and scalar semantics tests.
The integration tests require a built yasmv and extracted microcode (see the core
build guide); `make llvm-test` also builds yasmv. Direct subdirectory tests may
use `YASMV=/path/to/yasmv YASMV_HOME=/path/to/installation`.
The full local `make test` includes this gate when LLVM is enabled.
Fixtures cover direct and indirect calls, recursion, infeasible blocks, unknown
features, arithmetic flags, source locations, malformed and invalid SSA, bitcode,
compiler errors, deterministic reports, and preservation of output files.

The counter now has semantic tests: it ends at ten and cannot reach 99 within
the checked bound. Scalar tests also compare small integer domains with an
independent interpreter, exercise PHI swaps, nested loops, and nontermination,
and reject unsupported features before and after promotion. C workflow tests cover compilation and source evidence. Memory tests cover
byte aliases, layouts, provenance, copies, lifetimes, and coverage failures.
