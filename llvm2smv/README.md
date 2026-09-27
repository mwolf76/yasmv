# LLVM to SMV frontend

The frontend establishes the LLVM toolchain, verified IR inventory, and rejection
boundary
for the [implementation plan](../docs/LLVM2SMV_IMPLEMENTATION_PLAN.md).
**LLVM-to-SMV translation is disabled.** The previous writer produced incorrect
execution models and is no longer linked into the executable. There is no legacy-output
switch. M1 supplies the internal [typed model foundation](MODEL_FORMAT.md);
LLVM instruction lowering begins in M2.

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
compiles with `-O0 -g`, and propagates compiler failures. It only generates IR;
these flags do not establish a source-level verification guarantee.

`--analyze` prints a version-1 JSON report to stdout and returns **2** because
LLVM execution lowering is not implemented. It accepts textual IR and bitcode,
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
`translation_available` and every instruction's `supported` field are false.
The frontend accepts no target ABI for translation and never infers missing
target layout from the host.

## Diagnostics and output preservation

```sh
./llvm2smv/llvm2smv /tmp/counter.ll -o /tmp/counter.smv --diagnostics=json
```

A translation request emits diagnostics to stderr, leaves stdout empty, and
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
| 0 | Capability/help/version output completed; never a translation success yet. |
| 1 | LLVM command-line syntax error (LLVM's text diagnostic). |
| 2 | Invalid input/options or unsupported translation. |

`status: error` indicates input/option/IR verification failure.
`status: unsupported` reports a verified module that cannot be translated,
including invalid-entry or missing-layout diagnostics. `--diagnostics=json`
selects a single structured report on stderr for translation failures;
`--analyze` always writes that report on stdout. Neither claims a verification
result or proof.

## Tests

`make llvm-test` and `make -C llvm2smv test` run the process contracts and toolchain
checks, typed-model self-tests, and native writer/publication integration tests.
The integration tests require a built yasmv and extracted microcode (see the core
build guide); `make llvm-test` also builds yasmv. Direct subdirectory tests may
use `YASMV=/path/to/yasmv YASMV_HOME=/path/to/installation`.
The full local `make test` includes this gate when LLVM is enabled.
Fixtures cover direct and indirect calls, recursion, infeasible blocks, unknown
features, arithmetic flags, source locations, malformed and invalid SSA, bitcode,
compiler errors, deterministic reports, and preservation of output files.

The counter currently tests rejection of the old unsound translation. The
expected counter behavior and forbidden reachability of 99 become semantic
acceptance tests when CFG lowering is implemented in M2. See the implementation
plan for the supported sequential C release and later memory/call milestones.
