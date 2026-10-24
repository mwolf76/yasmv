# yasmv — Yet Another Symbolic Model Verifier

![master](https://github.com/mwolf76/yasmv/actions/workflows/ci.yml/badge.svg)

yasmv is a finite-state model checker and interactive model-exploration
workbench. It uses an SMV dialect with partial NuSMV compatibility and combines
a C++20 core, CUDD-based expression compilation, and a pinned CaDiCaL SAT backend.

The project began in 2011 as an independent reimplementation inspired by NuSMV
and has since developed its own language and exploration workflow.

## Capabilities

- Bounded reachability and certified shortest witnesses.
- Step-by-step simulation, trace inspection, branching, and independent replay.
- Constraint explanations, bounded safety checks, and verified k-induction.
- Guaranteed-progress checks with dead-end and repeating counterexamples.
- Executable scenario export and replay.
- A native interactive shell, a JSON Lines agent interface, and an optional
  browser/HTTP workbench.
- An optional LLVM 18 frontend for a documented subset of C/LLVM programs.

Bounded results apply only to the checked depth; they are not unbounded proofs.
Resource exhaustion and cancellation produce UNKNOWN rather than a safety
claim. The LLVM frontend rejects unsupported constructs and reports its
coverage limits explicitly.

## Build

The core requires a C++20 compiler, Python 3.10+, Autotools/libtool, ANTLR3 and its
C runtime, Boost, JsonCpp, readline, zlib, and **CaDiCaL 3.0.1**. CUDD 2.5.0 is
vendored. MiniSat is no longer required.

On Ubuntu 24.04, install the core dependencies and bootstrap tools:

```sh
sudo apt-get update
sudo apt-get install build-essential python3 autoconf automake libtool git bzip2 \
  libboost-filesystem-dev libboost-program-options-dev libboost-test-dev \
  libboost-thread-dev libboost-system-dev libboost-chrono-dev \
  libjsoncpp-dev libreadline-dev zlib1g-dev antlr3 libantlr3c-dev
```

ANTLR3 needs Java when generating the parser; the checker itself does not need
a Java runtime.

### SAT dependency

`setup.sh` automatically downloads and builds the pinned CaDiCaL revision
`c60730422e758ef1cebe7aeddf2dda31c996bf04` inside the ignored `.deps/` directory.
No manual solver installation or prefix argument is needed. The first run needs
access to GitHub; subsequent runs reuse the cached release build. Production
flags are `-O3 -DNDEBUG -fPIC`, independent of yasmv's own compiler flags.

Configure verifies the API, version, and full revision and links the archive
statically. For an externally managed solver, use `CADICAL_PREFIX` or
`--with-cadical-prefix` to skip the automatic bootstrap.

### Quick start (recommended)

Use `setup.sh` for the quickest route from a checkout to a running checker.
Install the core dependencies above and LLVM/Clang 18 for the recommended full
build:

```sh
sudo apt-get install llvm-18-dev clang-18
```

From the repository root, no additional setup arguments are required:

```sh
./setup.sh
export YASMV_HOME="$PWD"
./yasmv --version
./yasmv --solver-info
./yasmv
```

`setup.sh` prepares CaDiCaL, extracts the packaged arithmetic microcode when
needed, regenerates the build files, configures, and builds, stopping if any
step fails. Both dependency and project builds use
`make -j "$(nproc)"` when `nproc` is available and succeeds, otherwise plain `make`.
Its defaults match the tested build: LLVM enabled, GCC/G++, C++20, `-O2`,
position-independent code,
strict warnings (`-Wall -Wno-deprecated-declarations -Werror`), and installation
under `/usr/local`.

Explicit configure arguments override the defaults, including
`--with-cadical-prefix`, `--prefix`, and compiler/flag assignments. Setup does
not install system packages, require root access, or run tests; use the
[test commands](#test) below to validate the build.

### Core-only build

If you do not need the LLVM frontend, omit the LLVM packages and disable it:

```sh
./setup.sh --disable-llvm2smv
```

See [the LLVM frontend guide](llvm2smv/README.md) for LLVM 18 toolchain detection,
supported semantics, C verification commands, and limitations.

### Debian packages

Tagged releases ship `.deb` packages for Debian 13 and Ubuntu 24.04: `yasmv`,
its data files in `yasmv-data`, and the optional `llvm2smv` frontend. To build
them from a checkout, install the build dependencies listed in
`debian/control` and run:

```sh
tools/build-deb.sh
```

The script packs `HEAD`, fetches the pinned CaDiCaL release and checks its
checksum, builds the packages into `build-deb/` and runs lintian on them.

## Run

yasmv looks for `microcode/` next to its binary, in the installed data
directory, and in the source tree. Set `YASMV_HOME` to the directory
containing `microcode/` to use another one. If you did not use `setup.sh` and
the directory is absent, extract the bundled data first:

```sh
tar xfj microcode.tar.bz2
export YASMV_HOME="$PWD"
./yasmv
```

The current microcode package contains 2,432 arithmetic fragments. The SAT
migration preserves their contents and packed literal format.

### Explore a model

In the native shell, try the retry-protocol example:

```text
read-model "examples/retry-protocol/faulty.smv"
check reachable DUPLICATE -method bmc -shortest -depth 12
list-traces
dump-trace
```

The shortest witness reaches duplicate execution after five transitions.
Use `help`, `help check`, or `help workspace` for commands and artifact storage.
Shell command options use a single dash; `--` starts an SMV comment.

See the [retry-protocol example](examples/retry-protocol/README.md) for a complete
investigation.

### Agent and browser interfaces

```sh
# Structured requests over stdin/stdout:
./yasmv --agent --store ./investigation

# Machine-readable operation schemas:
./yasmv --capabilities

# Optional browser and HTTP API:
python3 -m tools.workbench serve
```

The agent/workspace services use Python 3.10+ and its standard library.
Only one process may own a workspace store at a time; do not share a live
store between the CLI, agent, and HTTP server.

## Test

Run the full regression gate from the repository root:

```sh
YASMV_HOME="$PWD" make -j3 test
```

This includes core tests and all eight supported CNF-option combinations.
LLVM suites run when the frontend is enabled. Install `jsonschema` in your
test environment to include the optional schema checks.

Useful focused targets include `short-test`, `unit-test`, `functional-test`,
`reliability-test`, `query-test`, and `llvm-test`. The standalone upstream API
gate requires an explicit checkout of the pinned CaDiCaL revision:

```sh
make cadical-api-test CADICAL_SOURCE=/path/to/pinned/cadical
```

Run `make dist` to check the distribution manifests and create a source archive.

CI validates the pinned CaDiCaL API, builds the core, and runs SAT literal and
adapter checks plus CLI/agent smoke tests. Full regression, LLVM, sanitizer,
and browser acceptance remain local gates.

## Documentation

- [Retry-protocol example](examples/retry-protocol/README.md)
- [Guaranteed progress examples](examples/progress/README.md)
- [CaDiCaL migration plan](cadical_integration.md)
- [LLVM frontend](llvm2smv/README.md)

## License and disclaimer

This code is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU Lesser General Public License for details.

yasmv is in no way related to, or endorsed by, the NuSMV development board or
FBK. yasmv does not contain any code from NuSMV's code base.
