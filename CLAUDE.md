# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

yasmv (Yet Another Symbolic Model Verifier) is a symbolic model checker that performs reachability analysis and step-by-step simulation. It uses a dialect of the SMV language and is built in C++ with modern development practices.

The project now includes **llvm2smv**, a C-to-SMV translator that enables formal verification of C programs by compiling them to LLVM IR and then translating to SMV models for verification with yasmv.

## Common Development Commands

### Building the Project

```bash
# Recommended: Use the setup script
./setup.sh
make -j $(nproc)

# Manual build
autoreconf -vif
tar xfj microcode.tar.bz2
./configure
make -j $(nproc)

# Build with llvm2smv (requires LLVM and clang)
./configure --enable-llvm2smv
make -j $(nproc)

# Build without llvm2smv
./configure --disable-llvm2smv
make -j $(nproc)
```

### Running Tests

```bash
# Run all tests
make test

# Run specific test types
make short-test        # Quick sanity tests
make unit-test         # Unit tests with Boost.Test
make functional-test   # Full functional tests

# Run a single unit test suite
YASMV_HOME=`pwd` ./yasmv_tests --run_test=tests/expressions

# Run a specific functional test
YASMV_HOME=`pwd` ./yasmv --quiet examples/maze/solvable8x8.smv < examples/maze/commands > out
diff -wB examples/maze/solvable8x8.out out

# Test llvm2smv (if enabled)
make -C llvm2smv test
```

### Code Quality

```bash
# Format and clean code
./tools/cleanup.sh  # Runs clang-format and removes tabs/trailing whitespace
```

## Architecture Overview

### Key Components

1. **Parser** (`src/parser/`) - ANTLR3-based SMV language parser
2. **Model** (`src/model/`) - Model representation with modules, variables, and constraints
3. **Compiler** (`src/compiler/`) - Compiles models to internal representation
4. **Encoding** (`src/enc/`) - Manages encoding schemes (algebraic, monolithic, TCBI/UCBI)
5. **SAT Engine** (`src/sat/`) - MiniSat-based SAT solving with CNF encoding
6. **Algorithms** (`src/algorithms/`) - Core verification algorithms:
   - `check/` - Consistency checking for INITial states, TRANSition relations, and constraints.
   - `reach/` - Forward/backward reachability
   - `sim/` - Simulation
7. **Decision Diagrams** (`src/dd/`) - CUDD 2.5.0 for BDD/ADD manipulation
8. **Commands** (`src/cmd/`) - Interactive shell commands
9. **LLVM2SMV** (`llvm2smv/`) - C-to-SMV translator using LLVM backend:
   - `src/main.cc` - Command-line tool entry point with timestamp headers
   - `src/llvm2smv_pass.cc` - Main LLVM IR to SMV translation pass
   - `src/expr_translator.cc` - LLVM expression to SMV expression translation
   - `src/type_translator.cc` - LLVM type to SMV type mapping
   - `src/smv_writer.cc` - SMV output generation with C++20 features

### Design Patterns

- **Manager Pattern**: Components use singleton managers (ExprMgr, ModelMgr, WitnessMgr)
- **Walker Pattern**: Tree traversal for expressions, models, and DDs
- **Microcode System**: JSON-based microcode fragments for algebraic operations

### Main Entry Point

`src/main.cc` - Initializes the interpreter, loads microcode, and runs the interactive shell.

## Development Notes

- Always set `YASMV_HOME` environment variable to the project root when running tests
- The main project uses modern C++ features (compiler default standard)
- llvm2smv sub-project uses C++20 standard and requires LLVM development libraries
- Debug builds use `-O0` by default for easier debugging
- Microcode must be extracted before building (`tar xfj microcode.tar.bz2`)
- The project supports distcc for distributed compilation

## Current Focus Areas

From TODO file:
- Backward BMC produces reversed witnesses that need straightening
- Name ordering preservation in witnesses
- Support for timed constraints (AT-expressions)
- Support for guarded transitions
- Automated frame condition generation

## Known Issues

- Constant-too-large check fails for corner case (value=1, width=1) - see known-issues.md
