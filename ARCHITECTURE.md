# yasmv Architecture Overview

This document provides a comprehensive overview of the yasmv (Yet Another Symbolic Model Verifier) codebase architecture, serving as a roadmap for development work and code navigation.

## Project Structure & Architecture

### High-level Directory Structure

- **`src/`** - Main source code organized into modular components
- **`llvm2smv/`** - C-to-SMV translator subsystem (optional, requires LLVM)
- **`examples/`** - SMV model examples (puzzles, algorithms, verification problems)
- **`microcode/`** - JSON-based algebraic operation microcode fragments  
- **`tools/`** - Build and testing scripts
- **`help/`** - Command documentation in nroff format
- **`doc/`** - Doxygen documentation configuration
- **`m4/`** - Autotools macro definitions for dependency detection

### Key Source Directories under `src/`

- **`parser/`** - ANTLR3-based SMV language parser with grammar definitions
- **`expr/`** - Expression system with preprocessing, printing, and time analysis
- **`model/`** - Model representation, type checking, and analysis
- **`compiler/`** - Compiles SMV models to internal representation
- **`enc/`** - Encoding schemes (algebraic, monolithic, TCBI/UCBI) 
- **`sat/`** - MiniSat integration and CNF encoding
- **`dd/`** - CUDD 2.5.0 for Binary/Algebraic Decision Diagrams
- **`algorithms/`** - Core verification algorithms (reachability, simulation, checking)
- **`cmd/`** - Interactive shell command system
- **`witness/`** - Witness (counterexample) management and evaluation
- **`type/`** - Type system with algebraic, array, and monolithic types
- **`utils/`** - Utilities (pools, variants, clocks, logging)
- **`common/`** - Shared definitions, exceptions, tokens

### Build System

**Autotools-based** with extensive dependency detection:
- **`configure.ac`** - Main autoconf configuration with LLVM optional support
- **`Makefile.am`** - Top-level automake with conditional LLVM2SMV builds
- **Dependencies**: ANTLR3, CUDD, MiniSat, Boost (filesystem, program options, test, threads), libjsoncpp, readline

**Build targets**:
- `yasmv` - Main model checker executable
- `yasmv_tests` - Unit test suite (Boost.Test)
- `short-test`, `unit-test`, `functional-test` - Test suite runners

## Core Components & Modules

### 1. Parser Subsystem (`src/parser/`)
- **ANTLR3-based** SMV language parser
- **Grammar**: `grammars/smv.g` generates lexer/parser in C, wrapped in C++
- **Exception handling** for syntax errors
- Produces expression trees for compilation

### 2. Expression System (`src/expr/`)
- **Core**: `expr.hh` defines expression node types (arithmetic, logical, temporal, etc.)
- **Management**: `expr_mgr.hh` singleton for expression creation and caching
- **Preprocessing**: Simplification and normalization
- **Time analysis**: Support for timed expressions and temporal operators
- **Printing**: Pretty-printing with configurable formatting
- **Walker pattern** for tree traversal operations

### 3. Model Representation (`src/model/`)
- **Model class**: Container for modules with symbol indexing
- **Module class**: Variables, constants, INIT/TRANS/INVAR sections
- **Type checking**: Static analysis of model correctness
- **Analysis**: Symbol dependency analysis and resolution

### 4. Compiler Pipeline (`src/compiler/`)
- **Compilation phases**: Analysis → algebraic/boolean/array compilation → unit generation
- **Unit system**: Compiled expressions with dependency tracking
- **Walker-based**: Traverses expression trees applying compilation rules
- **Encoding-aware**: Generates encoding-specific representations

### 5. Encoding Schemes (`src/enc/`)
- **Algebraic**: BDD/ADD-based symbolic encoding
- **Monolithic**: Bit-vector encoding for SAT solving
- **TCBI/UCBI**: Time-based circuit representations
- **Boolean**: Simple 1-bit variables
- **Array encoding**: Support for array variables

### 6. SAT Solving (`src/sat/`)
- **MiniSat integration**: Embedded SAT solver with custom extensions
- **CNF encoding**: Multiple strategies (no-cut, single-cut)
- **Engine management**: Thread-safe solver instances with statistics
- **Inlining**: Microcode-based operation inlining for efficiency

### 7. Algorithms (`src/algorithms/`)
- **Base class**: Common SAT-based algorithm infrastructure
- **Reachability** (`reach/`): Forward/backward reachability with witness generation
- **Simulation** (`sim/`): Step-by-step execution with witness traces
- **Checking** (`check/`): Consistency checking for INIT/TRANS/INVAR
- **FSM operations**: Diameter computation, state space analysis

### 8. Decision Diagrams (`src/dd/`)
- **CUDD 2.5.0**: Embedded BDD/ADD library
- **Manager**: CUDD manager wrapper with memory management
- **Walker**: Tree traversal for DD operations
- **Integration**: Bridges between expressions and DDs

### 9. Command System (`src/cmd/`)
- **Interpreter**: Interactive shell with readline support
- **Commands**: 20+ commands in `commands/` (reach, simulate, check-init, etc.)
- **Command pattern**: Base command class with consistent interface
- **Help system**: Integrated documentation for each command

### 10. LLVM2SMV (`llvm2smv/`)
- **C++20-based** LLVM IR to SMV translator
- **Type translation**: LLVM types → SMV types
- **Expression translation**: LLVM instructions → SMV expressions  
- **Control flow**: Basic blocks → program counter model
- **SMV writer**: Generates well-formed SMV output with metadata

## Key Design Patterns & Conventions

### 1. Manager Pattern
**Singleton managers** for major subsystems:
- `ExprMgr`: Expression creation and caching
- `ModelMgr`: Model management and resolution
- `WitnessMgr`: Witness generation and management
- `EncodingMgr`: Encoding scheme management
- `OptsMgr`: Command-line option processing

### 2. Walker Pattern
**Tree traversal** with visitor-like semantics:
- `expr::Walker`: Expression tree traversal
- `model::Walker`: Model structure traversal  
- `dd::Walker`: Decision diagram traversal
- Supports pre/post-order visiting with context

### 3. Exception Hierarchies
**Structured error handling**:
- Base `Exception` class with location information
- Component-specific exceptions (ParseException, TypeException, etc.)
- RAII-style resource management

### 4. Memory Management
- **RAII principles** throughout
- **Smart pointers** for object ownership
- **Reference semantics** for manager-controlled objects
- **Pool allocation** for frequent small objects

### 5. Naming Conventions
- **Classes**: PascalCase (e.g., `ExprMgr`, `ModelResolver`)
- **Methods/variables**: camelCase (e.g., `has_witness()`, `f_model`)
- **Constants**: UPPER_CASE (e.g., `MAINGROUP`)
- **Files**: lowercase with underscores (e.g., `expr_mgr.hh`)

## Entry Points & Control Flow

### 1. Main Entry Points
- **`src/main.cc`**: Program initialization, manager setup, command loop
- **`llvm2smv/src/main.cc`**: LLVM IR file processing and SMV generation

### 2. Command Processing Flow
1. **Initialization**: Manager singletons, microcode loading
2. **Model loading**: Parser → AST → Model compilation
3. **Interactive loop**: Command parsing → execution → result display
4. **Algorithm execution**: Encoding → SAT solving → witness generation

### 3. Verification Workflow
1. **Parse**: SMV file → Expression trees
2. **Compile**: Expressions → Compiled units  
3. **Encode**: Units → SAT variables/clauses
4. **Solve**: SAT queries with temporal reasoning
5. **Extract**: Solutions → Witnesses/counterexamples

### 4. Testing Infrastructure
- **Unit tests**: Boost.Test framework testing individual components
- **Functional tests**: End-to-end verification of example models
- **Short tests**: Quick sanity checks for basic functionality
- **Integration tests**: Cross-component interaction testing

## Data Structures & Key Classes

### 1. Core Expression Types
```cpp
class Expr {
    ExprType f_type;        // Operator type (AND, PLUS, etc.)
    ExprVector f_operands;  // Child expressions
    // Immutable, manager-controlled
};
```

### 2. Model Structure
```cpp
class Model {
    Modules f_modules;               // Module definitions
    SymbolIndexMap f_symbol_index;  // Symbol → index mapping
};

class Module {
    ExprVector f_init;    // Initial state constraints
    ExprVector f_trans;   // Transition relation
    ExprVector f_invar;   // Invariant constraints
    Variables f_vars;     // Variable declarations
};
```

### 3. Algorithm Base
```cpp
class Algorithm {
    Model& f_model;          // Target model
    Compiler f_compiler;     // Expression compiler
    Witness* f_witness;      // Generated witness
    // SAT-based verification infrastructure
};
```

## Configuration & Build Options

### 1. Configure Options
- **`--enable-llvm2smv`**: Enable C-to-SMV translator (requires LLVM)
- **`--disable-llvm2smv`**: Build without LLVM dependencies
- **Debug modes**: `-O0` for debug builds, optimizations for release

### 2. Conditional Compilation
- **`ENABLE_LLVM2SMV`**: LLVM2SMV subsystem compilation
- **Platform-specific**: Memory management, signal handling
- **Feature flags**: Experimental features, optimization levels

### 3. Runtime Configuration
- **Word width**: Default integer bit width (32/64)
- **Encoding schemes**: Algebraic vs. monolithic encoding
- **SAT solver options**: Restart strategies, variable ordering
- **Verbosity levels**: Logging granularity control

## Development Workflow

### 1. Testing Strategies
- **Unit tests**: Component isolation with mocked dependencies
- **Property-based**: Automated testing with generated inputs
- **Regression**: Continuous verification of example models
- **Performance**: Benchmark tracking for algorithm efficiency

### 2. Code Quality Tools
- **`tools/cleanup.sh`**: clang-format + whitespace cleanup
- **Static analysis**: Compiler warnings, potential issues
- **Documentation**: Doxygen for API documentation

### 3. Development Guidelines
- **Modular design**: Clear component boundaries
- **Exception safety**: RAII and strong exception guarantees
- **Performance-aware**: Efficient algorithms and data structures
- **Extensibility**: Plugin-like architecture for new algorithms

## Quick Reference

### Finding Functionality
- **Parsing SMV files**: `src/parser/`
- **Expression operations**: `src/expr/expr_mgr.hh`
- **Model manipulation**: `src/model/`
- **Verification algorithms**: `src/algorithms/`
- **SAT solving**: `src/sat/`
- **Command implementation**: `src/cmd/commands/`

### Making Common Changes
- **Add new command**: Create class in `src/cmd/commands/`, register in command manager
- **New expression type**: Extend `src/expr/expr.hh`, update walkers and managers
- **New algorithm**: Inherit from `src/algorithms/algorithm.hh`, implement solve method
- **New encoding**: Extend `src/enc/` with encoding-specific logic

### System Integration Points
- **Manager initialization**: `src/main.cc`
- **Expression compilation**: `src/compiler/`
- **Encoding selection**: `src/enc/`
- **Result presentation**: `src/witness/`

This architecture overview provides a foundation for understanding yasmv's sophisticated model checking capabilities and guides effective development within its modular, extensible design.