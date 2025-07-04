# LLVM to SMV Compiler Design

## Overview

This document outlines the design for an LLVM-based compiler that translates C programs into SMV models suitable for verification with yasmv.

## Architecture

```
C Source → Clang Frontend → LLVM IR → LLVM2SMV Backend → SMV Model → yasmv
```

## Key Translation Challenges

### 1. Type System Mapping

**C Types → SMV Types:**
- `int`, `long` → `int<width>` or `uint<width>` (bounded)
- `bool`, `_Bool` → `boolean`
- `char` → `uint8`
- `struct` → Module with fields as variables
- Arrays → SMV arrays with fixed bounds
- Pointers → Abstracted as integers or array indices

### 2. Memory Model

Since SMV is a finite-state language, we need bounded memory:
- Stack variables → SMV variables
- Global variables → SMV variables
- Heap allocation → Pre-allocated array pool
- Pointers → Indices into memory arrays

### 3. Control Flow Translation

**C Control Flow → SMV State Machines:**
- Basic blocks → States in FSM
- Branches → Guarded transitions
- Loops → Bounded unrolling or abstraction
- Function calls → Module instantiation or inlining

### 4. SSA Form to State Variables

LLVM IR uses SSA (Static Single Assignment), while SMV uses state variables:
- SSA values → Temporary SMV variables
- PHI nodes → Case expressions in transitions
- Updates → `next()` expressions

## Translation Strategy

### Phase 1: Basic Translation

1. **Variable Declaration**
   ```c
   int x = 5;
   int y = 10;
   ```
   →
   ```smv
   VAR
       x : int32;
       y : int32;
   INIT
       x = 5 && y = 10;
   ```

2. **Simple Assignments**
   ```c
   x = x + 1;
   y = x * 2;
   ```
   →
   ```smv
   TRANS
       next(x) = x + 1;
   TRANS
       next(y) = x * 2;
   ```

3. **Conditionals**
   ```c
   if (x > 0) {
       y = 1;
   } else {
       y = 0;
   }
   ```
   →
   ```smv
   TRANS
       next(y) = case
           x > 0 : 1;
           else : 0;
       end;
   ```

### Phase 2: Control Flow

1. **Program Counter**
   Each function gets a program counter variable:
   ```smv
   VAR pc : { ENTRY, BB1, BB2, ..., EXIT };
   ```

2. **Basic Block Transitions**
   ```smv
   TRANS
       pc = BB1 && condition ?:
           pc := BB2;
   ```

3. **Loop Bounds**
   ```c
   for (int i = 0; i < N; i++) {
       // body
   }
   ```
   →
   ```smv
   VAR i : uint32;
   TRANS
       pc = LOOP_HEAD && i < N ?:
           pc := LOOP_BODY &&
           next(i) = i + 1;
   ```

### Phase 3: Functions

1. **Function Inlining** (Simple approach)
   - Inline small functions directly
   - Create unique variable names per call site

2. **Module Instantiation** (Complex approach)
   ```c
   int add(int a, int b) {
       return a + b;
   }
   ```
   →
   ```smv
   MODULE add(a : int32, b : int32)
       DEFINE result := a + b;
   ```

## Implementation Plan

### Directory Structure
```
llvm2smv/
├── src/
│   ├── main.cpp              # Entry point
│   ├── LLVM2SMVPass.cpp      # Main LLVM pass
│   ├── TypeTranslator.cpp    # Type translation
│   ├── ExprTranslator.cpp    # Expression translation
│   ├── CFGTranslator.cpp     # Control flow translation
│   └── SMVWriter.cpp         # SMV output generation
├── include/
│   └── llvm2smv/
│       └── *.h
├── examples/
│   └── simple/
│       ├── counter.c
│       └── counter.smv
└── CMakeLists.txt
```

### Core Classes

```cpp
class LLVM2SMVTranslator {
    // Main translator interface
    void translate(Module& M, raw_ostream& OS);
};

class SMVModule {
    // Represents an SMV module
    void addVariable(StringRef name, SMVType type);
    void addInit(SMVExpr expr);
    void addTrans(SMVExpr guard, SMVExpr assignment);
};

class SMVExpr {
    // Represents SMV expressions
    static SMVExpr makeAdd(SMVExpr lhs, SMVExpr rhs);
    static SMVExpr makeNext(SMVExpr var);
    // ...
};
```

## Example Translation

### Input (C):
```c
int counter = 0;
int limit = 10;

void increment() {
    if (counter < limit) {
        counter = counter + 1;
    }
}

int main() {
    while (counter < limit) {
        increment();
    }
    return 0;
}
```

### Output (SMV):
```smv
#word-width 32

MODULE main
    VAR
        counter : int32;
        limit : int32;
        pc : { ENTRY, WHILE_CHECK, WHILE_BODY, INC_CHECK, INC_BODY, EXIT };

    INIT
        counter = 0 && limit = 10 && pc = ENTRY;

    TRANS
        pc = ENTRY ?:
            pc := WHILE_CHECK;

    TRANS
        pc = WHILE_CHECK && counter < limit ?:
            pc := WHILE_BODY;

    TRANS
        pc = WHILE_CHECK && !(counter < limit) ?:
            pc := EXIT;

    TRANS
        pc = WHILE_BODY ?:
            pc := INC_CHECK;

    TRANS
        pc = INC_CHECK && counter < limit ?:
            pc := INC_BODY;

    TRANS
        pc = INC_CHECK && !(counter < limit) ?:
            pc := WHILE_CHECK;

    TRANS
        pc = INC_BODY ?:
            pc := WHILE_CHECK &&
            next(counter) = counter + 1;

    DEFINE
        terminated := pc = EXIT;
```

## Verification Properties

The translator can automatically generate useful properties:
- Assertions → Invariants
- Function preconditions/postconditions
- Bounds checking
- Termination conditions

## Limitations

1. **Bounded State Space**
   - All loops must be bounded
   - Recursion depth must be limited
   - Dynamic allocation must be bounded

2. **Supported C Subset**
   - No dynamic memory allocation (or bounded)
   - No function pointers (or enumerated)
   - No floating point (or abstracted)
   - No I/O operations

3. **Abstraction Required**
   - Large data types need abstraction
   - External functions need models
   - System calls need stubs

## Next Steps

1. Set up LLVM development environment
2. Create minimal LLVM pass skeleton
3. Implement basic type translation
4. Add simple expression translation
5. Handle control flow
6. Test with simple examples
