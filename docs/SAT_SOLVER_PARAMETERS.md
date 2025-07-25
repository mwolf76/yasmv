# SAT Solver Configuration Parameters

This document provides detailed documentation for all configurable SAT solver parameters in yasmv, based on the underlying MiniSat SAT solver. These parameters control various aspects of the solver's behavior, performance characteristics, and search strategy.

## Overview

yasmv exposes five key MiniSat parameters through command-line options, allowing fine-grained control over the SAT solver's behavior. The default values have been optimized for maximum performance based on MiniSat best practices and extensive research in SAT solving.

## Parameters

### 1. Random Variable Frequency (`--sat-random-var-freq`)

**Type:** `double`  
**Default:** `0.02` (2% randomization for optimal performance)  
**Range:** `0.0` to `1.0`  
**MiniSat Default:** `0.0` (recent versions)  

#### Purpose
Controls how often the solver chooses variables randomly instead of using its normal decision heuristic. The solver typically uses an activity-based heuristic that prioritizes variables frequently involved in conflicts.

#### Behavior
- **0.0**: Completely deterministic variable selection using activity heuristic
- **0.02**: 2% random variable selection (optimal balance of performance and diversification)
- **1.0**: Completely random variable selection (not recommended)

#### When to Adjust
- **Decrease to 0.0** for completely reproducible results and testing
- **Increase** (0.03-0.05) when solver appears stuck in unproductive search areas
- **Higher values** may help with highly structured problems but typically reduce performance

#### Performance Impact
- **0.02** (default): Optimal performance with controlled diversification to avoid local minima
- Low values (0.0-0.02): Good performance, 0.02 often outperforms 0.0 on complex instances
- High values (>0.1): Significantly degrades performance due to poor variable choices
- Non-zero values introduce beneficial non-determinism for performance

---

### 2. Random Initial Activity (`--sat-random-init-act`)

**Type:** `string` (yes/no)  
**Default:** `yes` (enabled for optimal performance)  
**MiniSat Default:** `false`

#### Purpose
Controls whether variable activities are initialized with small random values instead of starting at zero. Variable activity determines the priority of variables in the decision heuristic.

#### Behavior
- **no**: All variables start with zero activity, purely deterministic
- **yes**: Variables get small random initial activities, breaking initial symmetries

#### When to Adjust
- **Disable** for completely reproducible results and testing
- **Keep enabled** (default) for optimal performance on most problem instances
- **Essential** for breaking symmetries in highly structured problems

#### Performance Impact
- **Enabled** (default): Improved performance by breaking initial symmetries and avoiding poor early decisions
- Generally provides performance benefits with minimal computational overhead
- Particularly effective on structured problems with inherent symmetries
- Introduces beneficial non-determinism for performance

---

### 3. Conflict Clause Minimization Mode (`--sat-ccmin-mode`)

**Type:** `int`  
**Default:** `2` (deep minimization for optimal performance)  
**Range:** `0`, `1`, `2`  
**MiniSat Default:** `2` (deep)

#### Purpose
Controls the level of conflict clause minimization performed when learning clauses from conflicts. Minimization reduces clause size by removing redundant literals.

#### Behavior
- **0 (None)**: No minimization, keeps original conflict clause
- **1 (Basic)**: Removes obviously redundant literals using simple checks
- **2 (Deep)**: Performs thorough minimization using more expensive analysis

#### When to Adjust
- **Use 0** for fastest clause learning but weaker learned clauses
- **Use 1** for balanced performance/clause size trade-off
- **Keep at 2** (default) for optimal long-term performance

#### Performance Impact
- **Mode 0**: Fastest learning, but creates larger/weaker clauses leading to slower overall solving
- **Mode 1**: Good balance between speed and clause quality
- **Mode 2** (default): Slower learning but significantly better long-term performance due to smaller, stronger clauses

#### yasmv Default Rationale
Set to `2` by default for optimal performance. The short-term overhead of deep minimization is more than compensated by the long-term benefits of learning smaller, more effective clauses.

---

### 4. Phase Saving Mode (`--sat-phase-saving`)

**Type:** `int`  
**Default:** `2` (full phase saving for optimal performance)  
**Range:** `0`, `1`, `2`  
**MiniSat Default:** `2` (full)

#### Purpose
Controls how the solver remembers and reuses variable polarities (true/false assignments) from previous search branches. Phase saving can significantly improve performance by leveraging learned preferences.

#### Behavior
- **0 (None)**: Always uses default polarity (typically false), no memory of previous assignments
- **1 (Limited)**: Saves some polarity information with restrictions
- **2 (Full)**: Remembers and reuses all variable polarities from successful branches

#### When to Adjust
- **Use 0** for completely deterministic behavior and simpler debugging
- **Use 1** for partial benefits when some determinism is desired
- **Keep at 2** (default) for maximum performance on most problem instances

#### Performance Impact
- **Mode 0**: Deterministic but potentially much slower on complex problems
- **Mode 1**: Moderate performance improvement with some polarity memory
- **Mode 2** (default): Often dramatic performance gains, especially on satisfiable instances and problems with locality

#### yasmv Default Rationale
Set to `2` by default for optimal performance. Phase saving is one of the most impactful SAT solver optimizations, providing significant speedups on most real-world problems with minimal computational overhead.

---

### 5. Garbage Collection Fraction (`--sat-garbage-frac`)

**Type:** `double`  
**Default:** `0.20` (MiniSat standard for optimal memory/performance balance)  
**Range:** `> 0.0` (typically `0.1` to `1.0`)  
**MiniSat Default:** `0.20`

#### Purpose
Controls when garbage collection is triggered based on the fraction of wasted memory. The solver periodically removes deleted clauses and variables to free memory.

#### Behavior
- **Lower values** (0.1-0.3): More frequent garbage collection, lower memory usage
- **Higher values** (0.5-1.0): Less frequent garbage collection, higher memory usage but potentially better cache locality

#### When to Adjust
- **Keep at 0.20** (default) for optimal balance of memory usage and performance
- **Decrease** (0.15) for memory-constrained environments
- **Increase** (0.3-0.5) for better performance when memory is abundant
- **Very low values** (<0.1) may cause excessive GC overhead

#### Performance Impact
- **0.20** (default): Optimal balance between memory usage and GC overhead for most problems
- **Low values**: Reduced memory usage but more frequent GC interruptions
- **High values**: Higher memory usage but fewer GC interruptions, better for memory-rich environments
- **Optimal for most cases**: 0.15-0.30 range

#### yasmv Default Rationale
Set to `0.20` (MiniSat standard) for optimal memory management. This provides the best balance of memory usage and performance across diverse problem types.

---

## Configuration Recommendations

### Default Configuration (Maximum Performance)
```bash
# These are the optimized defaults - no flags needed!
yasmv model.smv
# Equivalent to: --sat-random-var-freq=0.02 --sat-ccmin-mode=2 --sat-phase-saving=2 \
#                --sat-garbage-frac=0.20 --sat-random-init-act=yes
```

### For Testing and Reproducibility
```bash
yasmv --sat-random-var-freq=0.0 --sat-ccmin-mode=0 --sat-phase-saving=0 \
      --sat-random-init-act=no model.smv
```

### For Memory-Constrained Environments
```bash
yasmv --sat-garbage-frac=0.15 model.smv
```

### For Extremely Large Problems
```bash
yasmv --sat-garbage-frac=0.30 --sat-random-var-freq=0.01 model.smv
```

### For Highly Structured/Symmetric Problems
```bash
yasmv --sat-random-var-freq=0.03 model.smv
```

## References

- [Official MiniSat Repository](https://github.com/niklasso/minisat)
- [MiniSat FAQ](https://www.msoos.org/minisat-faq/)
- Eén, N., & Sörensson, N. (2003). An extensible SAT-solver. International conference on theory and applications of satisfiability testing.

## Notes

- All parameters can be combined freely
- Non-zero `random_var_freq` or enabled `random_init_act` will introduce non-determinism
- Performance impact varies significantly based on problem characteristics
- The yasmv defaults prioritize deterministic behavior for testing over raw performance
- Users should profile their specific use cases to find optimal parameter combinations