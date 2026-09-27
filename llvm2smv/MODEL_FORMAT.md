# Typed model foundation (M1)

This internal C++ API constructs finite transition systems independently of
LLVM. It does not establish C equivalence or enable the `llvm2smv` translation
CLI. See [transition_system.hh](include/llvm2smv/transition_system.hh) and
[model_writer.hh](include/llvm2smv/model_writer.hh). The historical string-based
translator is still excluded from the build.

## Types and expressions

`Type` represents Boolean values, signed/unsigned words of 1–64 bits, finite
enums, and nonempty flat arrays of Boolean or word elements. Boolean and
one-bit words are distinct. `Expr` is immutable and validates operand types at
construction. Binary operations require identical widths and signedness;
conversions use explicit casts. `APInt` constants must have exactly the declared
width. Hexadecimal bit patterns with explicit casts preserve all 64 bits,
including unsigned maximum and signed minimum values. Word extension follows
the source signedness; truncation keeps low bits. LLVM's signless integer rules,
poison, overflow flags, and operation-specific undefined behavior belong to
later lowering, not to this API.

Expressions cover Boolean/word operators, comparisons, casts, conditionals,
array literals, and constant array indices. No raw SMV expression injection is
accepted. Dynamic indexing and memory operations await the memory milestone.
Enum literals must refer to a domain declared by a model variable. All symbol
references, including assignment targets, must belong to the model.

Keys are stable identities supplied by the caller. Generated names encode every
byte of the key as hexadecimal, with disjoint variable, property, and enum
prefixes. This handles reserved words, punctuation, invalid UTF-8 source names,
and collisions without allocation-order-dependent suffixes. Source maps retain
these keys as `key_hex`; source locations and LLVM identities will be added by
the LLVM lowering layer.

## State and steps

Every variable declaration explicitly supplies either an initializer or
`std::nullopt` for unconstrained initialization. There are three modes:

* `State`: assigned only by guarded, simultaneous steps. Written variables use
  `#inertial`; unwritten variables use `#frozen`, because yasmv does not synthesize
  frame conditions for inertial variables with no writers.
* `Frozen`: immutable across transitions, with optional initial constraints.
* `Choice`: a fresh unconstrained value at each state, emitted as an ordinary
  variable without an initializer or assignments. This is not yasmv `#input`.

A step contains a Boolean guard and at least one assignment. Duplicate targets,
foreign symbols, type mismatches, and writes to frozen/choice variables fail.
Every assignment reads the current state, including within a simultaneous bundle.
When no guard fires, persistent state stutters. Choice values remain fresh.
Guards writing a common variable must be disjoint in the native backend's check;
reachability assumptions do not excuse overlapping guards.

Invariants constrain the model. Properties are Boolean `DEFINE` expressions and
sidecar entries, never assumptions or `INVAR` constraints. Checking or proving
these properties remains the caller's responsibility.

## Bundle and publication

`artifact(model, provenance)` returns a version-1 JSON container with five UTF-8
files under `files`: `model.smv`, `source-map.json`, `properties.json`,
`provenance.json`, and `manifest.json`. Maps and assignments are sorted by stable
key. Provenance includes the LLVM library version, `scope: typed-model-only`,
and caller-supplied UTF-8 origin fields. No current time or output path is added.

The manifest records SHA-256 digests of the four payload files. Its artifact ID
is SHA-256 of this UTF-8/ASCII sequence (filenames sorted lexicographically):

```
llvm2smv-model-v1\n
<filename>\n<lowercase hex digest>\n
...
```

The displayed `\n` denotes one LF byte, with no extra blank lines. The manifest
does not hash itself. This identity covers model text, properties, source map,
and provenance; it provides content identity, not a verification proof.

[`tools/llvm2smv_artifact.py`](../tools/llvm2smv_artifact.py) implements the
internal `publish(artifact, destination, checker, timeout=30)` API. It verifies
bundle digests, writes a temporary sibling directory, and invokes the supplied
yasmv through `validate-model`. Publication requires exit status zero and a
version-1 `completed`/`valid` result. Errors, UNKNOWN, malformed responses, and
timeouts fail without publishing a model. Timeout handling kills and reaps the
checker process group.

Publication uses Linux `renameat2(RENAME_NOREPLACE)` to expose the complete bundle
atomically. Existing files, directories, and symlinks are never replaced, even
when another publisher wins a race. The destination's parent must exist. There
is no non-atomic fallback or power-loss durability guarantee. The caller supplies
the checker installation and `YASMV_HOME`; publication does not certify that
checker's identity or C semantics. No public C compilation driver is added in M1.

## Validation

`make llvm-test` runs the frontend rejection contracts, C++ typed-model
self-tests, and Python integration tests against native yasmv. Fixtures check
sequential and simultaneous updates, exact integer boundaries and casts,
arrays, initialization/framing, fresh choices, properties, hostile identifiers,
deterministic identity, and atomic publication failures. LLVM-generated C
execution fixtures begin in M2.
