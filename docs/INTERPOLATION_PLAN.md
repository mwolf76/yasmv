# Interpolation-based reachability proposal

Status: milestones 1–2 implemented, 2026-09-29; milestones 3–5 are proposed.
See [proof validation](INTERPOLATION_PROOF_VALIDATION.md). Interpolation is an
internal SAT capability; search and query integration follow in milestones 3–4.

Reference: K. L. McMillan, [Interpolation and SAT-based Model Checking](https://mcmil.net/pubs/CAV03.pdf), CAV 2003, LNCS 2725, pp. 1–13, DOI [10.1007/978-3-540-45069-6_1](https://doi.org/10.1007/978-3-540-45069-6_1).

## Motivation and scope

Add an opt-in interpolation engine for unbounded reachability and state safety.
Keep bounded reachability and shortest-witness search as the concrete trace
engine. Initially retain the current defaults and k-induction implementation.

McMillan uses an UNSAT proof of a partitioned bounded path formula to derive
a state predicate J satisfying A => J and J AND B = false, using only shared
variables. Splitting after the first transition makes J an overapproximation
of a forward image. Repeated images enlarge a reachable-state approximation
until it closes; a spurious path causes a restart with a larger suffix bound.
The paper's basic termination argument uses reverse depth. Its full-unrolling
encoding assumes total transitions; checking only the last frame also has a
termination caveat. See Sections 2–3, Figure 3, and the footnote on page 5.

The benefit to investigate here is earlier unreachability proofs on systems
whose simple paths are long. Performance relative to our current algorithms
is an experimental question.

## Current integration points

| Component | Current behavior | Proposed use |
| --- | --- | --- |
| `src/query/query.cc::bounded_reach` | Increasing-depth concrete search; shortest evidence | Preserve and reuse for counterexamples |
| `src/algorithms/reach/forward.cc`, `backward.cc` | Simple-path constraints establish completeness | Add interpolation as a separate strategy |
| `src/algorithms/reach/reach.cc` | Legacy portfolio; query-context dispatch selects one direction | Explicit dispatch first; portfolio integration later |
| `src/query/property.cc` | Bounded safety checks and k-induction; fresh proof rechecks | Share invariant verification and add explicit method selection |
| `src/algorithms/base.hh` | Compiled INIT/INVAR/TRANS and assertion helpers | Reuse model compilation and constrain every relevant frame |
| `src/sat/engine.hh`, `engine.cc` | Opaque pinned CaDiCaL backend, groups, budgets, model mapping | Add optional proof capability and clause provenance |
| `src/sat/cnf.cc`, `inlining.cc` | DD and arithmetic CNF emission | Separate partition-local auxiliary namespaces |
| `src/enc/tcbi.hh` | Timed bit identity; frozen variables have absolute time zero | Map interpolant leaves back to canonical state bits |

`failed_groups()` exposes an assumption core, not a resolution proof. It cannot
provide the interpolant. Existing simple-path clauses must not enter the image
query: they constrain history across the intended state cut.

## Semantics for yasmv

Let C be the legal-state predicate: model INVAR, domain restrictions, and query
state assumptions. Work with I* = INIT AND C, T* = C AND TRANS AND C', and
F* = C AND target. A safety query uses target = NOT property. The conclusion
applies to this restricted system and retains its exact model identity and
assumptions.

Unlike the paper's total-transition encoding, use the following proposed suffix
formula so a short path ending in a deadlock remains visible:

```text
B_0(s)         = F*(s)
B_(h+1)(s,...) = F*(s) OR (T*(s,s') AND B_h(s',...))
A(s0,s1)       = R(s0) AND T*(s0,s1)
```

Every suffix frame is fresh, apart from intentionally shared frozen bits.
Only the selected path prefix needs transitions. In particular, do not encode
all h transitions unconditionally and then OR the targets: that can suppress
a real violation ending before h at a deadlock. A linear-size circuit with
Tseitin encoding can represent the nested suffix. This is our adaptation;
validate it against explicit finite graphs before integration.

Proposed control flow:

1. Check I* AND F* for a depth-zero witness. Handle empty I* explicitly.
2. Set suffix horizon h = 0 and R = I*.
3. Solve A AND B_h in a fresh proof-enabled solver.
4. On UNSAT, extract J(s1), check its allowed support, and rename its state
   bits to an untimed predicate J(s). Test J AND NOT R with ordinary SAT.
5. If that test is UNSAT, independently verify R and publish unreachability.
   Otherwise set R := R OR J and repeat at the same horizon.
6. SAT on the first iteration starts from I* and denotes a concrete path of
   length 1 through h+1. Recover a trace using concrete bounded search.
   SAT after enlarging R may be spurious: increase h and restart R from I*.
   The first implementation increments h by one.
7. UNKNOWN, cancellation, or resource exhaustion produces no proof claim.

Track whether this is the first iteration explicitly; do not compare formula
pointers to decide whether a SAT path starts from INIT. Checkpoint all proof
processing, circuit construction, re-encoding, and verification work. Internal
suffix horizons and image iterations are separate from concrete checked depths.

For partial transitions, B_h denotes exactly the states with a path to F* of
length at most h. Thus UNSAT ensures each added image avoids F*, including
deadlocked bad states. At a fixed point, Post(R) is included in J and J in R.
For a finite system, once h covers all finite shortest distances to F*, an
UNSAT first iteration cannot be followed by a spurious SAT iteration; each
nonterminal image adds states. This supplies the termination argument for the
adaptation, subject to complete SAT calls and no resource limits.

## Proof production and interpolation

The inspected dependency is CaDiCaL 3.0.1, revision
`c60730422e758ef1cebe7aeddf2dda31c996bf04`. Its `src/cadical.hpp` exposes
`connect_proof_tracer(tracer, antecedents, finalize_clauses)` and `conclude()`.
`src/tracer.hpp` supplies original/derived clause IDs, antecedent chains,
deletions/restorations, and conclusion events. Requesting antecedents invokes
`force_lrat()` in `src/proof.cpp`. These are promising interfaces, not evidence
that our required interpolation pipeline already works.

Milestone 1 installs the matching `tracer.hpp` alongside `cadical.hpp` and
extends configure, distribution, and dependency validation. Keep native solver
types behind the existing backend boundary when integrating production proofs.

Start with a standalone proof feasibility probe against the pinned build:

- Attach the tracer while the solver is still CONFIGURING, before Engine's
  first variable allocation. This calls for a constructor/configuration mode.
- Record original clause IDs with A/B provenance and reconstruct resolution
  derivations from checked RUP antecedents. Antecedent lists are not themselves
  explicit pivot sequences. Handle weakening/subclauses correctly.
- Exercise units, an original empty clause, root propagation, search-derived
  clauses, duplicate originals, deletion, and restoration.
- Use a conservative solver configuration. Disable transformations introducing
  unsupported RAT/extension steps; reject an unexpected proof event. Determine
  the exact required options experimentally against this revision.
- Initially use fresh, nonincremental proof instances. Materialize active
  assumptions as correctly attributed unit clauses, including the main-group
  truth constant, or simplify selectors/constants away before submission.
  An assumption-UNSAT conclusion must be closed into the actual refutation.
- Disable yasmv's optional pre-submission CNF optimizer in proof mode until
  its transformations preserve provenance or have proof reconstruction.

Use McMillan's resolution labeling: an A leaf contributes its shared literals,
a B leaf true; an A-local pivot combines labels with OR, other pivots with AND.
Represent labels as shared Boolean circuits so proof sharing is preserved.
[Definition 2 in the paper](https://mcmil.net/pubs/CAV03.pdf).

For every extracted J in the initial implementation, use fresh SAT instances
to check A AND NOT J and J AND B are UNSAT, and verify that its support is
contained in the allowed interface. These checks supplement proof replay.
Retain them as a diagnostic mode after measuring their cost.

## Partitioning and predicate representation

Assign every original clause to A or B at emission time; activation groups are
not partition labels. Freeze the partition definition for each proof query.
Share only semantic state bits at s1 and frozen state parameters. Partition
the following auxiliary identities as well as raw Tseitin variables:

- DD-node/time caches (`find_cnf_var` currently keys only by node and time).
- Arithmetic microcode rewrites and mux auxiliaries.
- Compiler temporary symbols that currently pass through the TCBI map.
- Selector variables and encoded constants, unless eliminated before solving.

Audit all emission paths through `Engine::push`, not just DD CNF. A shared
compiler temporary may represent an internal computation rather than state;
it must not silently survive in an interpolant. Reject unexpected support.
Maintain explicit native-variable-to-semantic-bit mapping rather than assuming
CaDiCaL IDs equal yasmv Var values. Preserve frozen-bit identity when renaming.

Milestone 2 implements this isolation with two distinct recording `Engine`
instances. Each owns its DD, microcode, mux, selector, and temporary namespaces.
`PartitionedCnf` merges their original CNF snapshots, identifying only declared
model state bits by TCBI. A declaration whitelist excludes inputs, instances,
and compiler temporaries. Any shared nonfrozen bit outside the designated cut
is rejected. Signed group assumptions become partition-local unit clauses.
The cut check is syntactic: disabled groups are materialized, not simplified
away before checking shared support.

Introduce a small hash-consed Boolean DAG or AIG for interpolants, with constant
folding, sharing, negation, state renaming, and direct Tseitin emission. Keep
the existing CUDD compiler for model formulas; avoid requiring the entire
growing invariant to become a monolithic BDD.

R starts with the semantic INIT predicate and accumulates disjuncts. Its
representation must support both polarities correctly. Negating a CNF with
existential encoding auxiliaries is not equivalent to negating its state
predicate. Compile semantic predicate negations before CNF conversion, or
provide a verified circuit lowering with definitional auxiliaries. Include
polarity and projection tests in the encoding milestone.

Initially accept deterministic, untimed Boolean state predicates, including
expanded definitions and effective inputs, for INIT/INVAR, target, and
assumptions. Keep nondeterministic transition relations. Diagnose unsupported
predicate constructs and absolute/mixed-time constraints explicitly; supporting
them may require monitors or richer semantic lowering. Audit this eligibility
check against the existing progress checker rather than relying on the weaker
`state_expression` test alone.

## Result and validation contract

Before publishing a proof, check these obligations in fresh ordinary solvers
against the original compiled restricted system:

```text
I*(s) AND NOT R(s)                    = UNSAT
R(s) AND T*(s,s') AND NOT R(s')        = UNSAT
R(s) AND F*(s)                        = UNSAT
```

This follows the existing k-induction verification policy. Fresh solvers share
the compiler/backend, so this is not an independent certified proof checker.
An interrupted or failed verification never publishes `proof.verified: true`.

Record method `interpolation`, invariant circuit and semantic bit dictionary,
model identity, assumptions, vacuity, horizon, image iterations/restarts,
proof/circuit sizes, and completed verification obligations. Bind any reusable
artifact to these semantics. Add a separate versioned invariant artifact when
exposing save/revalidate workflows; do not overload progress graph artifacts.

For reachability return `unreachable` with `scope: unbounded` only after
verification. For safety return `proven`; concrete violations retain normal
trace replay. Approximation-started SAT assignments never become user traces.
Only completed concrete smaller-depth checks justify shortest evidence.

Proposed native API: opt-in `strategy: interpolation` for unbounded `reach`,
and explicit selection on `prove-property`; `auto` initially keeps its current
meaning. Property dispatch currently rejects strategy selection, so update its
validation, schema, documentation, and tests together. Preserve bounded `reach`,
`shortest-reach`, and `check-property` semantics. For interpolation on
`prove-property`, use positive `limits.depth = D` as the concrete search cap,
with h <= D-1; exhaustion without a proof gives `holds_bounded` only when every
concrete depth through D completed. Resource interruption remains UNKNOWN.
Unbounded `reach` can grow h until another budget stops it.
Maintain an ordinary incremental concrete search alongside horizon advancement:
complete each newly exposed depth through h+1 in order. It supplies concrete
`checked_depths`, shortest evidence, and bounded fallback results. An image
iteration is never recorded as one of those concrete checks. Start with serial
execution in the query context; this does not require concurrent query threads.

## Delivery sequence and acceptance criteria

| Milestone | Deliverable | Acceptance gate |
| --- | --- | --- |
| 1 | Pinned CaDiCaL proof probe and installation support | Checked resolution reconstruction on small UNSAT families; explicit handling of unsupported events; assertion-enabled build |
| 2 | Partitioned emission, state predicate circuits, interpolant extraction | Exhaustive small A/B truth-table oracles; Craig obligations; no auxiliary leakage; correct negation/renaming including frozen bits |
| 3 | Standalone forward interpolation search with partial-transition suffix | Exhaustive small graph agreement; real/spurious SAT distinction; terminating unreachable cases; verified invariants |
| 4 | Reach/property query integration and evidence | Existing bounded/shortest contracts unchanged; replay-valid traces; cancellation and shared budgets across all phases; schema and session tests |
| 5 | Benchmarks and selective optimization | Measured end-to-end benefit and memory use before default or portfolio changes |

Essential model regressions: empty INIT; depth-zero target; a reachable bad
deadlock before the suffix horizon; safe deadlocks; unreachable cycles;
spurious images requiring restarts; periodic/toggling systems; frozen values;
finite enums, arrays, and arithmetic microcode; assumptions creating dead ends;
aliases hiding unsupported temporal or nondeterministic predicates. Mutated
proofs and invariants must fail validation. Exercise cancellation during proof
replay, interpolant growth, inclusion testing, and final verification, followed
by another query in a compiled session.

Benchmark safe and unsafe retry/progress examples where applicable, LLVM safety
models, arithmetic-heavy examples, and synthetic systems with short reverse
depth but long simple paths. Compare bounded search, simple-path exhaustion,
k-induction, and interpolation with identical semantics and budgets. Report
wall time including encoding/proof processing/validation, peak memory, horizon,
SAT calls, proof nodes, and invariant DAG nodes.

After the baseline passes: simplify circuits, experiment with frontier images,
and investigate reusing suffix clauses with sound proof bookkeeping. Do not
reuse learned clauses across changed partitions without reconstruction. Defer
backward interpolation, automatic portfolios, progress/liveness reduction, and
default changes until the forward safety implementation has evidence behind it.

Next implementation task: milestone 3. Build the standalone forward search on
`sat::StatePredicate`, `PartitionedCnf`, and the verified interpolant circuits.
Validate the partial-transition suffix against explicit finite graphs before
adding query dispatch in milestone 4.
