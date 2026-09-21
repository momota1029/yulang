# Oracle-aligned static SCC inference session

Status: Authoritative

Date: 2026-09-21

Approved: 2026-09-21, after the user accepted the oracle-aligned replacement
and clarified that `Never` is the ordinary bottom type rather than a special
error fallback.

Scope: replace the user-approved R2 model after oracle audit found its
Failed/Blocked and generic-executor semantics unsuitable, using a concrete
Yulang3 inference owner while retaining the completed F0--F2 static SCC plan.

Independent M3 compiler, specification, and performance review completed
without remaining blocking or major findings. User approval explicitly revokes
the prior R2 decision and supersedes
`2026-09-21-recoverable-scc-execution-r2-draft.md` in its full approved R2
authority scope: Failed/Blocked outcomes, body-error failure seeding,
dependency blocking and cascade suppression, the generic backend, completed-
session conversion, retained publication/lifecycle queries, the added
`ExecutionUnavailable` API, and R2-specific test contracts. Completed F0--F2
contracts remain unchanged.

## 1. Authority and oracle evidence

The frozen semantic oracle is `yulang2-oracle@a58eefc3`. Its relevant behavior
is concrete rather than backend-generic:

- `AnalysisSession` owns the poly arena, inference arena, use tables, SCC
  machine, draft schemes, diagnostics, and provenance
  (`crates/infer/src/analysis/mod.rs`).
- All admitted bodies and resolved uses are lowered before the global analysis
  drain (`crates/infer/src/lowering/body/mod.rs`).
- A resolved name owns a fresh value and exact-pure evaluation effect
  (`lowering/name_ref.rs`, `lowering/expr/constraints.rs`).
- An open use emits `target root <: occurrence value`; a closed use freshens
  the target's finalized scheme (`analysis/session/instantiate.rs`).
- Successful body publication emits `body value <: definition root`
  (`lowering/body/methods.rs`).
- A ready SCC emits component quantification before incoming instantiation
  (`crates/infer/src/scc.rs`, `analysis/session/selection.rs`).
- Component quantification first constructs every member's generalized draft,
  exposes all drafts, then finalizes and installs members one by one before
  returning to incoming instantiation (`analysis/session/instantiate.rs`).
- Registered lowering errors record diagnostics and still finish the
  definition. Missing bodies still receive a root. The definition participates
  in normal SCC closure and its predecessors continue
  (`lowering/body/methods.rs`, `lowering/tests/case_06.rs`).
- A naked unconstrained root generalizes to ordinary positive bottom / `Never`
  (`generalize/tests.rs`). `Never` is the ordinary bottom type, not a special
  error sentinel or fallback.
- Proof-kernel terminal failure discards the whole attempt; ordinary semantic
  diagnostics do not (`lowering/body/mod.rs`).

The oracle has no generic execution backend, opaque publication payload,
Failed/Blocked component states, seven-state publication query, or compact
completed-session conversion. Those are not semantic precedents and are not
carried forward.

## 2. Governing invariant and ownership

F3b introduces one private concrete `InferenceSession`:

```text
SolvedModule::solve(batch)
    -> InferenceSession::new(batch)
    -> session.run()
         -> admit_all_collected_facts()
         -> finish()
```

A future approved F4 inserts `drain_static_components()` between admission and
finish. F3b must neither define nor call a placeholder component drain.

`InferenceSession` solely owns mutable inference state:

- the consumed immutable `ConstraintBatch`, including its F2 plan;
- the `ConstraintStore`;
- projections, definition-root results, diagnostics, provenance, and counters;
- later, live occurrence values, transient component drafts, and finalized
  definition schemes.

`ConstraintBatch` and `SccPlan` remain the authorities for collected identity,
SCC membership, dependency-sink-first order, and internal/incoming partitions.
`DefinitionOrderId` remains a scheduling key only. HIR `DefId` and each
`CollectedDefinition`'s `DefinitionRootId` retain their existing semantic
roles. No solve-time dependency is admitted and no component is reopened.

`SolvedModule` remains the public result owner. `InferenceSession::finish`
moves concrete inference-owned result state into it. There is no
`CompletedSolveSession`, generic payload conversion, component-outcome array,
or public lifecycle query.

## 3. Recoverable semantic errors

Semantic, lowering, and ordinary type errors are diagnostics plus inference
input, not component failure states.

- `CollectedBodyStatus::Error` does not fail an SCC.
- The existing diagnostic owner retains the primary diagnostic; inference does
  not duplicate it.
- The registered definition root remains live and participates in ordinary SCC
  closure.
- The component and every predecessor continue normally.
- There is no failed-dependency blocking or cascade-suppression protocol.
- `Unknown` remains a public projection fallback only. It is never a type,
  constraint endpoint, root substitute, or scheme.
- F3a and F3b introduce no scheme and preserve current `Unknown` projections.
  F4 carries the oracle's ordinary naked-root-to-bottom behavior: an
  unconstrained registered root may generalize to `Never` through the normal
  type rules. No error-status branch injects `Never`, and `Never` is never used
  as a recovery sentinel or presentation fallback.

Current `CrossKind` handling remains local constraint-result behavior: it
records its diagnostic and preserves independent inference. It does not create
an SCC outcome.

## 4. Fixed ordering obligations for the future F4

F4 is not executable under this approval. It must separately define occurrence
and scheme representations, generalization, instantiation, provenance,
test-only observation, counters, retained-byte boundaries, focused checks, and
rollback before code is written.

The following oracle-aligned ordering and direction constraints are fixed for
that future design:

1. Allocate one fresh value and effect component for each resolved binding-body
   occurrence represented by an F0 `DefinitionUse`, and emit exact-pure
   evaluation-effect bounds. Direct-root resolved names remain outside F4 unless
   separately approved.
2. For each newly admitted binding-body kind, emit the whole body-result value
   `<: definition root` relation. In F4's current resolved-Name body surface,
   that body result is the resolved-name occurrence. This is not a rule that
   connects arbitrary nested name occurrences directly to the enclosing root.
   Retain the exact body-result cause and authoritative direction.
3. For every internal use, emit
   `target definition root <: occurrence value`.
4. Generalize every member into one component-local draft vector.
5. Make the complete draft vector available through an ordinal-indexed borrowed
   lookup; a finalizer must not scan the vector to find one member.
6. Finalize and move each member scheme directly into its one durable scheme
   slot while the complete draft vector remains authoritative. Slots may be
   populated one by one, matching the oracle, but incoming uses cannot observe
   them until the component quantification call returns.
7. Only after every member finalizes, instantiate every incoming use into its
   parent occurrence.
8. Continue to the next F2 component.

Temporary drafts are component scratch, not a second retained scheme authority.
F4 must define one total F2-member-to-`CollectedDefinition`/
`DefinitionRootId` mapping and one durable scheme key without inventing a new
semantic definition identity. A finalized scheme does not by itself change the
current `root_value_for` projection; any projection change requires explicit
supersession. Duplicate roots and scheme-versus-root-projection behavior need
focused witnesses.

This copies the oracle's semantic ordering without copying its incremental SCC
graph, reachability searches, edge-map rebuilds, per-append sorting, event
queue, caches, or transient component identities.

## 5. Whole-attempt failure boundary

`InferenceSession::run` returns
`Result<SolvedModule, SolveAvailabilityError>`.

The current availability cases remain whole-attempt failures:

- artifact mismatch;
- cause mismatch;
- receipt mismatch;
- identity exhaustion.

The private session is dropped and no partial `SolvedModule` is returned.
Compiler invariants remain assertions or hard failures rather than recoverable
semantic states. A future proof kernel may add a separately approved typed
`ProofKernelFailed`; it must not be disguised as a semantic diagnostic or a
partial successful result.

## 6. Construction gates

### F3a -- withdraw the R2 implementation

F3a removes the unstaged R2-only implementation and restores the committed
F0--F2 baseline. It does not salvage executor, Failed/Blocked outcome,
publication-query, or execution-ledger code.

Before restoration, F3a must:

1. Pin baseline commit `eb23998f` and tracked baseline blobs:
   - `crates/yu-solver/src/lib.rs` =
     `42a38277711db57aa07aec620e0ddd353f92bf84`;
   - `crates/yu-solver/src/scc.rs` =
     `945baf7dc2d59e74616f549f28703ef7a84f5eed`.
2. Inventory every dirty hunk and attribute it to R2; stop on any unattributed
   hunk.
3. Save an exact path-scoped recoverable patch or copy of all three pre-restore
   solver files and retain it until F3b is accepted.
4. Restore only those three solver targets, leaving this design and index edit
   intact.
5. Verify the tracked blobs match the pinned hashes and `execution.rs` is
   absent.

R2-only uncommitted tests are removed because their governing authority is
superseded, never merely because output differs. No committed F0--F2
expectation or semantic test name may change. F3a synchronizes the successor,
R2, `notes/design/INDEX.md`, and `tasks/current.md` statuses.

### F3b -- concrete session extraction

- Move mutable work currently performed by `SolvedModule::solve` into a private
  concrete `InferenceSession`.
- Do not traverse components, allocate scheme placeholders, introduce lifecycle
  states, expose new public queries, or add source-sized work/storage.
- Preserve all public behavior and representation exactly.

F3b is certified by both semantic before/after differential evidence and
public-API compile/diff evidence. The latter includes a downstream exhaustive
`SolveAvailabilityError` match and existing trait-bound probe plus diff
inspection for added `pub` surface. It must preserve:

- the same four `SolveAvailabilityError` variants and traits, with no new
  public item;
- the `Arc<HirModule>`, occurrence order, `SolverError` order and payloads,
  store facts/provenance order, projections, root values, and foreign-artifact
  query results;
- every existing `ProductionCounters` accessor before queries and after a fixed
  projection/root-query sequence;
- `CrossKind` local-`Unknown` behavior with later independent facts solved;
- error-body plus independent-integer results;
- all F0/F1/F2 plan topology and counters.

Any observable delta rolls F3b back wholesale to the post-F3a F0--F2 baseline.

### F4 -- semantic SCC closure

F4 is a separate M3 design and approval gate. It must implement the obligations
in sections 4 and 7 as one coherent semantic slice. It does not require
Function syntax, application, methods/roles, imports, or Core IR.

## 7. Obligations for the future F4 design

F4 must turn these into executable acceptance criteria:

- isolated definitions, forward/backward chains, a diamond, duplicate uses,
  self recursion, and mutual recursion;
- bounded test-only ordering evidence:
  `internal uses -> all drafts -> all drafts visible -> finalize/install -> incoming instantiations`;
- every use routed exactly once through its F2 partition;
- exact-pure effects for F0 binding-body name uses and the whole body-result
  value `<: definition root` relation. For the current Name-only body surface
  the body result is that occurrence; no arbitrary nested-name-to-root rule is
  introduced. These relations must produce correct chain and diamond schemes,
  while direct-root resolved names remain unchanged;
- missing/error bodies closing normally and predecessors instantiating them;
- ordinary unconstrained-root generalization to bottom/`Never`, with a witness
  that no error-status branch injects it as a fallback;
- independent diagnostics and schemes surviving another definition's error;
- one exact durable scheme identity distinct from scheduling identity and from
  public root projection;
- structural identity inconsistency aborting the whole attempt;
- no fixture-specific or Function-syntax branch.

## 8. Complexity and resources

F0--F2 keep their existing complexity contract. F3b adds no source-sized work
or storage.

The future F4 design must preserve scheduler overhead of:

```text
O(C + D + I + X) + explicitly accounted generalization/instantiation cost
```

where `C` is components, `D` definitions, `I` internal uses, and `X` incoming
uses. It may retain one final scheme per definition and one reusable
`O(max_scc_members)` draft buffer. It must not allocate lifecycle outcomes or
per-use blocker/recovery state.

F4 must pre-size the final-scheme table once. Its resource contract must name:

- component visits, internal connections, draft/finalized members, and incoming
  instantiations;
- draft lookups and cross-draft visits, with full-slice scans per finalizer
  forbidden;
- final-scheme table length/capacity/bytes/rebuilds;
- draft scratch length/capacity/bytes/growth;
- total session retained and peak bytes including the live F2 plan and semantic
  arena;
- semantic-arena retained and peak bytes reported as a named subset of that
  total, never added to it a second time;
- lookup/index probes and rebuilds.

The semantic engine's real costs are reported separately, never silently
omitted. Reuse 1,000/2,000/4,000 chain, diamond, and cycle scheduler families,
with an artifact-valid test-only builder for duplicate `DefinitionUseId`
payloads. Apply the below-2.5x doubling bound only to named linear fields and
keep sort/comparison budgets separate. Ordering observation is bounded test-only
state, never a production trace.

## 9. Stop and rollback conditions

Return to design if implementation requires:

- Failed or Blocked SCC state;
- generic backend callbacks or opaque publication payload;
- component visibility/outcome query;
- a compact second solved-result representation;
- incoming instantiation before all component schemes finalize;
- a no-op structural executor or open-use-only asymmetric semantics;
- dynamic graph rebuilding or solve-time dependency admission;
- a semantic diagnostic returning public `Err`;
- a proof/invariant failure returning partial output.

## 10. Decisions

Approval of this design decides:

1. R2 is superseded in its full authority scope.
2. Yulang3 follows the oracle's concrete session and error-continuation model,
   with F2's static plan replacing only the oracle's incremental SCC graph.
3. The current R2-only worktree diff may be discarded only through the pinned,
   archived, hunk-attributed F3a procedure.
4. F3b is the next implementation gate.
5. F4 ordering/direction, ordinary unconstrained-root bottom behavior, and
   scheme-container ownership, lookup, and publication topology are fixed.
   Semantic scheme payload representation--quantifiers, bounds, recursive form,
   and freshening--plus public projection changes, exact observer, and the
   executable resource contract require separate approval.
