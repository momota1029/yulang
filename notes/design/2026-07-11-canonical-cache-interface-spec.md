# Canonical cache interface specification

Date: 2026-07-11

Status: feasibility and implementation design for Option 1 of
`notes/design/2026-07-11-std-prefix-cache-boundary-concretization.md`.
Implementation has not been approved or started. This document does not amend the role-system
specification and must remain under `notes/design/` until the design is accepted and implemented.

## 1. Purpose

The canonical cache interface must recover the following invariant at a compiled-unit boundary:

```text
cold whole-program generalization
  ≡ prefix finalize -> serialize/import -> suffix instantiate/generalize
```

Here `≡` means equivalence of generalized type interfaces up to alpha-renaming and the explicitly
listed ordering equivalences. Runtime-result equality alone is not sufficient.

The immediate regression is the std-prefix warm path changing an abstract residual role demand into
a concrete input. That causes recursive candidate search in `role_solve` where the cold open graph
keeps the demand residual. The goal is not to suppress that search after it starts. The goal is to
make the imported interface reconstruct the same abstract bounds and sharing that justified the cold
result.

This document specifies:

- closure classes for every type variable crossing the boundary;
- the representation and lifecycle of explicit boundary bounds;
- an operational cache-principal freeze for schemes, role predicates, and impl prerequisites;
- structural alpha-equivalence oracles;
- the relationship to the conservative fallback in
  `crates/yulang/src/std_prefix_cache_safety.rs`;
- staged implementation work and its compatibility with the no-heavy-fixpoint policy.

This document does not claim that the proposed representation has been proved complete for every
future Yulang type-system feature. Unproved points are listed explicitly in section 13.

## 2. Current representation and the missing distinction

`poly::Scheme` currently contains:

```text
quantifiers
role_predicates
recursive_bounds
stack_quantifiers
predicate
```

`SchemeRecursiveBound { var, bounds }` is restored by
`SchemeInstantiator::clone_recursive_bounds` as two subtype constraints around a use-site variable.
It therefore has a per-instantiation lifecycle. The bound is part of the scheme instance.

A cache-boundary variable has a different lifecycle. A variable kept monomorphic by value
restriction or by an outer sharing boundary must:

1. be freshened once when the compiled unit enters a new analysis session;
2. be shared by every imported scheme and role candidate that referred to the same variable;
3. receive its explicit lower and upper bounds once in that session;
4. not be freshened again at each scheme use;
5. remain below the suffix's quantification boundary.

Reusing `recursive_bounds` for this purpose would either freshen a monomorphic variable per use,
which is unsound with respect to value restriction, or stop freshening a recursive scheme variable,
which changes ordinary polymorphic instantiation. The existing field is therefore not sufficient.

The required design has two different explicit bound kinds, not one field with an ambiguous
lifecycle.

## 3. Closure model

For one compiled unit, define three disjoint binder classes conceptually:

- `Q`: ordinary scheme quantifiers, fresh for each scheme instantiation;
- `R`: variables owned by explicit recursive scheme bounds, also fresh for each instantiation;
- `B`: compiled-unit boundary variables, fresh once per imported analysis session and shared across
  schemes and impl candidates.

The current implementation normally has `R` included in `Q`. A canonical implementation may retain
that representation, but instantiation must not rely on the overlap accidentally. Every
`recursive_bounds.var` must be registered in the per-use substitution before its bound graph is
cloned. In version 1, requiring `R ⊆ Q` is acceptable as a validator restriction if all current
producers satisfy it. If a recursive-bound variable outside `Q` exists, the implementation must
either freshen it explicitly as an `R` binder or reject the interface; it must not reuse the raw
`TypeVar` number.

Let `FV(X)` collect type variables from all positive, negative, and neutral nodes reachable from
`X`, including stack-weight type arguments. A canonical exported scheme `S` must satisfy:

```text
FV(S.predicate)
∪ FV(S.role_predicates)
∪ FV(S.recursive_bounds)
⊆ Q(S) ∪ R(S) ∪ B(unit)
```

Additional closure conditions are:

1. A recursive bound may refer to its scheme's `Q ∪ R` and to unit boundary variables `B`.
2. A boundary bound may refer only to `B` and closed concrete structure. It may not refer to a
   scheme-local quantifier or a candidate-local head variable because it is installed before any
   particular use exists.
3. Mutually recursive boundary bounds are permitted. Their graph is unit-scoped and installed as a
   batch.
4. Every `SubtractId` reachable from a scheme must be in `stack_quantifiers` or be proven absent by
   the existing stack cleanup. Version 1 does not introduce a monomorphic boundary `SubtractId`.
   Encountering one makes the interface non-canonical until its semantics are designed.
5. A role impl candidate is closed when every variable in its head and prerequisites is either a
   candidate-head binder or a member of `B`. Candidate prerequisite variables that occur neither in
   the head nor in `B` are not closed.
6. The transitive closure of every referenced `B` bound must be present in the unit interface.

`Pos::Bot` and `Neg::Top` are valid explicit lower and upper bounds for an otherwise unconstrained
boundary variable. They mean Bottom and Top. They are not `Unknown`, error recovery, or a fallback
type.

## 4. Proposed boundary representation

### 4.1 Surface-level table

Boundary bounds belong to the compiled unit, not to one scheme. The proposed logical data model is:

```rust
struct CompiledBoundaryInterface {
    bounds: Vec<CompiledBoundaryBound>,
}

struct CompiledBoundaryBound {
    var: TypeVar,
    bounds: NeuId,
}
```

The names are illustrative; implementation may choose project-consistent names. The semantic
requirements are not optional:

- `var` is a unit-scoped binder declaration;
- `bounds` is a centerless neutral interval, or another existing lifted `Neu` shape with equivalent
  lower/upper projection;
- entries are sorted by a canonical structural key, not source `TypeVar` number;
- a variable has exactly one bound entry after coalescing;
- duplicate declarations must be structurally equal after alpha-renaming or artifact construction
  fails.

The table must be present in both `CompiledTypedSurface` and `CompiledRuntimeSurface`, referring to
the respective surface's type arena. Both copies must be produced from one canonical draft and must
have the same semantic fingerprint. The artifact manifest should record that fingerprint so decode,
merge, and tests can reject typed/runtime disagreement.

This duplication follows the current fact that typed and runtime surfaces are independently
importable. An alternative single table in `CachedCompiledUnitArtifact` would require every surface
consumer to gain an out-of-band dependency and is therefore not the preferred first implementation.

### 4.2 Why the table is not added to `Scheme`

Putting a copied `boundary_bounds` vector on every `Scheme` would make the sharing scope implicit and
would duplicate the transitive closure. More importantly, two schemes could accidentally import the
same source boundary variable as two different target variables. A unit-level table makes sharing an
explicit artifact invariant.

Schemes continue to refer to boundary variables through ordinary `TypeVar` occurrences in their type
graphs. Membership in `CompiledBoundaryInterface` changes the binder class and import lifecycle of
those occurrences.

### 4.3 Artifact and merge behavior

The compiled-unit cache format must be bumped when this table is added. Old artifacts must be cache
misses; they must not be interpreted as having an empty canonical boundary table.

When compiled surfaces are merged:

- each source unit's `B` scope is alpha-renamed disjointly by that source surface's existing type
  importer;
- bounds and all scheme/candidate references use the same importer mapping;
- two boundary variables from different units are not coalesced merely because their bounds are
  equal;
- the merged boundary table is the concatenation after remap, canonical sort, and exact duplicate
  validation;
- typed/runtime semantic fingerprints are recomputed for the merged artifact.

## 5. Producing boundary bounds

Boundary capture is a final interface operation over already-settled inference state. It must not be
a new solver.

### 5.1 Inputs

The producer needs, at the same time:

- finalized exported schemes selected by `CompiledNamespaceSurface`;
- finalized role impl candidates retained in the runtime surface;
- the live `ConstraintMachine` needed to read bounds and `TypeLevel`;
- the generalization decisions (`Q`, `R`, stack quantifiers) already made by the normal pipeline;
- the type-variable mapping used when compact results were finalized into `poly::TypeArena`.

The clean entry point is a pure `AnalysisSession` cache-interface finalizer invoked once by
compiled-unit construction. It should produce one canonical draft consumed by both
`CompiledTypedSurface::from_lowering` and `CompiledRuntimeSurface::from_lowering_with_namespace`.
Building the two tables independently would risk recreating the current detached-view mismatch.

### 5.2 Classification algorithm

The producer performs one reachability traversal:

1. Scan all exported scheme predicates, residual role predicates, recursive bounds, candidate heads,
   and candidate prerequisites.
2. Remove variables bound by each scheme's `Q ∪ R` and candidate-local head binders. A head
   occurrence already classified as unit-owned by its level/sharing decision is not removed here.
3. Preclassify every remaining variable from the existing level/generalization decision as a unit
   boundary variable `B`. This is ownership discovery for bound capture, not a simplification
   protection set. Do not infer binder class from how concrete its current bounds look.
4. For each newly discovered `B`, freeze its current lower/upper bounds from the
   `ConstraintMachine` and enqueue variables reachable from those bounds.
5. Continue until the reachable boundary graph is exhausted.
6. Run the joint normal simplification described in section 7 over the interface component. This may
   eliminate redundant provisional `B` variables but may not introduce new owned variables.
7. Validate the closure rules in section 3 and emit only the retained, transitively reachable sorted
   table.

This is a graph worklist with each boundary variable and type node visited once, not a constraint
fixed point. A bound that would require a newly generated subtype or merge constraint is evidence
that capture ran too late. The correct response is to move that constraint generation into the
existing generalization loop, not to restart capture.

### 5.3 Value restriction and monomorphic boundaries

`BindingFetch::FetchComputation` currently moves the generalization boundary to `boundary.child()`.
The canonical interface must preserve that decision.

The following are mandatory:

- a variable rejected from quantification by value restriction remains in `B` if it crosses the
  compiled-unit boundary;
- it is never added to `Q` merely to satisfy closure;
- it is never labeled `R` unless it is an actual per-use recursive scheme binder and was eligible for
  per-use instantiation;
- every use of every imported scheme sees the same session-level target variable for that `B`;
- suffix generalization treats the target boundary variable as root-level/non-quantifiable;
- a suffix artifact that re-exports it includes the corresponding boundary closure again.

These rules also apply to non-expansive definitions that share an outer monomorphic variable. The
criterion is binder ownership, not expression syntax alone.

## 6. Import and instantiation lifecycle

### 6.1 Import once

Runtime import must use one `CompiledTypeImporter` mapping for schemes, role candidates, and boundary
bounds. The imported boundary table is retained by `BodyLoweringPrefix` and passed to a new
boundary-aware `AnalysisSession` constructor.

At session initialization:

1. allocate one fresh infer `TypeVar` for every imported `B`;
2. build a persistent `poly TypeVar -> infer TypeVar` boundary substitution;
3. clone all boundary bound graphs through that substitution;
4. register all boundary variables at root level;
5. install `lower <: B` and `B <: upper` for the whole table as one batch;
6. route the resulting ordinary constraint events before suffix use instantiation;
7. seed imported schemes as quantified SCC definitions and seed role candidates only after the
   boundary substitution exists.

The batch may contain cycles. Installation must not recursively expand them in the importer; the
ordinary constraint machine owns propagation.

### 6.2 Scheme instantiate

`SchemeInstantiator` receives the persistent boundary substitution as a preloaded mapping.

- `Q` and `R` receive fresh per-use mappings.
- `B` entries keep the preloaded session mapping.
- recursive bounds are cloned and added for the per-use mappings.
- boundary bounds are not replayed at each use.
- an unmapped free variable is a canonical-interface violation. Returning the unchanged source
  `TypeVar`, as current non-`freshen_unmapped` cloning can do, is forbidden on the canonical cache
  route.

### 6.3 Role candidate freshening

Current `freshen_role_impl_candidate` freshens every unmapped candidate variable when a session is
created. The canonical form keeps that behavior for candidate-local head variables, but preloads the
same boundary substitution first. A candidate occurrence of `B` must therefore point at the same
infer variable as every imported scheme occurrence of `B`.

This shared substitution is the minimum topology needed to preserve relationships between a cached
scheme and an impl prerequisite. Serializing the entire `ConstraintMachine`, SCC graph, or birth
levels remains out of scope.

## 7. Cache-principal freeze

“Principal form” is used operationally here. The implementation must establish the deterministic
normal form below and preserve the same instance set. A theorem that this normal form is unique for
all Yulang types has not been established.

### 7.1 Scheme and residual role predicates

The freeze input is the final joint compact view from normal generalization, not a role-only view and
not a reconstruction from formatted `poly::Scheme` text.

For one scheme, freeze performs:

1. Start after the existing compact/merge/dominance/cast/role loop has settled.
2. Use the same floor normalization for role resolution and output freeze. There must not be separate
   “solve floor” and “fallback/output floor” interpretations.
3. Apply already-established impl-member simplifications and ancestor simplifications.
4. Run the existing interval equalities, variable sandwich, constructor sandwich, co-occurrence, and
   polarity elimination over the main type and all residual role predicates jointly.
5. Include reachable boundary bounds in occurrence accounting when they are part of the interface
   component. Do not mark `B` rigid and do not add a protected-variable set. If ordinary
   simplification can remove a redundant boundary variable without changing the instance set, it
   should disappear.
6. Preserve centerless invariant intervals. `Neu::Bounds(lower, upper)` stores only the two bounds;
   a display center is never serialized.
7. Apply role-declaration variance only at the residual `where` boundary:
   `Covariant` freezes the lower side, `Contravariant` the upper side, and `Invariant` the neutral
   interval. Associated types remain invariant.
8. Remove a role demand only when the existing joint main-plus-all-roles final disposition proves it
   was already applied. A role-only re-solve must not delete it.
9. Do not resolve or delete a predicate merely because the current impl table happens to contain a
   candidate. Cache interfaces must remain valid when the suffix adds candidates.
10. Sort associated types by name. Sort and deduplicate residual predicates by a structural key after
    binder normalization. Preserve duplicates if the role semantics later proves them multiplicative;
    current role constraints are treated as idempotent, but this assumption needs a test.

Freeze is pure. If interval merging discovers an unapplied `loA <: upB` or `loB <: upA` condition,
freeze fails the canonical validator. The condition belongs in the existing generalization loop,
where merge-constraint keys already control restarts.

### 7.2 Relationship to floor and co-occurrence simplification

The required order is:

```text
existing constraint settling
  -> preliminary Q/R/unit ownership classification
  -> one boundary-bound closure capture
  -> joint compact collect (main + all residual roles + captured boundary bounds)
  -> shared floor normalization
  -> co-occurrence / interval equality / sandwich / polarity elimination
  -> prune eliminated boundary entries and validate final Q/R/B closure
  -> pure structural freeze and canonical ordering
```

Boundary classification must not be used to stop the structural simplifications. In particular, the
design must not introduce boundary-rigid variables, blocked pairs, or a “through” flag. Those would
violate the current Simple-sub 4.3 core policy and could reproduce the old protection machinery under
a cache-specific name.

The preliminary ownership classification does not force a variable to survive. Floor cleanup still
runs before the final retained `B` table is chosen. A shallow variable that is only a redundant floor
component should be eliminated by the existing justified rule, not serialized into `B` merely
because it is shallow.

### 7.3 Impl head and prerequisite freeze

An impl candidate is frozen as one connected interface component:

- the head inputs and associated types are anchors;
- all prerequisites are included in the same occurrence/co-occurrence analysis;
- head matching remains invariant and keeps centerless lower/upper intervals;
- prerequisite demands use normal role-constraint simplification after the head substitution;
- shared variable identity between head and prerequisites is preserved;
- prerequisites are sorted and deduplicated by structural key after normalization;
- no candidate search or recursive discharge runs during freeze.

After normalization, every prerequisite variable must occur in the head or in `B`. A variable that
occurs only in prerequisites cannot be silently quantified: doing so may change a shared
monomorphic condition into a universally instantiated one. If its intended status cannot be derived
from existing levels and sharing, artifact construction must report a non-canonical interface and
the implementation stage must stop for a design decision.

This is intentionally stricter than the current `collect_role_impl_member_prerequisites`, which
copies a predicate when it contains a variable outside the member scheme quantifiers. The current
test is useful for collection but is not a complete binder specification.

## 8. Canonical interface validator

The validator is required both as an implementation aid and as a permanent cheap artifact check. It
must report structured reasons, at least:

- `UnboundSchemeVariable`;
- `UnboundCandidateVariable`;
- `BoundaryDependsOnLocalBinder`;
- `MissingBoundaryBound`;
- `ConflictingBoundaryBound`;
- `UnboundSubtractId`;
- `TypedRuntimeInterfaceMismatch`;
- `FreezeProducedConstraint`;
- `NonCanonicalOrdering`.

The validator traverses each reachable arena node once and memoizes `PosId`, `NegId`, and `NeuId`.
It is not allowed to resolve roles, instantiate schemes, or mutate the constraint machine.

Artifact construction must not write a supposedly canonical artifact after validator failure.
Artifact decode treats a version/fingerprint/closure failure as a cache miss. User programs must not
receive a type error merely because a cache artifact is absent or stale.

## 9. Alpha-equivalence test oracle

### 9.1 What “immediately after instantiate” means

There is no `Scheme` object immediately after `instantiate_scheme_with_roles`. The result is an infer
predicate, cloned role predicates, and recursive constraints already inserted into the target
machine. A test that claims to compare two schemes at that point would be comparing unlike objects.

The implementation therefore needs a test-only `InstantiationWitness` (name illustrative) containing:

- instantiated predicate;
- instantiated role predicates;
- the `Q/R` source-to-target mapping;
- the session `B` mapping;
- cloned recursive bound pairs before or as they are inserted;
- stack-quantifier mapping.

Production instantiation may continue to return its compact current result; the witness is a testing
view over the same operation, not a second instantiator.

### 9.2 Structural alpha view

Both the expected symbolic instantiation and the actual imported witness are converted to a
`SchemeAlphaView` with separate namespaces for:

- per-use type binders (`Q/R`);
- unit boundary binders (`B`);
- stack/subtract binders.

The view recursively records all positive, negative, and neutral constructors, role paths, input
variance, associated-type names, recursive bounds, and boundary bounds. Binder numbers are assigned
by deterministic first structural occurrence after canonical collection ordering, never by raw
`TypeVar`, arena node ID, or `SubtractId`.

The equality relation must be a bijection within each binder class. It must reject a mapping that
turns two shared source variables into two target variables or merges two source variables into one.
It must also reject changing a `B` binder into a per-use binder even if the printed type is the same.

The following collections are compared as canonical sorted collections:

- residual role predicates;
- associated types by name;
- recursive-bound entries by normalized binder and bound fingerprint;
- unit boundary entries by normalized binder and bound fingerprint.

Function slots, tuple order, role argument order, record field semantics, and constructor argument
order remain ordered. Union/intersection flattening or reordering may be included only where the
cache freeze itself defines that canonical operation. The alpha oracle must not hide a semantic
difference by applying extra subtype algebra unavailable to freeze.

Exact alpha-equivalence for mutually recursive bound graphs needs either partition refinement over
the finite labeled graph or a proven canonical SCC encoding. Choosing between those algorithms is
an implementation decision still marked as unconfirmed in section 13. A factorial permutation
search is not acceptable.

### 9.3 Oracle A: binder lifetime and artifact round-trip gates

Oracle A is split into two stage-aligned gates. This split preserves the full invariant while
avoiding a dependency cycle in which Stage 3 required the production artifact support enabled only
by Stage 5.

#### Oracle A1: in-memory import and binder lifetime (Stage 3)

For each selected exported scheme:

1. Construct its canonical `CompiledBoundaryInterface` in memory.
2. Seed that table into one fresh analysis session.
3. Instantiate the imported scheme twice before suffix constraints are added and assert:
   - `Q/R` binders differ between uses;
   - `B` binders are identical between uses and equal the session-level imported mapping.
4. Freshen the analogous role candidate in the same session and assert:
   - candidate-local head variables are freshened;
   - candidate `B` occurrences equal the scheme `B` mapping.

This is the Stage 3 exit witness. It tests the importer and instantiator lifetime rules directly and
does not claim that a non-empty compiled-unit artifact is accepted by the production decoder.

#### Oracle A2: production artifact round trip (Stage 5)

For each selected exported scheme:

1. Build its expected symbolic instantiation from the pre-serialization canonical interface.
2. Encode and decode the actual compiled-unit artifact through the production cache format.
3. Import the decoded boundary table into a fresh analysis session.
4. Instantiate the imported scheme before suffix constraints are added.
5. Compare expected and actual `SchemeAlphaView` values.
6. Repeat the Oracle A1 lifetime assertions after decode, including scheme/candidate `B` identity.

Oracle A2 is the Stage 5 artifact-integration gate. It must not be replaced by a raw envelope decode
that bypasses version, fingerprint, typed/runtime agreement, or closure validation.

### 9.4 Oracle B: cold/warm suffix-result equivalence

The whole invariant also needs an end-to-end oracle:

1. Run the fixture cold with the full source set and no prefix cache.
2. Build only the prefix artifact, then compile the same suffix through the warm prefix route.
3. Build `CompiledNamespaceSurface` for both results.
4. Match selected suffix values by `(module path, value name, declaration order)`. The namespace
   `symbol` may be used after this match, but raw `DefId` is not stable across routes.
5. Compare their finalized schemes with the structural alpha oracle, including role predicates and
   recursive/boundary closures.
6. Separately compare the canonical candidate interface for suffix-visible impls.
7. Retain runtime-result equality and phase timings as additional, not substitutive, checks.

The first mandatory fixture is the Yumark HTML reproduction from the boundary-concretization note.
The existing role-equivalence canary remains useful as a safe warm-path control. Tests should also
cover:

- two uses of one value-restricted imported scheme sharing `B`;
- two distinct schemes sharing one `B`;
- one scheme and one impl prerequisite sharing one `B`;
- a recursive scheme using fresh `R` per use;
- an invariant role interval whose lower/upper center is display-only;
- covariant and contravariant residual role inputs;
- artifact merge keeping boundary scopes disjoint;
- a deliberately malformed artifact rejected by the validator.

### 9.5 Existing dump commands

`dump-poly-std` and `dump-poly-std-raw` are useful for diagnosis and human-readable golden tests.
They are not sufficient as the alpha-equivalence oracle:

- raw dumps expose arena-local IDs;
- formatted dumps name variables by rendered occurrence order;
- formatted output does not encode binder lifecycle (`Q/R` versus `B`);
- future display redaction or ordering changes should not change semantic equality;
- the current dump does not include a unit boundary-bound table because it does not yet exist.

After implementation, raw dump should display boundary binders and bounds for debugging, but test
pass/fail must come from the structural comparator.

## 10. Relationship to the conservative fallback

Commit `a0934e57` added a program-sensitive fallback. It rejects the warm std-prefix route when the
suffix has a prerequisite-bearing impl and the cached runtime surface has an open scheme or
candidate boundary.

During Option 1 implementation, this fallback must remain enabled. It is the safety net while
artifacts and importers may still be mixed canonical/non-canonical.

Once Option 1 is complete, the current fallback should not remain as the permanent correctness
mechanism:

- a versioned canonical artifact cannot contain the open conditions it scans for;
- scanning suffix CST for `impl ... where` is unrelated to the final canonical invariant;
- retaining the heuristic could hide regressions by silently converting expected warm tests into
  cold runs;
- it adds a std-prefix-specific policy where the invariant should apply to every compiled unit.

The recommended retirement sequence is:

1. Keep `std_prefix_cache_safety.rs` during Stages 0-6 below.
2. Add shadow telemetry/tests proving that canonical artifacts never trigger it and that the
   Yumark fixture takes the warm route with alpha-equivalent schemes.
3. Require explicit cache-route assertions so a fallback cannot make equivalence tests pass.
4. Remove the suffix syntax scan and open-boundary heuristic in a separate change.
5. Retain the cheap, format-independent canonical interface validator at artifact write/decode.
   Validator failure is treated as a cache miss and is not the old program-sensitive heuristic.

Thus defensive validation remains, but `std_prefix_cache_safety.rs` itself can be removed after the
gates pass. Removal before those gates would be premature.

## 11. Implementation stages

Sizes are rough review scale, not calendar commitments. `S` is a focused change, `M` spans several
types/import paths, and `L` changes an inference boundary and requires multiple regression layers.

### Stage 0: closure inventory and test oracle skeleton

- Changes: add read-only closure scanners, structured violation reasons, alpha-view data model, and
  characterization tests for current cold/warm output. No production route change.
- Likely targets: `crates/infer` test/support modules, `crates/yulang/tests/cli.rs`.
- Size: M, roughly 3-5 files and 400-700 lines including tests.
- Risk: medium; an overly permissive alpha view can make later tests lie.
- Dependencies: none.
- Exit: the current Yumark case is shown to differ at the scheme/interface level, and malformed
  binder classes are rejected.
- No-heavy-fixpoint: structural graph traversal only; no solver mutation.

### Stage 1: boundary surface and cache schema

- Changes: add `CompiledBoundaryInterface` to typed/runtime surfaces, import/remap/merge/hash support,
  manifest fingerprint, and compiled-unit format bump. Initially allow only an empty table.
- Likely targets: `compiled_typed.rs`, `compiled_runtime.rs`, `cache.rs`, surface tests.
- Size: M, roughly 5-7 files and 300-600 lines.
- Risk: medium; typed/runtime arena remaps must use the same semantic table.
- Dependencies: Stage 0 validator/fingerprint definitions.
- Exit: empty-boundary artifacts round-trip, merge, and reject old formats deterministically.
- No-heavy-fixpoint: mechanical clone/remap and one hash traversal.

### Stage 2: canonical scheme export and boundary capture

- Changes: produce the unit `B` closure from finalized schemes and live machine bounds; integrate the
  shared floor/co-occurrence/sandwich result; enforce value-restriction classification.
- Likely targets: `analysis/session/generalize.rs`, `generalize.rs`/finalize modules,
  `compiled_typed.rs`, focused infer tests.
- Size: L, roughly 6-10 files and 700-1,200 lines including tests.
- Risk: high; this is where an apparently harmless quantification or late simplification could
  change the instance set.
- Dependencies: Stages 0-1.
- Exit: every exported scheme validates under `Q ∪ R ∪ B`, and no new constraint is discovered by
  freeze.
- No-heavy-fixpoint: one reachability worklist and one pure freeze. Any need for a restart is routed
  back to the existing generalization constraint lanes, not implemented as a new loop.

#### 2026-07-11 session progress note

Stages 0 and 1 are committed. Stage 0's closure scanner and structural alpha view establish that the
Yumark HTML fixture is not alpha-equivalent across the current cold/warm boundary, while the Markdown
fixture is alpha-equivalent. Stage 1 wires an empty `CompiledBoundaryInterface` through the typed and
runtime surfaces without changing production behavior.

An experimental Stage 2 boundary capture reproduced the HTML cold abstract shape: an open interval
equivalent to `Bounds(Union(Var, Concrete), Var)`. This is positive evidence that the capture approach
is directionally correct. However, the mandatory strict no-new-constraint audit found two previously
unapplied subtype/dominance keys while freezing std's own `std.control.flow.label_sub.sub`. This is
independent of either Yumark fixture.

Section 5.2 requires a newly discovered constraint to be handled by the existing generalization loop,
not by restarting capture. The session also had an explicit stop condition: if Stage 2 appeared to
require a change to that loop, implementation had to stop. Therefore all experimental Stage 2 changes
were rolled back and were not committed. The worktree was clean at the stop point; no boundary-capture
implementation from the experiment remains.

The Markdown merge audit initially reported 23 apparently new keys, but comparison against the
existing generalization applied-key sets showed that all 23 were already known. The session stopped
at the independent std blocker before reaching the Markdown fixture's final abstract-shape check.

Stage 2 must not resume until the two `std.control.flow.label_sub.sub` keys are classified between
these alternatives:

1. Existing generalization is allowing dominance/subtype facts that it should settle to pass through.
   The fix then belongs to the existing generalization loop, outside Stage 2 boundary capture.
2. The experimental freeze order or interface-component construction created dominance conditions
   absent from normal generalization. The Stage 2 algorithm must then be revised.

The exact restart point is to identify the type variables and source constraints represented by those
two keys in `std.control.flow.label_sub.sub`, then determine which side owns them. Do not resume the
Stage 2 implementation or weaken the strict audit before that classification is complete.

### Stage 3: boundary-aware import and instantiation

- Changes: carry imported boundary metadata through `BodyLoweringPrefix`; seed one session mapping;
  preload it in scheme instantiation and candidate freshening; make unmapped canonical free variables
  an error; expose test-only instantiation witnesses.
- Likely targets: `lifecycle.rs`, analysis `instantiate.rs`, core `instantiate.rs`, compiled runtime
  import, lowering prefix wiring.
- Size: L, roughly 6-9 files and 600-1,000 lines including tests.
- Risk: high; incorrect mapping lifetime breaks value restriction or cross-scheme sharing.
- Dependencies: Stage 1; Stage 2 is required for non-empty production artifacts but unit tests can use
  synthetic tables.
- Exit: Oracle A1 passes with an in-memory `CompiledBoundaryInterface`: two scheme instantiations
  freshen `Q/R`, share one session-level `B`, and the analogous role candidate shares that same `B`.
- No-heavy-fixpoint: one batched boundary seed plus existing constraint event routing.

### Stage 4: principal impl prerequisite interface

- Changes: jointly canonicalize candidate heads/prerequisites, classify candidate boundary variables,
  serialize their shared `B` references, and validate closure.
- Likely targets: analysis prerequisite collection, role candidate finalization, `role_solve/mod.rs`
  candidate compact cache, compiled runtime import tests.
- Size: L, roughly 5-8 files and 600-1,000 lines including tests.
- Risk: high; prerequisite-only variables do not yet have a fully proved binder interpretation.
- Dependencies: Stages 0-3.
- Exit: candidate prerequisites are closed under head binders plus `B`, and candidate freeze performs
  no role resolution.
- No-heavy-fixpoint: one per-candidate compact normalization; no recursive candidate search during
  export.

### Stage 5: artifact integration and cold/warm equivalence

- Changes: construct one canonical draft for both surfaces, enable non-empty boundary artifacts,
  implement Oracle A2 and Oracle B, add merge and malformed-artifact tests.
- Likely targets: compiled-unit construction in `cache.rs`, compiled surface tests, CLI integration
  tests, Yumark cache fixtures.
- Size: M-L, roughly 4-7 files and 500-900 lines including fixtures/tests.
- Risk: high; a test can accidentally take full-miss and conceal warm-route failure.
- Dependencies: Stages 1-4.
- Exit: Oracle A2 passes the production compiled-unit encode/decode/fresh-session-import round trip;
  Oracle B observes an explicit `std-prefix-hit`, alpha-equivalent suffix schemes/candidates, and
  equal runtime results.
- No-heavy-fixpoint: comparison and validation are offline structural passes.

#### 2026-07-12 production writer / reuse-gate resolution

Claude Sonnet 5 and the user confirmed that compiled-unit artifact construction remains prefix-only
and independent of the program-sensitive std-prefix reuse gate. The writer always attempts the
canonical typed/runtime handoff. It persists the non-empty boundary pair only when construction and
exact structural-key agreement succeed; otherwise it persists the previous empty-boundary pair.

`std_prefix_cache_safety` remains a separate suffix-dependent gate at reuse time, after artifact
read/build and before warm lowering. Its decision, call order, and protection scope are unchanged.
In particular, an artifact may be constructed canonically and still be rejected for a particular
suffix. The rejected suffix follows the existing full-compile route. The alternative two-phase
writer design, in which suffix eligibility controls artifact contents, is explicitly not adopted.

### Stage 6: performance and shadow validation

- Changes: measure cold/warm role-resolution time, boundary table size, validator cost, and fallback
  shadow result; add a performance regression threshold only after stable measurements.
- Likely targets: timing/metrics, CLI performance tests or scripts, design/progress notes.
- Size: S-M, roughly 2-5 files and 200-500 lines.
- Risk: medium; wall-clock thresholds can be noisy, so role-solver counters and route assertions are
  primary.
- Dependencies: Stage 5.
- Exit: the Yumark warm path no longer performs the pathological recursive candidate expansion and
  retains a useful cache advantage. This outcome is expected, not guaranteed by the design alone.
- No-heavy-fixpoint: observation only.

### Stage 7: fallback retirement decision

- Changes: remove the program-sensitive std-prefix fallback and suffix CST scan, retain canonical
  artifact validation, and update tests to require warm hits.
- Likely targets: `std_prefix_cache_safety.rs`, `main.rs`, CLI tests.
- Size: S, roughly 2-3 files with net deletion.
- Risk: medium-high if performed without Stage 6 evidence.
- Dependencies: all earlier Stages and an explicit implementation decision by the user/maintainer.
- Exit: all compiled-unit boundaries use the same canonical invariant; invalid artifacts become
  misses, not program-sensitive warm/cold decisions.
- No-heavy-fixpoint: removes a scan; no infer change.

## 12. No-heavy-fixpoint audit

The design is compatible with the project policy only under these constraints:

- Boundary discovery is a finite reachability traversal with visited sets, `O(V + E)` in the
  exported interface graph.
- Boundary seed is one batched constraint insertion. Existing constraint propagation may run, but no
  cache-specific settle loop is added.
- Scheme freeze is a pure final transformation over the already-settled compact result.
- Candidate freeze does not call `resolve_role_constraints` and does not recursively discharge
  prerequisites.
- Alpha normalization is test/artifact tooling, not an inference hot-path solver.
- Canonical sorting uses structural fingerprints computed once per node; repeated full-tree compares
  should be avoided.
- Typed/runtime construction consumes one shared draft instead of rescanning the complete prefix
  independently.

The main potential violation is Stage 2: if boundary freeze emits new interval merge or dominance
constraints and then repeats compact collection until stable, it becomes a second generalization
loop. That design is rejected. The new constraint must be generated in the existing merge/dominance
lane before the final snapshot, keyed by the existing applied-constraint sets.

A second potential violation is alpha-equivalence for recursive graphs. A naive permutation search
over binders can be exponential. The implementation must use deterministic SCC encoding or
partition refinement.

## 13. Unconfirmed points

The following are deliberately not guessed:

1. **Completeness of `B` bounds.** It is not proved that explicit reachable lower/upper bounds plus
   shared variable identity preserve every cold co-occurrence fact relevant to future solver rules.
   Stage 0/5 counterexamples may require revisiting Option 1's summary representation.
2. **Uniqueness of the cache-principal form.** Existing floor, co-occurrence, sandwich, and polarity
   elimination rules are operationally specified, but no confluence/unique-normal-form theorem is
   available here.
3. **Exact alpha algorithm for recursive graphs.** Partition refinement and canonical SCC encoding
   are both plausible; their exact equality conditions need implementation-level validation.

   **Resolution (2026-07-12): conservative ambiguity rejection is the shipped policy.** Claude
   Sonnet 5 and the user confirmed that a symmetric or otherwise ambiguous boundary graph continues
   to produce `None` from `semantic_fingerprint_with_types`, making the artifact a cache miss. Stage
   5 does not choose or implement a complete canonical SCC algorithm. That work may be reconsidered
   only if Stage 6 measurements identify this rejection as a material source of repeated misses.
4. **Prerequisite-only binder meaning.** A variable that occurs only in an impl prerequisite may be
   an omitted head dependency, a shared boundary variable, or an unsupported existential. It must not
   be classified by convenience.

   **Resolution (2026-07-12): strict canonical rejection.** After the one permitted joint candidate
   normalization, any variable that still occurs only in prerequisites and belongs to neither the
   normalized head binders nor the known unit `B` table is an `UnboundCandidateVariable`. Artifact
   construction rejects that candidate as non-canonical, so the cache route falls back to the slower
   full compilation path. It is not promoted to `B`, implicitly quantified, or treated as an
   existential. This matches the existing conservative-cache policy: an interface that cannot be
   proved closed is not cached. Provenance tracking may be reconsidered only if Stage 6 measurements
   show that this strict gate causes material cache misses; it is not part of Stage 4.
5. **`R` outside `Q`.** Current tests show quantified recursive variables, but this investigation did
   not prove that every produced `recursive_bounds.var` is in `quantifiers`. Stage 0 must inventory
   this before choosing validation-only or explicit `R` freshening.
6. **Boundary stack identities.** The design assumes existing cleanup leaves only
   `stack_quantifiers`. A monomorphic `SubtractId` crossing a unit boundary has no specified `B`
   analogue yet.
7. **Idempotence of duplicate role predicates.** Canonical dedup assumes duplicate residual demands
   are logical conjunction facts rather than multiplicities. This needs confirmation from role
   semantics/tests.
8. **Private/local definition correspondence.** `(module path, name, declaration order)` is adequate
   for exported CLI oracle targets. A general oracle for anonymous/local definitions needs a stable
   source identity not currently specified here.
9. **Performance result.** Restoring the abstract shape should remove the observed 4.25-second search,
   but the magnitude and cache win must be measured after implementation.
10. **Formal invariant strength.** Passing both round-trip and fixture cold/warm alpha tests is strong
    evidence, not a universal proof over all programs or future impl-table extensions.

Any implementation encountering one of these points must preserve it as an explicit blocker or
validator failure. It must not substitute unconditional quantification, `Any`, predicate deletion,
rigid/protected boundary variables, or a new solver loop.

## 14. Acceptance gates for declaring Option 1 complete

Option 1 is complete only when all of the following hold:

- every written canonical compiled-unit artifact passes closure validation;
- typed and runtime boundary fingerprints agree;
- imported schemes never leave an unmapped free `TypeVar`;
- `Q/R` and `B` lifetimes pass the two-instantiation witness test;
- impl prerequisites close under head binders plus `B`;
- Oracle A1 passes the in-memory two-instantiation and scheme/candidate binder-lifetime witness;
- Oracle A2 passes production encode/decode/fresh-session-import/instantiate round trips;
- Oracle B passes the Yumark reproduction and representative safe role-polymorphic fixtures;
- tests assert the actual warm cache route;
- role-solver counters show the pathological recursive expansion is absent;
- no cache-specific fixed-point/restart loop has been added;
- the current fallback's shadow predicate remains false for all canonical fixtures.

Only after these gates should Stage 7 consider removal of the conservative fallback.

Investigation and specification design: Codex (gpt-5.6-sol), 2026-07-11 session. Whether and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a feasibility and design specification, not an implementation commitment.

*Revision decision (2026-07-11): Claude Sonnet 5 and the user approved splitting Oracle A into the
Stage 3 in-memory binder-lifetime gate (A1) and the Stage 5 production artifact round-trip gate (A2).
The original Stage 3 exit accidentally depended on non-empty artifact decode support assigned to
Stage 5. This revision removes that stage dependency cycle without weakening either validation gate.
Changes to this allocation require explicit user approval.*

*Revision decision (2026-07-12): Claude Sonnet 5 and the user approved strict rejection for the
section 13.4 prerequisite-only binder case. A variable that survives joint candidate normalization
outside both the head binders and known `B` makes the candidate non-canonical and forces the existing
safe full-compile fallback. This decision deliberately avoids changing prerequisite collection or
inventing binder provenance; provenance may be reconsidered after Stage 6 evidence. Changes to this
policy require explicit user approval.*
