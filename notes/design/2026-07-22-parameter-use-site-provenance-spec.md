# Parameter use-site provenance across scheme instantiation

Date: 2026-07-22

Status: draft reference design for a staged parameter-use-site provenance project. This document
specifies the representation, invariants, rollout order, and diagnostic-integration gates, but does
not authorize implementation of any slice.

Current-code citations were re-verified against the working tree on 2026-07-22. Line references
identify the code shape investigated for this design and must be rechecked at the start of each
implementation slice.

The immediate predecessor and foundation are:

- commit `e5b32137` (`infer: explain missing implicit cast boundaries`), which adds the current
  call-site explanation for `MissingImplicitCast` diagnostics;
- `notes/design/2026-07-21-constraint-provenance-redesign-spec.md`, which defines the persistent
  canonical derivation graph, its semantic-isolation invariants, its same-session boundary, and the
  bounded CPROV-H explanation API.

This project extends those results. It does not replace the existing call-site explanation, reopen
the base CPROV representation decisions, or create a second diagnostics-only provenance system.

## 1. Purpose and problem statement

### 1.1 User-facing gap after the first explanation slice

The first diagnostic-explanation slice can now explain a missing implicit cast at an application
boundary in terms of the caller:

- this argument expression supplied the inferred source type;
- this callee requires the resolved target type.

That is sufficient when the callee's parameter type is explicitly declared. For example, in:

```text
f(x: bool): bool = x
f(42)
```

the annotation itself owns the `bool` requirement. There is no deeper inference step to explain.

It is not sufficient when the parameter is unannotated and its type is inferred from the function
body. The representative case is:

```text
f(x) = if x { 1 } else { 2 }
f(42)
```

Here the useful explanation is not merely "the callee requires `bool`." It is:

```text
the argument has type int
the parameter x is required to be bool
because x is used as this if condition
```

The persistent graph already contains much of the local structural proof, but the live diagnostic
cannot follow it through the generalized function scheme. This project supplies the two missing
provenance layers.

### 1.2 Concrete investigation evidence

The feasibility investigation constructed the unannotated-parameter case and queried the original
parameter's upper bound directly.

The original parameter was allocated as a fresh `TypeVar` at
`crates/infer/src/lowering/expr/lambda.rs:637`. A local use reuses or instantiates that value at
`crates/infer/src/lowering/name_ref.rs:122-145`; `RefUse` retains the use's `SourceSpan`, but that
span is not part of the constraint graph. The `if` lowering then applies its junction and constrains
the resulting condition value to `bool` at `crates/infer/src/lowering/control.rs:72-86`.

For the investigated session, querying the original parameter's relevant upper-bound record reached
the body-created `bool` requirement through 19 graph nodes and 18 edges. The decisive leaf was a
three-node chain:

```text
parameter/body upper bound
    -> root constraint requiring bool
    -> Origin(UnknownInternal)
```

The graph therefore already knows that a particular body-side bound caused the parameter to become
`bool`. It does not know that the root means "used as an if condition," and it cannot recover the
condition's source span from that root.

The call-side `NominalCastNeeded` producer was different. Its bounded explanation contained 11 nodes
and 9 edges and reached the application-argument boundary, but it did not reach the original
parameter bound at all. The instantiated callee predicate was rooted as `Internal`, so traversal
stopped at the copied scheme shape. The original parameter bound remained alive in the same
`ConstraintMachine`; it was simply disconnected from the instantiated copy.

These observations establish two distinct loss points:

1. body requirement creation loses semantic source ownership and location;
2. generalization/instantiation copies semantic type structure without copying a derivation link to
   the original same-session bound witnesses.

### 1.3 Decided architectural direction

**Decided:** this project adds true scheme-generalization and scheme-instantiation records and edges
to the persistent derivation graph.

It does not add a diagnostic-only `(DefId, parameter_index)` lookup table containing preformatted or
preprojected explanations. A diagnostics-only table would create a second provenance model with a
separate lifecycle, completeness policy, and traversal semantics. It could drift from the canonical
constraint graph and would be unusable by future non-diagnostic consumers.

The chosen model keeps one provenance system:

- body requirements are source-owned root leaves in the existing graph;
- finalized same-session schemes retain graph witness records for the original bounds they contain;
- each same-session instantiation adds typed graph edges from the instantiated canonical facts back
  to those generalized witnesses;
- CPROV-H queries traverse those edges with the same visited set and hard budgets used today.

The implementation may use session-local indexes to locate graph records. Such an index is not a
parallel provenance mechanism: the evidence itself remains canonical graph nodes and edges, and the
index is never consumed directly by diagnostics.

### 1.4 Relationship to the base CPROV project

The base CPROV project remains authoritative for:

- canonical semantic constraint and bound records;
- append-only, deduplicated incoming derivation edges;
- exact binary replay parentage;
- semantic/provenance epoch separation;
- bounded, deterministic, cycle-safe queries;
- the same-session boundary;
- the prohibition on full proof-path materialization;
- graceful `Incomplete` reporting when provenance is unavailable or budget-limited.

This project adds new root and edge categories to that model. It does not alter subtype semantics,
generalization semantics, instantiation semantics, OCAST eligibility, replay, or the CPROV-H
traversal algorithm.

## 2. Goals, non-goals, and scope boundary

### 2.1 Required goals

The project must provide:

1. a typed, source-located root origin for a body expression that imposes a type requirement,
   starting with `if` conditions;
2. an extensible body-requirement taxonomy that distinguishes source meaning without using file,
   module, definition, variable, or fixture names;
3. stable same-session generalized-scheme witness records that point to the exact canonical
   constraint/bound records incorporated into a finalized scheme position;
4. a typed scheme-instantiation derivation edge from each covered instantiated fact to its original
   generalized witness;
5. exact mapping through generalization simplification and polarized scheme cloning, rather than a
   guessed association by resolved constructor name;
6. bounded `why_constraint`, `why_lower_bound`, and `why_upper_bound` traversal through the new
   records without a second graph walker;
7. an additive `MissingImplicitCast` explanation that retains the existing call-site evidence and
   adds the callee body use site when it is available;
8. explicit completeness and cost metrics for body-origin coverage, generalized witnesses,
   instantiation edges, and the deeper queries;
9. proof that all new provenance remains observational metadata until the final diagnostic slice.

### 2.2 Explicit non-goals

This project does not include:

- serializing `ConstraintRecordId`, `BoundRecordId`, generalized-witness records, source boundaries,
  or derivation edges into `poly::Scheme`, compiled units, or caches;
- reconstructing an imported or cached callee's original proof graph;
- changing generalization, compacting, quantifier selection, simplification, role resolution, or
  instantiation semantics;
- changing which cast is selected or whether a cast diagnostic is emitted;
- changing CPROV-I's approved ordinary-cast eligibility semantics; category handling may be extended
  only as needed to keep `BodyRequirement` non-eligible and preserve the existing one-sided-boundary
  result;
- replacing the call-site explanation shipped in `e5b32137`;
- recovering a body location by rescanning CST after lowering;
- attaching source spans to semantic `Hash`, `Eq`, dedup, cache, or termination keys;
- materializing all paths between an instantiated scheme and every original body proof;
- selecting one use site by variable name, function name, constructor spelling, fixture path, or
  resolved output type alone;
- explaining every body-requirement category in the first slice;
- public editor navigation, interactive graph export, or cross-module provenance serialization.

### 2.3 Same-session boundary

**Decided:** the bridge is same-session only, matching base CPROV Section 2.3.

A scheme generalized from a definition whose original constraint records still live in the current
`AnalysisSession` may receive a `GeneralizedSchemeRecordId` and same-session instantiation edges.
Imported or cache-loaded schemes do not carry those records. Their instantiation continues through
the existing imported/unknown origin path and a deeper explanation degrades to "no body explanation
available."

The existing call-site explanation remains valid for imported and cached callees. Absence of a body
bridge must not suppress the primary diagnostic, remove its call-site related information, or cause
an unbounded attempt to reconstruct another session's graph.

### 2.4 Initial semantic surface

The first accepted body-requirement surface is an unannotated parameter constrained by an `if`
condition. Broader categories are designed into the taxonomy but are not acceptance requirements for
the first body-origin slice.

The first end-to-end witness is:

```text
unannotated parameter
    -> use as an if condition
    -> body-owned bool requirement
    -> generalized function argument position
    -> same-session scheme instantiation
    -> call-site MissingImplicitCast(int -> bool)
```

Explicitly annotated parameters remain explained by their annotation boundary. No body traversal is
required merely because a function body exists.

## 3. Current lifecycle and information-loss points

### 3.1 Parameter creation and body uses

`lower_defined_lambda_params_with_anchors` allocates a fresh parameter variable at
`crates/infer/src/lowering/expr/lambda.rs:637`. If an upper annotation is already available, it adds
that relation immediately at lines 638-644. An unannotated parameter has no such root relation at
declaration time.

The parameter is stored in a local binding. A use is lowered by `lower_local_name` at
`crates/infer/src/lowering/name_ref.rs:122-145`. The resulting `RefUse` records:

```text
parent DefId
value TypeVar
source_span
```

For a monomorphic local, `instantiate_local_value` returns the exact live `TypeVar` at
`crates/infer/src/lowering/expr/tail.rs:771-774`. For a generalized local, it clones the scheme and
roots the cloned predicate as `Internal` at lines 775-787.

The `RefUse` source span proves that lowering knows where the parameter is used. It is not sufficient
on its own: one parameter may have several uses, only some of which impose the relevant bound. The
span must be attached to the exact requirement root, not inferred later by matching a `TypeVar` to
all of its `RefUse` entries.

### 3.2 Body requirement creation

`lower_if_condition` lowers the condition, applies the synthetic junction, and calls
`constrain_exact_primitive(condition.value, "bool")` at
`crates/infer/src/lowering/control.rs:72-86`.

`constrain_exact_primitive` adds both a lower and an upper primitive constraint through
`constrain_lower` and `constrain_upper` at
`crates/infer/src/lowering/expr/constraints.rs:35-67`. Those helpers currently use
`OriginId::unknown_internal()`.

Two facts are therefore lost:

- semantic category: the requirement is specifically a boolean-condition requirement;
- source ownership: the exact condition expression span that caused it.

The synthetic junction and later replay/structural edges remain valid. The missing information is at
the root-entry seam, not in the later propagation rules.

### 3.3 Generalization

Local generalization drains pending semantic work, computes a compact generalized root, finalizes it
into the poly type arena, and stores the resulting `Scheme` at
`crates/infer/src/lowering/expr/tail.rs:790-850`.

`generalize_type_var_with_boundaries` begins from the live `ConstraintMachine` at
`crates/infer/src/generalize/mod.rs:70-80`. `finalize_generalized_compact_root` then turns the compact
root into `poly::Scheme` nodes at `crates/infer/src/generalize/finalize.rs:3-26`.

`poly::Scheme` contains quantifiers, role predicates, recursive bounds, stack quantifiers, and a
predicate (`crates/poly/src/types.rs:10-23`). It intentionally contains no same-session constraint or
bound record IDs. The semantic type shape survives; the exact canonical facts from which each
finalized position came do not.

Generalization also applies substitutions, simplification, pruning, and compact structural
conversion. A correct bridge cannot assume that the original parameter `TypeVar` survives as a
quantifier. In the representative case the parameter position may finalize directly as concrete
`bool`. Mapping only quantified source variables to fresh instantiation variables would therefore
miss the required proof.

### 3.4 Instantiation

The core scheme cloner is `SchemeInstantiator` in `crates/infer/src/instantiate.rs`. It already owns
source-to-target maps for positive, negative, and neutral type nodes and for variables while cloning
the predicate (`crates/infer/src/instantiate.rs:150-160` and `268-296`). Those maps are currently
discarded with the instantiator.

At the SCC/batch analysis entry, `prepare_instantiated_use` distinguishes imported from same-session
definitions at `crates/infer/src/analysis/session/instantiate.rs:370-375`. Imported instantiations are
rooted `UnknownInternal`; same-session instantiations are rooted `Internal`. The cloned predicate is
then either inserted through a direct-lower fast path or queued as a subtype at lines 435-443.

Local scheme instantiation follows a separate caller at
`crates/infer/src/lowering/expr/tail.rs:771-787`. Both paths use the same core structural cloner and
both must participate in the bridge. Covering only `prepare_instantiated_use` would not cover local
functions such as the representative witness.

### 3.5 Current query boundary

CPROV-H's `why_constraint`, `why_lower_bound`, and `why_upper_bound` traverse canonical constraint,
bound, origin, row, subtract-fact, lower-filter, and disposition records. They use depth-first
pre-order, append-only insertion ordering, a visited set, and hard node/edge/depth budgets.

When a query reaches the `Internal` root on a same-session instantiation, there is currently no
incoming edge to visit. The original definition's records remain alive but unreachable. This is a
graph connectivity gap, not a missing recursive traversal feature.

## 4. Required invariants

### 4.1 Semantic and provenance domains remain separate

The base CPROV invariant remains absolute:

> No body-requirement descriptor, source boundary, generalized witness, instantiation ID, source
> span, or scheme-instantiation derivation may participate in semantic `Hash`, `Eq`, canonicalization,
> queue admission, replay, generalization, instantiation, caching, or termination.

Semantic generalization and instantiation must produce the same `Scheme`, fresh type variables,
constraints, bounds, epochs, and diagnostics before the final presentation slice. A missing or
budget-dropped provenance edge never changes the copied type.

### 4.2 Body ownership is attached at requirement creation

A body-use span is valid evidence only when lowering attaches it to the root constraint that imposes
the requirement. Matching a resolved type, a parameter variable, a reference name, or the nearest
CST node after inference is forbidden.

Both directions emitted by one exact invariant requirement may share one source boundary and one
semantic descriptor. That expresses one source requirement without pretending that the two
constraint records are semantically identical.

### 4.3 Generalization witnesses preserve exact contributors

A finalized generalized position records the exact canonical parent records that contributed to
that position. It does not record only the final constructor path and does not flatten all origins
reachable from the definition.

If one compact transformation genuinely consumes several facts, it may use an ordered multi-parent
hyperedge under the base CPROV rule. If several alternate facts independently explain the same
generalized position, they remain separate deduplicated incoming edges. The implementation must not
form every combination of their transitive proof paths.

### 4.4 Instantiation edges are true graph edges

Each covered same-session instantiated fact receives a typed incoming edge to the corresponding
generalized witness. The edge is stored on a canonical constraint or bound record and is returned by
the normal CPROV-H query surface.

A session-local `DefId -> GeneralizedSchemeRecordId` association may locate the source record during
instantiation. It is not itself an explanation and must never be queried by the diagnostic renderer.
Deleting diagnostic integration must leave the generalized and instantiated graph fully queryable.

### 4.5 Append-only identity survives pruning and repeated use

Original body bound records remain valid even after generalization, later subsumption, or active
frontier pruning. Generalized witnesses and instantiation edges refer to those stable records, not to
indexes in a mutable active-bound vector.

Repeated calls to a generic function allocate distinct instantiation records but share the same
immutable generalized witnesses. Reprocessing the same use request merges the identical provenance
edge and does not allocate another semantic fact or another proof-path copy.

### 4.6 No proof-path enumeration

The CPROV-G combinatorial-blowup incident is a standing negative requirement. That bug cached
`Vec<Vec<Parent>>` combinations of proof paths instead of canonical graph edges. This project must
not recreate that shape during generalization or instantiation.

Allowed storage is:

- one canonical generalized-scheme record per same-session finalized scheme version;
- one canonical generalized witness per typed structural position and witness role;
- a deduplicated set of incoming edges over exact canonical parents;
- one canonical instantiation record per same-session use request;
- one deduplicated scheme-instantiation edge per exact target/witness mapping.

Forbidden storage is:

- every path from a scheme position to a body origin;
- a nested vector of alternative parent paths;
- a Cartesian product of witness derivations across cloned nodes;
- copying the full body graph into each instantiation;
- flattening all definition origins into every instantiated parameter.

### 4.7 Query traversal remains bounded and cycle-safe

Generalized and instantiated records may connect graph regions that were previously disconnected.
They can reveal cycles between recursive schemes, definition bodies, and use sites. Queries must
continue to treat the projection as a graph.

CPROV-H's visited-set, node budget, edge budget, depth budget, deterministic ordering, and
completeness states remain mandatory. No new recursive formatter or unbounded scheme walker may sit
beside it.

### 4.8 Diagnostic degradation is additive and honest

The existing `e5b32137` call-site explanation remains the floor:

- if the body bridge is complete, append a body-use related site;
- if the callee is annotated, imported, cached, budget-truncated, uncovered, or otherwise lacks a
  clean body witness, retain the call-site explanation unchanged;
- never fabricate a body span;
- never suppress or alter the primary `MissingImplicitCast` diagnostic because deeper explanation
  is unavailable.

## 5. Decided provenance model

### 5.1 Body-requirement origin taxonomy

**Decided:** body requirements use a new structured `ConstraintOriginKind` family, not
`Internal`, `UnknownInternal`, or a collection of unrelated top-level variants.

The intended shape is:

```rust
enum ConstraintOriginKind {
    ApplicationArgument,
    Annotation,
    Return,
    Field,
    Assignment,
    BodyRequirement(BodyRequirementKind),
    Internal,
    UnknownInternal,
}

enum BodyRequirementKind {
    BooleanCondition,
    OperatorOperand { operand: StructuralIndex },
    PatternGuard,
    CalleeArgument { argument: StructuralIndex },
}
```

Only `BooleanCondition` is required to be wired by the first body-origin slice. The remaining
variants describe the intended extension axis; each must be characterized before production wiring.
If an internal call already has an exact `ApplicationArgument` boundary that owns the same relation,
later work should reuse that boundary rather than record a redundant `CalleeArgument`. The exact
reuse rule remains an open taxonomy detail in Section 13.

`BodyRequirement` has two important properties:

1. it is source-owned and may carry a `SourceBoundaryId`, so explanation queries can report it as a
   located source leaf;
2. it is not an eligible ordinary-cast boundary. CPROV-I must not interpret a boolean condition or
   operator operand as a cast request merely because it comes from source syntax.

The code should separate "has source ownership" from "eligible OCAST boundary." The current
`ConstraintOriginKind::is_source` helper and CPROV-I's `is_eligible_source_kind` must not be treated as
the same predicate when this category is added.

### 5.2 Body-requirement source locations

Spans remain outside semantic graph identity, following base CPROV Section 5.2 and the
`SourceBoundaryProvenanceTable` introduced by `e5b32137`.

The source-only table gains a body-requirement entry such as:

```rust
struct BodyRequirementBoundaryProvenance {
    use_span: SourceSpan,
    context_span: Option<SourceSpan>,
}
```

`use_span` is the exact expression whose value is constrained. For the first slice it points to the
condition expression passed to `lower_if_condition`. `context_span` may point to a larger construct
when lowering already owns that range; it is optional and must not be reconstructed later.

The semantic category lives in `ConstraintOriginKind::BodyRequirement(BodyRequirementKind)`. The
table carries source location only. This avoids duplicating category state between the graph and the
source table.

### 5.3 Generalized-scheme graph records

The graph gains stable session-local generalized-scheme identities. Exact Rust names may be refined,
but the model is decided:

```rust
struct GeneralizedSchemeRecordId(u32);
struct GeneralizedSchemeWitnessId(u32);

struct GeneralizedSchemeRecord {
    owner: DefId,
    generation: u32,
    witnesses: Vec<GeneralizedSchemeWitnessId>,
    completeness: ProvenanceCompleteness,
}

struct GeneralizedSchemeWitness {
    scheme: GeneralizedSchemeRecordId,
    path: GeneralizedTypePath,
    role: GeneralizedWitnessRole,
    incoming: Vec<GeneralizationDerivation>,
}
```

`generation` distinguishes successively finalized scheme values for one definition without placing
provenance in `poly::Scheme`. A session-local association records which generalized record belongs to
the currently installed same-session scheme.

`GeneralizedTypePath` is a typed structural address from the finalized scheme predicate or recursive
bound to one polarized position. It uses structural steps such as function argument, function
return, constructor argument, tuple element, record field, variant payload, or row item. It must not
contain source text, display strings, or target-arena node IDs as its stable identity.

`GeneralizedWitnessRole` distinguishes the semantic fact represented at a path, at least:

```text
constraint relation
lower bound
upper bound
recursive lower bound
recursive upper bound
```

Each `GeneralizationDerivation` points to exact existing graph parents: canonical constraints,
canonical bounds, or another typed generalization transformation record. Alternate derivations are
separate edges. A genuinely joint compact transformation uses one ordered hyperedge.

These records are first-class graph records. They are not serialized in `poly::Scheme`, compared as
part of scheme equality, or exposed to `crates/yulang`.

### 5.4 Capturing provenance through compact generalization

Generalization must build the semantic compact root and a provenance projection together. The
projection tracks which canonical input records contribute to each compact position through:

- bound collection;
- polarity and function-position projection;
- variable substitution;
- sandwich simplification;
- recursive-bound extraction;
- dead-quantifier and unreachable-position pruning;
- final clone into the poly type arena.

The projection does not influence any of those decisions. It observes the already-chosen semantic
transformation and updates typed witness addresses accordingly.

If one semantic transformation cannot map an output position to exact inputs, that witness and its
scheme record become `Incomplete`. The implementation must not guess from equal rendered types or
attach every bound of the definition as a fallback.

The representative function-argument witness must ultimately point to the original parameter's
canonical upper-bound record whose normal CPROV derivation reaches the boolean-condition origin.

### 5.5 Scheme-instantiation records and edges

The graph gains stable instantiation identities and a typed derivation:

```rust
struct SchemeInstantiationId(u32);

struct SchemeInstantiationRecord {
    source: GeneralizedSchemeRecordId,
    owner: DefId,
    target: DefId,
    use_value: TypeVar,
    completeness: ProvenanceCompleteness,
}

struct SchemeInstantiationDerivation {
    instantiation: SchemeInstantiationId,
    source_witness: GeneralizedSchemeWitnessId,
    path: GeneralizedTypePath,
}
```

`owner`, `target`, and `use_value` identify a same-session use request for provenance dedup. They do
not enter semantic constraint identity. If a caller lacks one of these exact concepts, it allocates
an equivalent stable per-use key at its existing instantiation seam; it must not use a source string
or span as the dedup key.

The derivation is stored as an incoming edge on the canonical fact that realizes the cloned scheme
position:

- subtype instantiation attaches it to a `ConstraintRecord`;
- the direct-lower fast path attaches it to the resulting `BoundRecord`;
- subsequent ordinary bound insertion continues to point to the constraint through the existing
  `BoundDerivation::Constraint` edge;
- if an instantiated structural child is the first precise realization of a scheme path, provenance
  propagation attaches the scheme edge to that child rather than flattening all root witnesses onto
  the whole predicate.

`ConstraintRecord` therefore gains a deduplicated scheme-instantiation derivation collection, and
`BoundDerivation` gains a scheme-instantiation form for direct insertion. CPROV-H gains the
corresponding explanation edge kind and generalized-witness node kind.

### 5.6 Structural-path propagation during instantiation

The core `SchemeInstantiator` already maps source positive/negative/neutral nodes and quantified
variables to target nodes while cloning. Same-session instantiation extends its return value with a
provenance-only mapping from cloned target nodes to generalized witness paths.

The semantic `InstantiatedScheme` fields remain unchanged. The provenance mapping is adjacent
session-local output and is absent for imported instantiation.

When the instantiated predicate is admitted, the root canonical record receives an instantiation
record. As `step_subtype` performs its existing typed structural decomposition, the provenance layer
advances the `GeneralizedTypePath` by the same already-chosen
`StructuralDerivationRule`. The exact child canonical record then receives the mapping edge for that
path.

This is provenance-only propagation:

- it never changes whether the child is generated;
- it never creates a semantic child that did not already exist;
- it never changes weights, polarity, order, or replay;
- merging the edge into an existing child bumps only `ProvenanceEpoch`;
- inability to advance a mapping marks that branch incomplete without altering semantic work.

### 5.7 Edge identity and scaling

One `SchemeInstantiationId` is allocated per unique same-session use request. Multiple mapped facts
inside that use share the record. The incoming edge dedup key is:

```text
(target record kind,
 target record ID,
 instantiation ID,
 generalized witness ID,
 typed structural path)
```

The generalized witness's own incoming derivation key is:

```text
(generalized scheme record,
 witness role,
 typed structural path,
 rule,
 ordered exact parent record IDs)
```

Calling one generic function at `N` distinct use sites therefore allocates `N` small instantiation
records and at most the mapped canonical edges actually realized at those sites. All calls share the
definition's generalized witnesses and the body graph beneath them. Growth is linear in realized
instantiation mappings, not in the number of transitive proof paths.

If the same use is prepared twice by fixed-point scheduling, its stable use key resolves to the same
instantiation record and exact edge dedup suppresses repeats. If two use sites happen to produce the
same semantic constraint record, both instantiation edges may coexist on that canonical result; this
is provenance progress only and does not requeue the result.

### 5.8 Imported and cache-loaded schemes

Imported and cache-loaded schemes have no `GeneralizedSchemeRecordId` in the receiving session. They
do not receive a fabricated instantiation edge. Existing imported validation and
`UnknownInternal` rooting remain unchanged.

The body-explanation consumer interprets this absence as unavailable or incomplete deeper
provenance and retains the existing call-site explanation. This project does not add record IDs to
serialized `Scheme`, compiled boundaries, cache artifacts, or imported-boundary substitutions.

## 6. Layer 1: body-requirement source ownership

### 6.1 Touchpoint: `lower_if_condition`

**Current state.** `lower_if_condition` receives the condition CST, lowers it, applies the synthetic
junction, and constrains the result to exact `bool` at
`crates/infer/src/lowering/control.rs:72-86`. The CST and source range are available there.

**Required change.** Allocate one source boundary before creating the exact primitive constraints:

```text
BodyRequirement(BooleanCondition, condition use span)
```

Add an origin-aware exact-primitive helper and pass the same `OriginId` to the lower and upper
primitive roots. Register the condition's `SourceSpan` in `SourceBoundaryProvenanceTable` while the
CST is available.

**Semantic isolation.** The helper allocates the same `Pos`, `Neg`, weights, and constraints as
today. Origin and span are additive metadata. Neither exactness nor the synthetic junction changes.

### 6.2 Touchpoint: generic constraint helpers

**Current state.** `constrain_lower`, `constrain_upper`, and `constrain_exact_primitive` use
`UnknownInternal` at `crates/infer/src/lowering/expr/constraints.rs:35-67`.

**Required change.** Add narrowly named origin-aware variants. Existing callers continue using their
current origins until characterized. Do not blanket-tag all primitive constraints as body
requirements.

**Semantic isolation.** The origin-aware overload must delegate to the same semantic entry points.
It must not branch on primitive name or CST text.

### 6.3 Touchpoint: source-boundary provenance table

**Current state.** The table introduced by `e5b32137` stores application, callee, and argument spans
for `ApplicationArgument` boundaries. It is explicitly outside semantic equality and graph
traversal.

**Required change.** Add a typed body-requirement location entry keyed by `SourceBoundaryId`.
Retrieval returns location only after the graph has already produced a body-requirement boundary.
The table must not answer "which requirement applies to this type variable?"

**Semantic isolation.** Inserting or missing location metadata cannot change constraint creation,
classification, or diagnostic existence. Missing metadata degrades to no body related-information.

### 6.4 OCAST compatibility

**Current state.** CPROV-I separately recognizes eligible source kinds. The live CPROV-J activation
emits diagnostics only for those eligible boundaries.

**Required change.** Treat `BodyRequirement` as complete, source-owned, non-OCAST evidence. It may be
returned by explanation queries, but it must not become an eligible cast boundary.

The classifier's eligible-boundary set, unrelated-boundary comparison, and one-sided replay test
must continue to reason only over OCAST-eligible boundary kinds. A body requirement reached beneath
the callee side does not become a second competing cast boundary and does not disqualify the
existing `ApplicationArgument + confidently non-cast ancestry` case. The existing `Internal` root
remains alternate ancestry; the new body leaf explains that ancestry rather than changing ownership
of the call relation.

**Semantic isolation.** The two known false-positive repros and the complete CPROV characterization
corpus must retain their classifier and diagnostic results. Layer 1 does not authorize any OCAST
eligibility refinement.

### 6.5 Extension categories

Later source-root slices may characterize:

- boolean and pattern guards;
- operator operands constrained to an intrinsic or declared operand type;
- a parameter passed to another typed callee inside the body;
- destructuring and pattern positions that impose constructor/payload requirements;
- explicit body annotations not already represented by the existing `Annotation` origin.

Each category must attach ownership at its actual requirement-creation seam. The taxonomy must not
be expanded merely because a syntax node is easy to locate.

## 7. Layer 2: generalization/instantiation provenance bridge

### 7.1 Touchpoint: generalization input capture

**Current state.** Generalization reads the live machine, compacts a root, simplifies it, and emits a
`GeneralizedCompactRoot`. The compact structures retain semantic type information but no canonical
constraint/bound parent identities.

**Required change.** Build a provenance projection beside compacting. Whenever compacting reads a
canonical lower/upper bound or constraint to populate a compact position, record the exact parent
record under the corresponding typed path and witness role.

**Semantic isolation.** Provenance capture observes bound iteration and semantic choices after they
are made. It must not reorder active bounds, keep an otherwise-pruned variable alive, alter
substitutions, or force a different compact representation.

### 7.2 Touchpoint: simplification and finalization

**Current state.** `GeneralizedCompactRoot` carries substitutions and sandwiches, and finalization
clones the compact result into the poly type arena. Provenance is discarded.

**Required change.** Apply every already-selected structural rewrite to typed witness paths and
incoming derivation edges. When several source positions coalesce, preserve alternate edges unless
the semantic operation genuinely consumes them jointly. After finalization, allocate one
`GeneralizedSchemeRecord` and its canonical witnesses.

**Semantic isolation.** The provenance projection cannot veto, modify, or repeat simplification. A
mapping failure marks only provenance incomplete.

### 7.3 Touchpoint: scheme ownership

**Current state.** A finalized `Scheme` is stored on `Def::Let` and may also be held on local-binding
state. `poly::Scheme` is serializable and used by caches/imports.

**Required change.** Store the same-session `GeneralizedSchemeRecordId` in an analysis/lowering-owned
session index keyed by the installed definition and exact scheme generation. If local-binding state
needs the ID to call the core instantiator, it carries the opaque ID beside the scheme, not inside
the scheme.

**Semantic isolation.** Scheme cloning, serialization, equality, and cache keys remain unchanged.
Dropping the session index yields today's compiler behavior plus no deep explanation.

### 7.4 Touchpoint: core `SchemeInstantiator`

**Current state.** `SchemeInstantiator` builds fresh variable and type-node maps internally and
returns semantic predicate/role data. The maps are dropped afterward.

**Required change.** For a same-session scheme record, project its typed generalized witnesses
through those existing clone maps and return an adjacent `InstantiatedSchemeProvenance` value. Do not
re-walk the cloned type tree after the maps have been discarded.

**Semantic isolation.** The semantic `InstantiatedScheme` output is byte-for-byte equivalent. The
provenance return is optional and ignored by imported callers.

### 7.5 Touchpoint: SCC/batch instantiation

**Current state.** `prepare_instantiated_use` chooses `UnknownInternal` for imported schemes and
`Internal` for same-session schemes, then routes the cloned predicate through either direct lower
insertion or a subtype root (`crates/infer/src/analysis/session/instantiate.rs:370-443`).

**Required change.** For same-session inputs, resolve the source generalized-scheme record, intern a
stable instantiation record, and attach its projected mappings to the exact canonical constraint or
bound results. Imported inputs retain the current unknown root and no bridge.

**Semantic isolation.** The current `Internal` root remains as an alternate incoming origin; this
project does not delete or rewrite append-only history. Direct-lower selection and batch order remain
unchanged.

### 7.6 Touchpoint: local instantiation

**Current state.** `instantiate_local_value` clones a local `Scheme` and adds an `Internal` subtype
root at `crates/infer/src/lowering/expr/tail.rs:771-787`.

**Required change.** Carry the local definition's generalized record beside the scheme, allocate a
same-session instantiation record for the fresh use value, and attach the same mapping form used by
the batch path.

**Semantic isolation.** Monomorphic locals continue returning their live value directly and need no
scheme bridge. Generalized locals allocate the same fresh semantic variables and constraint as
today.

### 7.7 Touchpoint: structural propagation and direct bounds

**Current state.** Structural children receive typed unary edges from their parent constraint;
direct-lower instantiation may bypass a root constraint and insert a bound directly.

**Required change.** Propagate only the mapping whose typed scheme path matches the already-produced
structural child. Add a `SchemeInstantiation` incoming edge to that child. For direct lower
insertion, add the same edge through `BoundDerivation`.

**Semantic isolation.** A scheme edge added to an already-canonical result is a provenance-only
merge. It bumps no semantic epoch, emits no event, performs no replay, and queues no work.

### 7.8 Touchpoint: explanation graph

**Current state.** CPROV-H has no generalized-scheme node or scheme-instantiation edge kind.

**Required change.** Extend `ExplanationNodeId`, `ExplanationNode`, and `ExplanationEdgeKind` with
generalized-witness and scheme-instantiation cases. Their parents are exact canonical records, and
their iteration order is append-only deterministic order.

**Semantic isolation.** Querying remains read-only. Traversal does not populate missing mappings,
advance epochs, or mutate inference state.

## 8. Query and consumer implications

### 8.1 Expected query chain

After both layers are present, the representative query can traverse:

```text
call-side nominal mismatch constraint
    -> exact replay/structural parent for the callee argument
    -> instantiated scheme constraint or bound
    -> SchemeInstantiation(instantiation, function-argument path)
    -> GeneralizedSchemeWitness(function-argument upper requirement)
    -> original parameter upper BoundRecord
    -> existing constraint/replay/structural derivations
    -> BodyRequirement(BooleanCondition) origin
    -> SourceBoundaryId
    -> condition use_span in SourceBoundaryProvenanceTable
```

The edge chain identifies the original bound before the diagnostic layer reads the span. The source
table never performs graph matching.

### 8.2 Existing CPROV-H API remains the entry point

**Decided:** the signatures and traversal algorithm of `why_constraint`, `why_lower_bound`, and
`why_upper_bound` remain the query entry point. No new unbounded `why_parameter` walker is added.

The implementation extends the closed node/edge enums and their incoming-edge visitors. The same
visited set, depth-first deterministic ordering, node limit, edge limit, depth limit, and
completeness calculation apply.

The deeper graph may consume more budget than current explanations. Existing defaults are not
assumed sufficient merely because the algorithm is safe. PUSP-A and PUSP-E must measure depth and
fan-out and report truncation on real same-session cases before diagnostic integration.

### 8.3 Choosing the relevant body witness

A diagnostic consumer must project from the already-bounded explanation result. It must select a
body witness connected by the exact scheme path that produced the mismatching callee parameter. It
must not choose an arbitrary `BodyRequirement` leaf elsewhere in the function.

The production consumer should extend CPROV-I's existing single bounded classification projection
to retain this body witness. It must not run a second full graph query for every emitted diagnostic.
PUSP-E may invoke the query API directly in focused tests, but PUSP-F reuses the quiescent query
result just as `e5b32137` reuses `EligibleBoundaryEvidence` today.

If the path reaches several alternate body requirements, the structured diagnostic payload retains
their deterministic order and completeness. Whether the initial renderer displays all of them or
one representative is an open presentation decision; the graph stores the exact alternate edges.

### 8.4 Presentation-neutral projection

Internal IDs remain inside `infer`. The final diagnostic projection may extend the existing
presentation-neutral types with a role such as:

```text
RequiredByBodyUse(BodyRequirementDiagnosticKind)
```

and a `SourceSpan`. It must not expose `ConstraintRecordId`, `BoundRecordId`, `TypeVar`,
`GeneralizedSchemeRecordId`, `GeneralizedSchemeWitnessId`, or `SchemeInstantiationId` to
`crates/yulang`.

The existing call-site related entries from `e5b32137` remain first. Body-use information is an
additional related entry, not a replacement for the argument or callee location.

## 9. Performance, storage, and completeness policy

### 9.1 Required measurements

PUSP-A establishes a baseline and later slices report at least:

- body-requirement origins allocated by kind;
- body requirement roots lacking location metadata;
- generalized scheme records and witnesses;
- generalized witnesses by role and structural depth;
- incoming generalization edges considered, inserted, and deduplicated;
- same-session instantiations by local and batch path;
- imported/cache instantiations without a bridge;
- scheme-instantiation edges considered, inserted, and deduplicated;
- maximum mapped witnesses per scheme and per instantiation;
- maximum incoming scheme edges per canonical constraint/bound record;
- logical-byte proxy for generalized witnesses, instantiation records, and edge indexes;
- deeper query nodes, edges, maximum depth, elapsed time, and truncation count;
- semantic constraint, bound, replay, event, scheme fingerprint, and diagnostic parity through inert
  slices.

### 9.2 Storage shape

Generalized witnesses are shared across all instantiations of a scheme. Instantiation records store
small IDs and typed path references, not copies of original explanation subgraphs. An exact parent
record may be referenced by many generalized witnesses or instantiations without cloning its
incoming derivations.

The implementation should use arena-backed records and exact hash/index keys consistent with base
CPROV. A large `Vec<Vec<...>>`, recursive owned tree, or per-query reverse index is a design failure,
not an optimization opportunity.

### 9.3 Budget exhaustion

The base CPROV replay storage budget remains unchanged. A separate storage budget for generalized
witness and instantiation edges is not fixed in this document; it is chosen from PUSP-A/C/D
measurements under Section 13.

Any approved limit must:

- stop only new provenance retention;
- mark the affected witness, instantiation, and query `Incomplete`;
- preserve semantic generalization/instantiation and all diagnostics;
- retain already-recorded edges;
- expose budget counters;
- never collapse exact edges into an origin union.

### 9.4 Query cost

The existing CPROV-H default budget and the larger OCAST classifier budget provide starting
measurements, not an automatic public-diagnostic budget decision. The diagnostic integration slice
must use an explicit bounded budget and record whether the body extension truncated.

If the body path is unavailable within budget, rendering falls back to the existing call-site-only
explanation. It does not retry with unrestricted traversal.

## 10. Implementation stages and slices

All Rust changes are deferred to follow-up tasks. The slices follow the CPROV pattern: characterize,
add inert source ownership, add inert generalized identity, bridge instantiation, prove the query,
then integrate presentation separately.

### Slice PUSP-A: parameter/scheme provenance characterization

Size: S-M. Risk: low.

Characterize the representative unannotated-parameter case and a compact comparison corpus before
adding records. Record:

- the original parameter variable and relevant canonical upper/lower bound IDs;
- the existing body-to-`bool` explanation topology and its terminal origin kind;
- the call-side explanation topology and exact point where same-session instantiation stops;
- local versus SCC/batch instantiation entry counts;
- scheme shapes in which the relevant parameter remains a variable versus finalizes concrete;
- current query nodes, edges, depth, completeness, and timing;
- semantic counts, scheme fingerprints, OCAST classifications, diagnostics, and output.

Include at least:

- `f(x) = if x { 1 } else { 2 }; f(42)`;
- an explicitly annotated parameter control;
- one generic function instantiated more than once;
- one imported/cache-loaded callee control;
- one function whose parameter has multiple body uses.

Exit witness: checked-in tests or reports demonstrate that a direct query on the original parameter
reaches the body `bool` root without a location, while the call-side query stops at same-session
`Internal`; all compiler behavior is unchanged.

### Slice PUSP-B: body-requirement origins and locations

Size: M. Risk: medium.

Add `ConstraintOriginKind::BodyRequirement(BodyRequirementKind)` and the body-requirement location
entry. Wire `BooleanCondition` at `lower_if_condition` through a narrow origin-aware exact-primitive
helper. Update provenance coverage metrics and OCAST's source-owned/non-eligible distinction.

Do not add scheme records or diagnostic rendering.

Exit witness: querying the original parameter bound reaches a
`BodyRequirement(BooleanCondition)` leaf whose boundary resolves to the exact condition expression
span; the same lower/upper primitive constraints, semantic epochs, scheme, OCAST classification,
diagnostics, and output remain unchanged; missing location metadata remains harmless.

### Slice PUSP-C: generalized-scheme witness capture

Size: L. Risk: high.

Introduce generalized-scheme and generalized-witness graph records. Carry exact parent record
identity through compact collection, substitutions, sandwiches, pruning, recursive-bound extraction,
and finalization. Store a same-session opaque association beside installed schemes. Add metrics and
debug inspection, but do not attach any instantiation edge yet.

Stop if exact output-to-parent mapping cannot be preserved through one semantic generalization
transformation. Do not replace missing fidelity with a whole-definition origin set.

Exit witness: the representative finalized function-argument witness points to the exact original
parameter upper bound; concrete-finalized and quantified parameter shapes are both characterized;
duplicate contributors remain deduplicated graph edges; semantic schemes and all compiler behavior
are byte-identical to PUSP-A.

### Slice PUSP-D: same-session scheme-instantiation bridge

Size: L-XL. Risk: very high.

Add `SchemeInstantiationId`, core-cloner provenance mappings, path-specific instantiation edges, and
direct-bound support. Cover both local instantiation and SCC/batch instantiation. Imported/cache
instantiation remains unbridged and explicit. Extend CPROV-H's node/edge enums and visitors without
changing its traversal algorithm.

This slice remains inert with respect to diagnostics. Establish and enforce the measured storage
budget before closeout.

Exit witness: a query beginning on the call-side instantiated parameter fact traverses a
`SchemeInstantiation` edge to the original parameter bound; repeated generic calls share generalized
witnesses, allocate one instantiation record per use, and do not enumerate proof paths; semantic
constraints, bounds, replay, epochs, schemes, caches, diagnostics, and output remain unchanged.

### Slice PUSP-E: bounded end-to-end query verification

Size: M. Risk: high.

Build a read-only projection that identifies body requirements connected to the exact mismatching
callee parameter path. Reuse `why_constraint`/`why_lower_bound`/`why_upper_bound`; do not add another
walker. Characterize deterministic ordering, cycles, alternate body uses, budget truncation, and
incomplete imported provenance.

No public diagnostic content changes in this slice.

Exit witness: the representative call-side query reaches the exact `if x` span and semantic
`BooleanCondition` category; an unrelated body requirement is not selected; repeated runs are
identical; a forced small budget returns truncated/incomplete metadata promptly; imported/cache
callees return no body witness without losing their call-site evidence.

### Slice PUSP-F: additive `MissingImplicitCast` integration

Size: M. Risk: high.

Extend the presentation-neutral diagnostic explanation produced by `e5b32137` with body-use related
sites projected from the already-bounded query. Preserve the primary diagnostic, argument site,
callee site, eligibility decision, and cast cardinality. Add user-facing related information in
`crates/yulang/src/source/mod.rs` only after the structured infer-side tests pass.

Exit witness: for the representative unannotated function, the diagnostic retains its existing
call-site message and related sites and additionally identifies the condition use with wording
equivalent to "this parameter is required to be `bool` because it is used as this condition";
explicitly annotated, imported, cached, truncated, and uncovered cases retain today's call-site-only
explanation; false-positive repros still emit no cast diagnostics; infer, specialize, yulang library,
CLI, contract, cache, and performance gates pass.

## 11. Slice dependencies and gates

The required order is:

```text
PUSP-A characterization
    -> PUSP-B body-requirement ownership
    -> PUSP-C generalized-scheme witnesses
    -> PUSP-D same-session instantiation bridge
    -> PUSP-E bounded query proof
    -> PUSP-F additive diagnostic integration
```

The ordering encodes these dependencies:

- a scheme witness cannot identify a useful body cause until the body root is typed and located;
- an instantiation edge cannot precede stable generalized witnesses;
- diagnostic integration cannot precede bounded end-to-end query evidence;
- imported/cached behavior must be tested before presentation activation;
- no slice may bundle semantic compiler changes with provenance recording.

Before PUSP-D closes:

- generalized witness mapping is exact for concrete and quantified parameter shapes;
- both local and SCC/batch same-session instantiation paths are covered;
- duplicate fixed-point preparation merges the same edge;
- no graph field enters scheme or semantic equality;
- storage growth is measured on std plus representative multi-instantiation cases;
- the CPROV-G no-path-enumeration safeguard has a focused regression test.

Before PUSP-F begins:

- the end-to-end query reaches the exact body requirement by structural path, not name or rendered
  type;
- truncation and unavailable imported provenance degrade deterministically;
- multiple body-use behavior has an approved presentation policy;
- query and storage budgets are approved;
- all inert slices preserve semantic characterization counts and diagnostic existence.

## 12. Compatibility, rollback, and failure policy

PUSP-A through PUSP-E are observational/inert with respect to source-language semantics and public
diagnostic content. They may add records, indexes, metrics, test-only views, and query-visible edges.
They must preserve inferred types, generalized schemes, instantiated predicates, solver work,
diagnostics, emitted programs, runtime behavior, caching, and termination.

If an inert slice changes semantic output:

1. compare semantic constraint/bound cardinality, replay counts, epochs, generalized scheme dumps,
   instantiation shapes, and event counts with PUSP-A;
2. verify that a body kind, scheme ID, witness path, instantiation ID, or source span did not enter a
   semantic key or branch;
3. verify that a duplicate provenance merge did not enqueue a constraint, replay a bound, or retain
   a variable semantically;
4. roll back the slice while retaining characterization evidence;
5. do not update semantic expectations to accept the change.

If storage or query cost exceeds the approved limit:

1. preserve semantic generalization and instantiation first;
2. determine whether growth comes from witness capture, repeated instantiations, duplicate mappings,
   or query traversal;
3. verify exact edge dedup before considering a lower budget;
4. mark dropped provenance incomplete under an explicit policy;
5. never flatten origins or materialize proof paths as a shortcut.

PUSP-F changes only additive diagnostic related-information. Its rollback removes body-use
projection and rendering while retaining body roots, generalized witnesses, instantiation edges, and
debug queries. The `e5b32137` call-site explanation remains intact.

## 13. Open decisions

The following are decided and must not be reopened as incidental implementation choices:

- true graph edges instead of a diagnostic-only parameter table;
- a structured `BodyRequirement(BodyRequirementKind)` origin family;
- `BooleanCondition` as the first wired body requirement;
- exact generalized contributors rather than a whole-definition origin union;
- one shared generalized witness graph plus per-use instantiation records;
- same-session-only bridging;
- unchanged semantic keys and unchanged CPROV-H traversal machinery;
- additive diagnostic degradation to the existing call-site explanation.

The following points remain open for the named slices:

1. **Broader body taxonomy (PUSP-B and later).** Confirm which operator, guard, destructuring, and
   internal-callee requirements need distinct `BodyRequirementKind` variants. In particular, decide
   when an existing `ApplicationArgument` boundary already owns an internal callee requirement and
   must be reused instead of adding `CalleeArgument`.
2. **Typed path encoding (PUSP-C).** Choose the compact Rust representation of
   `GeneralizedTypePath` and `GeneralizedWitnessRole`. The semantic requirement—polarized,
   structural, stable across arena cloning, and free of source strings—is decided.
3. **Generalization transformation vocabulary (PUSP-C).** Determine which compact substitutions,
   sandwiches, joins, and recursive-bound moves require distinct typed derivation rules for an
   honest explanation. Missing categories must mark provenance incomplete.
4. **Instantiation-edge storage budget (PUSP-D).** Set session, per-scheme, per-instantiation, and
   per-canonical-record limits from measurements. Limits must preserve semantics and report
   incompleteness.
5. **Extended query budget (PUSP-E).** Decide whether the existing 512-node/1,024-edge/depth-32
   default is sufficient for diagnostic body paths or whether the diagnostic projection needs a
   separately named bounded budget.
6. **Multiple constraining body uses (PUSP-E/F).** Decide whether the first diagnostic shows all
   deterministic body witnesses within budget, the cheapest/first stable witness plus a count, or
   one representative. Storage continues to retain all exact incoming edges regardless of the
   presentation choice.
7. **Body related-information wording (PUSP-F).** Choose final CLI/LSP text and whether optional
   context spans add a second related item. The primary `MissingImplicitCast` wording and existing
   call-site related entries do not change.
8. **Coverage beyond ordinary value parameters.** Decide in later projects whether role predicates,
   effect parameters, recursive scheme bounds, method receivers, and associated types use the same
   bridge for public explanation. PUSP-C/D must not silently claim complete coverage for these
   categories unless characterized.

The following are deferred by scope, not open implementation choices:

9. **Cross-session proof serialization.** Imported and compiled schemes do not carry their original
   graph in this project.
10. **Interactive/public graph UX.** Graph browsers, editor commands, and arbitrary "why this type"
    requests are separate presentation projects.
11. **Truth maintenance or retraction.** Scheme provenance remains append-only explanation data; it
    does not make deleting an origin or undoing a generalized consequence sound.

## 14. Overall project exit criteria

The parameter-use-site provenance project is complete only when:

- boolean-condition requirements have a typed, source-located root origin allocated at lowering;
- body source spans remain outside semantic graph and scheme identity;
- the representative original parameter bound reaches the exact boolean-condition leaf;
- same-session generalized schemes have stable graph witness records with exact canonical parents;
- concrete-finalized and quantified parameter positions both retain honest witnesses;
- local and SCC/batch same-session instantiations add typed edges to those witnesses;
- imported/cache-loaded schemes remain explicitly unbridged and degrade without fabrication;
- repeated generic instantiations share generalized witnesses and grow linearly in exact mappings;
- no nested proof-path combinations, origin flattening, or copied body subgraphs are stored;
- duplicate scheme edges produce provenance progress only;
- CPROV-H queries traverse the bridge deterministically, cycle-safely, and within approved budgets;
- budget exhaustion and mapping gaps return incomplete provenance rather than a guessed body site;
- the call-side unannotated-parameter query reaches the exact body use that imposed the target type;
- unrelated body requirements are not selected by name, constructor text, or whole-definition
  ancestry;
- `MissingImplicitCast` retains the `e5b32137` call-site explanation and adds body-use detail only
  when complete evidence and location are available;
- annotated, imported, cached, truncated, and uncovered cases retain the existing explanation
  unchanged;
- OCAST eligibility, cast cardinality, false-positive suppression, solver semantics, generalized
  schemes, cache behavior, and runtime output remain unchanged;
- characterization, infer, specialize, yulang library, CLI, contract, cache, and performance gates
  pass under the approved storage/query policies.

Completion of the graph bridge does not claim cross-session provenance. Completion of the
diagnostic slice does not replace the call-site explanation or authorize unbounded public graph
queries. Each implementation slice requires separate authorization and review.

Investigation and specification design: Codex (gpt-5.6-sol), 2026-07-22 session. Whether and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a feasibility and design specification, not an implementation commitment.

Reference specification approved by Claude Sonnet 5, 2026-07-22 session, with the user's explicit approval. This signature approves the document as a reference specification for future implementation slices — it does not itself authorize implementation of any slice, including Slice PUSP-A. Each slice requires its own explicit scoping and authorization before write-enabled work begins, following this project's established discipline (as used for the constraint-provenance-redesign project's CPROV-A..J slices).
