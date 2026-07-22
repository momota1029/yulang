# General subtype explanation bridge across infer, poly, and specialize

Date: 2026-07-22

Status: draft reference design for a staged general-subtype explanation project. This document
specifies the representation, invariants, rollout order, and diagnostic-integration gates, but does
not authorize implementation of any slice.

Current-code citations were re-verified against the working tree on 2026-07-22. Line references
identify the code shape investigated for this design and must be rechecked at the start of each
implementation slice.

The immediate predecessors and foundation are:

- commit `4f3cf396` (`test(infer): characterize general subtype provenance gap`), which proves that
  four representative general `UnsatisfiedSubtype` failures have exact infer-side canonical
  constraint records but no surviving identity at specialize time;
- `notes/design/2026-07-21-constraint-provenance-redesign-spec.md`, which defines the canonical
  append-only derivation graph and the bounded CPROV-H explanation API;
- `notes/design/2026-07-22-parameter-use-site-provenance-spec.md`, which defines exact generalized
  witnesses and same-session scheme-instantiation edges and demonstrates a narrower end-to-end
  explanation bridge for `MissingImplicitCast`;
- commit `ff88e762`, which completes PUSP-A through PUSP-F and is the latest relevant implementation
  baseline for this design.

This project extends those results. It does not replace CPROV, duplicate PUSP's generalized-witness
model, alter subtype semantics, or infer provenance after the fact by structurally matching rendered
types.

## 1. Purpose and problem statement

### 1.1 User-facing gap

The general specialize error:

```rust
SpecializeError::UnsatisfiedSubtype {
    lower,
    upper,
    origin: None,
}
```

reports that one materialized type is not a subtype of another, but it cannot identify the source
obligations that produced either side. Its display can say that a tuple, record, or polymorphic
variant is structurally incompatible. It cannot explain why the lower structure was inferred or why
the upper structure was required.

This is the largest remaining source-provenance gap in the subtype diagnostic surface. Earlier
diagnostic-provenance work classified it as constraint-graph-origin and therefore hard: the failure
is detected during specialization, while the causal subtype relations were created during
inference.

CPROV and PUSP change the feasibility boundary:

- CPROV gives infer canonical constraints and bounds stable identities and exact derivation edges;
- CPROV-H can explain those records with deterministic, cycle-safe hard budgets;
- PUSP preserves exact contributors through selected generalization and same-session instantiation
  positions;
- PUSP-F demonstrates that an internal derivation can be projected into additive,
  presentation-neutral related information without exposing graph IDs to `crates/yulang`.

The remaining problem is not whether causal records exist. It is preserving their identity across
the infer-to-poly-to-specialize lifetime boundary.

### 1.2 Characterization evidence

Commit `4f3cf396` keeps a test-only `BodyLowering` alive while specializing its adjacent
`poly::Arena`. That arrangement is intentionally unavailable in production, but it permits a
one-time structural correlation between each specialize failure and the still-live infer machine.

The checked-in characterization records:

| case | infer canonical record | query nodes | query edges | completeness |
| --- | ---: | ---: | ---: | --- |
| shallow tuple arity | `ConstraintRecordId(45)` | 36 | 48 | complete |
| tuple arity through a generic call | `ConstraintRecordId(89)` | 71 | 94 | complete |
| nested tuple arity | `ConstraintRecordId(69)` | 41 | 53 | complete |
| polymorphic-variant tag mismatch | `ConstraintRecordId(21)` | 16 | 18 | complete |

The exact numeric IDs are characterization-local, not stable cross-build identities. Their
significance is that all four specialize failures have an exact infer-side causal record and a
bounded complete explanation before the session is dropped.

The test also proves the production gap:

- `BuildPolyOutput` retains `poly::Arena` and sparse source-side metadata;
- it does not retain `AnalysisSession`, `ConstraintMachine`, CPROV records, or a queryable graph;
- specialize receives no `ConstraintRecordId` or `BoundRecordId`;
- post-hoc structural matching is test-only and becomes ambiguous after generalization,
  materialization, simplification, and structural sharing.

The four corpus witnesses exercise three current general `origin: None` construction arms in
`crates/specialize/src/specialize2/type_graph.rs`:

- tuple arity mismatch at lines 396-398;
- missing required record field at lines 399-408;
- missing polymorphic-variant tag at lines 422-430.

All three call `unsatisfied_subtype` at lines 530-535. The phrase "four characterized call sites" in
earlier project discussion refers to the four corpus witnesses above; the current code has three
general match arms. The separate task-solver missing-record-field origin is already structured and
is not the target of this project.

### 1.3 Decided architectural direction

**Decided:** provenance identity crosses the production boundary explicitly as a portable,
occurrence-sensitive sidecar owned by the poly layer.

The bridge is not:

- post-hoc matching of equal `poly` or `mono` type structure;
- a provenance field inside `poly::Pos`, `poly::Neg`, `poly::Neu`, `poly::Scheme`, or `mono::Type`;
- a bare `PosId -> infer record` map;
- a copied proof tree per expression, scheme instantiation, or specialize subtype work item;
- a diagnostics-only table of preformatted explanation strings.

The bridge is:

```text
infer canonical CPROV graph
    -> portable reachable graph snapshot
    + occurrence ownership tables
    -> poly::Arena + poly-layer provenance sidecar
    -> SchemeMaterializer projects matching mono structural positions
    -> specialize TypeGraph propagates only along semantic structural children
    -> general UnsatisfiedSubtype retains opaque lower/upper provenance anchors
    -> bounded CPROV-H traversal over the portable snapshot
    -> presentation-neutral subtype explanation
    -> additive source related-information
```

This is materially larger than completing PUSP-C's structural paths. PUSP covers generalized scheme
positions within one infer session. General specialize comparisons also consume expression-derived
and pattern-derived types, and they run after that session has been destroyed.

### 1.4 Relationship to CPROV and PUSP

CPROV remains authoritative for:

- canonical record and edge semantics;
- exact parent identity;
- append-only provenance;
- semantic/provenance progress separation;
- replay's binary-parent model;
- completeness reporting;
- bounded, deterministic, cycle-safe traversal;
- the prohibition on proof-path enumeration.

PUSP remains authoritative for:

- exact generalized-scheme witnesses;
- honest `Incomplete` results when compact transformations cannot preserve exact contributors;
- typed structural paths across generalization and instantiation;
- shared witnesses plus per-use mappings rather than copied definition graphs.

This project generalizes PUSP's typed path representation into a poly-owned, layer-neutral path and
extends exact ownership to scheme, expression, and pattern occurrences. It exports a bounded snapshot
of the existing CPROV graph; it does not create another causal graph with independent semantics.

## 2. Goals, non-goals, and scope boundary

### 2.1 Required goals

The project must provide:

1. a portable opaque provenance anchor distinct from infer's session-local record IDs;
2. a bounded immutable snapshot containing the exact CPROV records and incoming edges reachable
   from exported occurrence anchors;
3. occurrence-sensitive ownership keyed by definition, expression, or pattern identity plus a typed
   structural path and semantic role;
4. exact generalized witness coverage for the tuple, record, variant, row, constructor, and function
   positions needed by the characterized failures;
5. expression and pattern ownership capture for mismatch endpoints that do not originate in a
   generalized scheme;
6. provenance projection inside `SchemeMaterializer`, while source poly identity and destination
   mono structural position are simultaneously known;
7. exact provenance propagation through specialize's already-selected structural subtype children;
8. lower and upper portable anchors on a covered general `UnsatisfiedSubtype`;
9. bounded explanation projection using CPROV-H's traversal engine rather than a new unbounded
   walker;
10. additive source related-information that explains why each covered mismatch side exists;
11. graceful, behavior-identical degradation when provenance is absent, incomplete, truncated,
    imported, or cache-loaded;
12. measurements proving linear storage in realized occurrence mappings and no semantic output
    change before the final diagnostic slice.

### 2.2 Explicit non-goals

This project does not include:

- changing infer or specialize subtype semantics;
- changing `mono::Type`, `poly::Scheme`, or poly node semantic equality;
- making provenance part of an arena hash-cons key, specialize instance key, subtype queue key,
  cache key, or fixed-point condition;
- reconstructing a dropped graph by comparing rendered or structurally equal types;
- serializing the portable graph or occurrence sidecar into compiled units or caches;
- explaining imported or fully cache-loaded code beyond today's diagnostic;
- making `BuildPolyOutput` retain a mutable `AnalysisSession` or `ConstraintMachine`;
- copying all CPROV records when only a bounded reachable closure is needed;
- preserving every proof path as an owned tree;
- changing PUSP's honest incomplete classification into whole-definition fallback ownership;
- covering every specialize error variant;
- changing the already-structured `MissingRecordField` or `MissingImplicitCast` origins as part of
  the initial general-subtype surface;
- selecting explanation sites by definition name, field spelling, rendered type, fixture path, or
  source-text rescan;
- final LSP graph navigation, arbitrary public "why type" commands, or cache-portable provenance.

### 2.3 Cold-only, same-build boundary

**Decided:** the initial bridge is cold-only and same-build.

Freshly lowered sources may carry their portable sidecar through `BuildPolyOutput` into specialize.
An arena reconstructed from a compiled-unit cache receives an empty sidecar. A prefix-cache build
may explain freshly lowered suffix occurrences, but imported prefix occurrences remain unbridged.

The behavior contract is:

- absent portable provenance does not suppress or alter `UnsatisfiedSubtype`;
- imported and cache-loaded occurrences render today's spanless/general diagnostic;
- no cache artifact version changes in this project;
- no source route is rejected because provenance is unavailable;
- full cache/build explanation parity is deferred to a separately designed project.

This matches CPROV/PUSP's established policy that unavailable cross-session provenance degrades
honestly rather than being fabricated.

### 2.4 Initial structural surface

The first accepted mismatch surface is:

- tuple arity mismatch, shallow and nested;
- missing required record field in the general TypeGraph path;
- polymorphic-variant tag mismatch;
- the generic-call tuple case from the characterization corpus.

Tuple element, record field, variant payload, row item, constructor argument, function position, and
recursive-bound steps belong to the shared path taxonomy. Their mere presence in the taxonomy does
not claim complete ownership coverage.

Effect-row failures, role-associated comparisons, recursive bounds, and specialize-generated open
variables must be characterized before they are claimed complete.

## 3. Current lifecycle and information-loss points

### 3.1 Infer canonical analogs

Infer has an exact canonical record before handoff for each characterized failure. The records are
queryable through `why_constraint` and reach typed source/internal origins through the existing
CPROV graph.

The source-side semantic counts and explanation topology are fixed by
`crates/infer/src/constraints/tests/subtype_provenance_characterization.rs`. The test explicitly
retains `BodyLowering` only to demonstrate feasibility. Production does not have that object at the
failure consumer.

The missing data is therefore identity transport, not a missing causal fact in the four initial
cases.

### 3.2 Generalization and current PUSP coverage

`generalize_type_var_with_boundaries` begins from the live machine at
`crates/infer/src/generalize/mod.rs:70-80`. PUSP-C's adjacent collector in
`crates/infer/src/generalize/provenance.rs` records exact bound contributors.

The current collector is deliberately narrow:

- it follows function-argument positions;
- `function_argument_path_survives` rejects non-function-argument steps;
- sandwiches mark affected witnesses incomplete;
- recursive bounds are represented but incomplete;
- no whole-definition origin set is substituted.

`GeneralizedTypePathStep` already contains function, constructor, tuple, record, variant, row, and
recursive-bound vocabulary at `crates/infer/src/constraints/mod.rs:697-723`.

The core PUSP instantiator projection at `crates/infer/src/instantiate.rs:208-284` currently advances
only `FunctionArgument`. Completing structural witnesses is required, but it still covers only
scheme-owned positions in the live infer session.

### 3.3 Infer/poly handoff and session teardown

`BodyLowerer::finish` settles source role candidates, classifies and activates OCAST, finalizes poly
role implementations, extracts diagnostics and source provenance, and returns a `BodyLowering` at
`crates/infer/src/lowering/body/mod.rs:1430-1487`.

`BuildPolyOutput` then retains:

```text
poly::expr::Arena
ApplicationProvenanceTable
SelectionProvenanceTable
diagnostic source data
labels and host manifest
formatted lowering errors
```

at `crates/yulang/src/source/mod.rs:1496-1506`. It does not retain the infer session or constraint
machine. The production build path moves `lowering.session.poly` into this output around lines
291-300.

The compiled-unit route at lines 307-319 deliberately creates empty application and selection source
tables. This is the model for the decided cold-only subtype sidecar: cache reconstruction yields an
empty subtype-provenance sidecar rather than stale or guessed ownership.

### 3.4 Poly representation and structural sharing

`poly::expr::Arena` owns arena-local `DefId`, `ExprId`, `PatId`, `RefId`, and `SelectId`, plus a
hash-consed `TypeArena` (`crates/poly/src/expr.rs:9-86`).

`poly::Scheme` contains quantifiers, role predicates, recursive bounds, stack quantifiers, and one
`PosId` predicate (`crates/poly/src/types.rs:10-23`). `TypeArena` structurally shares equal poly
nodes.

Consequently, a bare mapping:

```text
PosId -> provenance anchor
```

is unsound as occurrence ownership. Two unrelated definitions or expressions can refer to the same
interned node. Their type structure is equal, but their source obligations are not.

Poly node IDs remain useful as transient projection inputs while materializing one known occurrence.
They are not sufficient as the stable ownership key.

### 3.5 Scheme materialization

`SchemeMaterializer` is defined at `crates/specialize/src/types/mod.rs:329-345`. Its recursive
functions in `crates/specialize/src/types/materialize.rs` receive `PosId`, `NegId`, or `NeuId` and
construct plain `mono::Type`.

This is the last point at which both are simultaneously known:

- the source poly node and occurrence path;
- the destination mono structural position.

After `materialize_pos`, `materialize_neg`, or `materialize_neu` returns:

- the semantic result is a plain `mono::Type`;
- substitutions may have replaced variables;
- unions/intersections or bounds may have simplified;
- record, tuple, variant, constructor, and function children are plain owned values;
- the source poly node ID is gone.

Re-walking the mono result after this point cannot restore exact ownership.

### 3.6 Specialize TypeGraph and general failure construction

`TypeGraph::constrain_weighted_subtype` constructs a semantic
`SubtypeConstraint { lower, lower_weight, upper, upper_weight }` and deduplicates it in
`queued_constraints` at `crates/specialize/src/specialize2/type_graph.rs:57-79`.

The key derives `Hash` and `Eq` over semantic `mono::Type` and stack weights at
`crates/specialize/src/specialize2/mod.rs:414-420`.

`process_subtype` destructures the types and creates child semantic constraints:

- equal-length tuples enqueue corresponding element pairs;
- records enqueue corresponding required-field pairs or fail at the container;
- variants enqueue corresponding payload pairs or fail at the container;
- open variables store and replay bounds inside specialize's own type slots.

At the general mismatch arms, only materialized types remain. `unsatisfied_subtype` constructs
`origin: None`; it has no infer or poly position identity.

### 3.7 Existing adjacent metadata precedent

The project already keeps sparse, source-owned metadata outside semantic IR identity:

- `ApplicationProvenanceTable` maps arena-local `ExprId` to source application metadata;
- `SelectionProvenanceTable` maps arena-local selection and definition IDs to source spans;
- both are carried adjacent to `poly::Arena` in `BuildPolyOutput`;
- downstream stages translate them through their own occurrence IDs without changing semantic
  expression or type equality.

There is no equivalent provenance field on poly type nodes themselves. This project follows the
adjacent-table precedent and introduces its sidecar in a new poly-owned provenance module.

## 4. Required invariants

### 4.1 Semantic and provenance identity remain disjoint

The primary invariant is:

> Portable provenance never participates in semantic `Hash`, `Eq`, interning, subtype
> canonicalization, queue admission, instance identity, role resolution, cache identity, or
> termination.

The following remain byte-for-byte semantically equivalent:

- `poly::Scheme`;
- `poly::Pos`, `poly::Neg`, and `poly::Neu`;
- `mono::Type`;
- `specialize2::SubtypeConstraint`;
- generalized and instantiated predicates;
- emitted mono/control programs;
- compiled-unit cache format.

### 4.2 Occurrence ownership, not interned-node ownership

Ownership is keyed by:

```text
(DefId | ExprId | PatId, semantic role, typed structural path)
```

An interned poly node may be used while projecting that occurrence, but it never replaces the
occurrence key.

Two occurrence keys may map to the same poly node and different provenance anchors. That is expected
and must not duplicate the semantic poly node.

### 4.3 Exact contributors and exact structural projection

Each exported anchor points to an exact canonical CPROV node. Each materialization and specialize
edge advances only by the structural step already selected by semantic processing.

The implementation must not:

- assign every definition origin to every scheme position;
- assign a container's complete origin set to every child;
- select a contributor because its displayed type equals the failed type;
- infer ownership from field or variant spelling alone;
- cross-product alternate lower and upper proof paths.

If an exact mapping cannot be preserved, that occurrence path becomes incomplete.

### 4.4 Portable snapshot is immutable and bounded

At infer quiescence, the exporter builds one immutable snapshot of canonical graph records reachable
backward from registered occurrence anchors. Shared ancestors are exported once and referenced by
portable IDs.

The exporter has explicit node, edge, depth, per-anchor fan-in, and logical-byte budgets. Exceeding a
budget:

- marks affected anchors and the snapshot incomplete;
- retains already-exported canonical records;
- does not change semantic lowering;
- does not retry with an unbounded traversal;
- does not replace the missing graph with a flattened source set.

### 4.5 No proof-path enumeration

The CPROV-G combinatorial-blowup incident is a standing negative requirement.

Allowed storage:

- one portable node per exported canonical graph node;
- one portable edge per exported canonical derivation edge;
- one bounded deduplicated anchor set per occurrence;
- one bounded direct structural edge per realized specialize mapping;
- shared immutable graph ancestry.

Forbidden storage:

- `Vec<Vec<...>>` alternatives of complete proof paths;
- Cartesian products of lower and upper explanations;
- one copied graph per instantiation, expression, pattern, or subtype work item;
- recursive owned explanation trees;
- copying all definition records into each generalized or materialized position.

### 4.6 Provenance-only merging never creates semantic progress

Adding an occurrence owner, portable edge, materialized mapping, or specialize mapping:

- does not enqueue semantic subtype work;
- does not insert a second semantic `SubtypeConstraint`;
- does not change `queued_constraints`;
- does not create or replay a specialize type-slot bound;
- does not change infer `ConstraintEpoch`;
- does not change instance or cache admission;
- does not affect success or failure.

If late duplicate semantic work contributes a new provenance mapping, a separate provenance record,
canonical indirection, or bounded provenance-only queue handles it. Semantic requeue is forbidden.

### 4.7 Querying remains bounded and cycle-safe

The portable snapshot preserves canonical graph sharing and can expose recursive paths. Querying must
reuse CPROV-H's:

- visited set;
- deterministic append-only edge ordering;
- node budget;
- edge budget;
- depth budget;
- explicit completeness and truncation result.

No renderer or specialize error formatter may walk the graph directly.

### 4.8 Diagnostic degradation is additive and honest

When complete mapped provenance is available, the general subtype diagnostic may gain a primary
span and related explanation sites.

When it is unavailable:

- the same `UnsatisfiedSubtype` still fires;
- the same lower and upper `mono::Type` values are displayed;
- the current general wording remains valid;
- no span or causal claim is fabricated;
- imported and cached builds retain today's behavior.

## 5. Decided provenance model

### 5.1 Poly-layer sidecar ownership

**Decided:** portable bridge types live in a dedicated poly module, conceptually
`poly::provenance`.

The sidecar is adjacent to `poly::Arena`; it is not a field on semantic type nodes. `BuildPolyOutput`
owns:

```rust
struct BuildPolyOutput {
    arena: poly::expr::Arena,
    subtype_provenance: poly::provenance::SubtypeProvenanceSidecar,
    // existing source and build fields
}
```

Specialize entry points that need explanation receive both the arena and the sidecar. Ordinary
semantic APIs may continue to accept only the arena and behave exactly as today.

The cold-only project does not serialize `subtype_provenance`. Cache reconstruction supplies
`SubtypeProvenanceSidecar::empty()`.

This placement lets infer produce the artifact, specialize consume it, and yulang query it without
making poly depend on infer's mutable graph implementation.

### 5.2 Shared structural path

**Decided:** introduce a layer-neutral `TypePositionPath` in `poly::provenance` and migrate
PUSP's `GeneralizedTypePath` to use it.

The canonical sketch is:

```rust
struct TypePositionPath(Vec<TypePositionStep>);

struct TypePositionIndex(u32);

enum TypePositionStep {
    FunctionArgument,
    FunctionArgumentEffect,
    FunctionReturnEffect,
    FunctionReturn,
    ConstructorArgument {
        alternative: TypePositionIndex,
        argument: TypePositionIndex,
    },
    TupleElement(TypePositionIndex),
    RecordField {
        alternative: TypePositionIndex,
        field: TypePositionIndex,
    },
    VariantPayload {
        alternative: TypePositionIndex,
        item: TypePositionIndex,
        payload: TypePositionIndex,
    },
    RowItemArgument {
        item: TypePositionIndex,
        argument: TypePositionIndex,
    },
    RowTail,
    RecursiveBound(TypePositionIndex),
}
```

The path contains typed structural indices, never source text, rendered type strings, or an arena
node ID. A poly node ID may be paired with a path transiently during materialization, but the path
remains the stable structural address.

PUSP's current `GeneralizedTypePathStep` has this vocabulary. Migration should be an exact
representation move or lossless conversion with characterization parity. The shared type does not
change PUSP witness semantics.

The exact extension rules for record spreads, materialized union/intersection alternatives, and
container-only mismatch sites remain slice-level decisions under Section 13.

### 5.3 Portable anchors and graph snapshot

Infer session-local IDs do not cross the boundary. Export allocates new dense portable IDs:

```rust
struct ProvenanceAnchor(u32);
struct PortableProvenanceNodeId(u32);
struct PortableProvenanceEdgeId(u32);
struct PortableSourceSiteId(u32);

struct PortableProvenanceSnapshot {
    nodes: Vec<PortableProvenanceNode>,
    edges: Vec<PortableProvenanceEdge>,
    source_sites: Vec<PortableSourceSite>,
    completeness: ProvenanceCompleteness,
}
```

`ProvenanceAnchor` resolves to one portable graph node plus per-anchor completeness:

```rust
struct PortableAnchorRecord {
    node: PortableProvenanceNodeId,
    completeness: ProvenanceCompleteness,
}
```

Portable nodes preserve typed causal identity needed by CPROV-H:

- canonical constraint;
- canonical bound and direction;
- source/internal origin;
- generalized witness;
- scheme-instantiation witness;
- row, subtract-fact, disposition, and other already-queryable record classes.

Portable edges preserve the existing typed derivation rule and ordered exact parents. They do not
retain infer `ConstraintRecordId`, `BoundRecordId`, `TypeVar`, or arena type-node IDs.

Source leaves resolve to a presentation-neutral source site containing module identity, byte range,
and semantic source role. Conversion from infer `SourceSpan` happens during export. Exact filesystem
resolution remains yulang's responsibility.

The exporter reindexes a backward reachable closure from registered occurrence anchors. It does not
copy unrelated session records.

### 5.4 Occurrence owners and roles

The sidecar uses one key form:

```rust
struct TypeOccurrenceKey {
    owner: TypeOccurrenceOwner,
    role: TypeOccurrenceRole,
    path: TypePositionPath,
}

enum TypeOccurrenceOwner {
    Definition(DefId),
    Expression(ExprId),
    Pattern(PatId),
}

enum TypeOccurrenceRole {
    DefinitionPredicate,
    DefinitionRecursiveLower(TypePositionIndex),
    DefinitionRecursiveUpper(TypePositionIndex),
    ExpressionActual,
    ExpressionExpected,
    PatternInput,
    PatternRequirement,
}

struct OccurrenceProvenance {
    anchors: Vec<ProvenanceAnchor>,
    completeness: ProvenanceCompleteness,
}
```

The anchor vector is a bounded, deduplicated list of exact alternate canonical contributors. It is
not a list of paths. An empty list with `Incomplete` means unavailable provenance; it does not mean
the position has no cause.

The role vocabulary distinguishes which side of a later comparison an occurrence represents.
Definition, expression, and pattern IDs are arena-local occurrence identities and remain outside
semantic type equality.

### 5.5 Poly sidecar

The complete cold-build artifact is:

```rust
struct SubtypeProvenanceSidecar {
    snapshot: PortableProvenanceSnapshot,
    occurrences: TypeOccurrenceProvenanceTable,
    metrics: SubtypeProvenanceMetrics,
}
```

The occurrence table is sparse. Only positions with a characterized exact infer owner are inserted.
Synthetic or imported positions are absent or incomplete.

The snapshot and occurrence table are immutable after the infer/poly handoff. Specialize derives
ephemeral materialized and work-item mappings from them but does not mutate causal infer history.

### 5.6 Materialized type provenance

`SchemeMaterializer` returns semantic data and adjacent metadata:

```rust
struct MaterializedTypeWithProvenance {
    ty: mono::Type,
    provenance: MaterializedTypeProvenance,
}

struct MaterializedTypeProvenance {
    positions: Vec<MaterializedPositionProvenance>,
    completeness: ProvenanceCompleteness,
}

struct MaterializedPositionProvenance {
    path: TypePositionPath,
    anchors: Vec<ProvenanceAnchor>,
    completeness: ProvenanceCompleteness,
}
```

The semantic `ty` is exactly today's materialization result. The wrapper is not hashed, compared, or
stored as an instance key. Callers that do not request provenance receive or extract the same
semantic type.

Projection advances the registered occurrence path during the existing recursive materialization.
It does not re-walk the finished mono tree.

### 5.7 Specialize subtype-work provenance

Specialize keeps a parallel canonical provenance table keyed by the existing semantic subtype key:

```rust
struct SpecializeSubtypeProvenanceRecordId(u32);

struct SpecializeSubtypeProvenanceRecord {
    semantic_key: SubtypeConstraint,
    incoming: Vec<SpecializeProvenanceDerivation>,
    completeness: ProvenanceCompleteness,
}

enum SpecializeProvenanceDerivation {
    Root {
        lower: Vec<ProvenanceAnchor>,
        upper: Vec<ProvenanceAnchor>,
    },
    Structural {
        parent: SpecializeSubtypeProvenanceRecordId,
        step: TypePositionStep,
    },
    OpenVarBound {
        parents: Vec<SpecializeSubtypeProvenanceRecordId>,
    },
}
```

This table is not the semantic queue. The existing `HashSet<SubtypeConstraint>` remains the sole
semantic admission key.

One semantic child records one typed structural edge to its parent. It does not copy the parent's
portable snapshot ancestry. A semantically duplicate constraint may merge an alternate exact
provenance derivation without semantic requeue.

If late provenance must be exposed after the semantic child already exists, canonical parent
indirection or a bounded provenance-only worklist handles it. The implementation must not rerun
`process_subtype`.

### 5.8 Failure provenance

The general error gains optional opaque metadata:

```rust
struct SubtypeFailureProvenance {
    lower: Vec<ProvenanceAnchor>,
    upper: Vec<ProvenanceAnchor>,
    completeness: ProvenanceCompleteness,
}
```

or an equivalent reference to the final specialize provenance record from which those endpoint
anchors can be projected before returning the error.

`SpecializeError::UnsatisfiedSubtype` retains `lower`, `upper`, and `origin`. Covered general
failures add optional provenance. Existing structured origins remain unchanged.

The internal model can retain both endpoints. Whether the first public renderer shows both causal
chains or selects one primary chain remains an explicit presentation decision in Section 13.

### 5.9 Completeness composition

Completeness is monotone:

- an incomplete infer anchor makes the occurrence incomplete;
- an unsupported PUSP structural path makes that occurrence position incomplete;
- an incomplete snapshot export makes all affected mapped positions incomplete;
- a materialization step with no exact path mapping is incomplete;
- a specialize structural step that cannot project exact ownership is incomplete;
- query truncation remains incomplete.

No later layer upgrades incomplete evidence to complete. Diagnostic rendering only claims a causal
site when the selected chain is complete and source-located.

## 6. Infer capture and portable handoff touchpoints

### 6.1 Touchpoint: generalized scheme ownership

**Current state.** PUSP-C captures exact function-argument witnesses in
`crates/infer/src/generalize/provenance.rs`. Non-function positions are mostly omitted or incomplete,
and `function_argument_path_survives` rejects their paths.

**Required change.** Extend exact capture for the tuple, record, variant, row, constructor, function,
and recursive-bound positions accepted by this project's characterized corpus. Convert the resulting
paths to `poly::provenance::TypePositionPath`.

Every output position must point to exact canonical constraint/bound parents through the existing
`GeneralizedSchemeWitness`. Unsupported compact transformations remain incomplete.

**Semantic isolation.** Witness capture observes existing generalization choices. It cannot alter
bound order, substitutions, sandwiches, pruning, quantification, final poly nodes, or scheme
fingerprints.

### 6.2 Touchpoint: expression occurrence ownership

**Current state.** Infer/lowering retains expression IDs and internal typing state while the session
is alive. `SolvedTask` later stores specialize-side expression actual types, but no infer canonical
record accompanies the `ExprId`.

**Required change.** At the final infer seam where an expression's poly-facing actual or expected
position is installed, register:

```text
(ExprId, ExpressionActual | ExpressionExpected, TypePositionPath) -> exact canonical parents
```

Capture occurs while both `ExprId` and the causal constraint/bound records are known. Synthetic
expressions without exact source ownership remain absent or incomplete.

**Semantic isolation.** Registration does not create a type, constraint, event, or source span. It
does not affect expression lowering or evaluation order.

### 6.3 Touchpoint: pattern occurrence ownership

**Current state.** Specialize derives pattern requirements and stores pattern-related signatures by
`PatId`. The polymorphic-variant characterization demonstrates a causal infer record, but no
production identity crosses with the pattern occurrence.

**Required change.** Register exact pattern input and pattern-requirement positions:

```text
(PatId, PatternInput | PatternRequirement, TypePositionPath) -> exact canonical parents
```

Container-level ownership must be retained when a missing variant tag has no child payload on one
side. It must not fabricate a child anchor.

**Semantic isolation.** Pattern matching, exhaustiveness behavior, variant ordering, and emitted
pattern IR remain unchanged.

### 6.4 Touchpoint: portable graph export

**Current state.** CPROV records and CPROV-H queries are infer-internal. The graph is dropped with the
session.

**Required change.** At constraint/provenance quiescence:

1. collect all exact internal graph nodes referenced by registered definition, expression, and
   pattern occurrences;
2. traverse incoming parents with the approved export budget;
3. globally deduplicate shared nodes and edges;
4. reindex them into portable IDs;
5. convert source leaves to portable source-site records;
6. mark every anchor's completeness;
7. freeze the snapshot.

The exporter should share CPROV-H's node/edge visitors and stable ordering. It may use a specialized
multi-root export driver, but not a second derivation interpretation.

**Semantic isolation.** Export runs after semantic quiescence, performs no solver mutation, and
cannot affect diagnostics until the final integration slice.

### 6.5 Touchpoint: `BodyLowerer::finish` and `BuildPolyOutput`

**Current state.** `BodyLowerer::finish` still owns the complete session before returning.
`BuildPolyOutput` later moves out only `session.poly` and sparse source tables.

**Required change.** Freeze `SubtypeProvenanceSidecar` before moving the poly arena, then carry both
through the fresh-source `BuildPolyOutput` route.

Every constructor of `BuildPolyOutput` must make its route explicit:

- fresh full lowering: populated sidecar;
- cached full artifact: empty sidecar;
- cached prefix plus fresh suffix: sidecar for exact fresh suffix occurrences only;
- synthetic/test arena: empty unless the test explicitly installs ownership.

**Semantic isolation.** The compiled-unit artifact and cache envelope do not gain a field. Existing
arena serialization remains byte-identical.

## 7. Materialization and specialize touchpoints

### 7.1 Touchpoint: `SchemeMaterializer`

**Current state.** `materialize_pos`, `materialize_neg`, and `materialize_neu` recursively transform
poly node IDs into `mono::Type`, then discard source IDs.

**Required change.** Add provenance-aware companion entry points that accept one occurrence owner and
its role. During the existing recursion, advance `TypePositionPath` in lockstep with semantic
construction and emit `MaterializedPositionProvenance`.

Substitution, bound materialization, union/intersection simplification, record spreads, and function
runtime-shape conversion require explicit projection rules. If a transformation coalesces positions
without an exact mapping, mark only the metadata incomplete.

**Semantic isolation.** The semantic materialization functions remain the source of truth. The
provenance companion cannot select a different substitution, default, simplification, or function
shape.

### 7.2 Touchpoint: specialize task roots

**Current state.** Specialize creates task-local actual and expected expression types, reference
signatures, selection signatures, and pattern signatures as plain `mono::Type` values.

**Required change.** When creating a semantic TypeGraph root constraint, resolve the matching
definition/expression/pattern occurrence and attach its materialized anchor set to the parallel
provenance record.

Every root mapping identifies its role and exact structural path. Missing sidecar data creates an
incomplete/no-anchor provenance root without changing semantic admission.

**Semantic isolation.** Task identity, `InstanceKey`, demand creation, expression order, and role
resolution remain unchanged.

### 7.3 Touchpoint: TypeGraph semantic dedup and provenance records

**Current state.** `queued_constraints` deduplicates the complete semantic
`SubtypeConstraint`; only first insertion enters `pending`.

**Required change.** Intern an adjacent provenance record under the same semantic key. First semantic
admission queues exactly once. Later semantically equal input:

- leaves the semantic set and queue unchanged;
- merges one exact provenance derivation;
- deduplicates by result record, rule, ordered parent records, and structural payload;
- marks incomplete on budget exhaustion.

**Semantic isolation.** Provenance cardinality never controls the semantic queue or solve loop.

### 7.4 Touchpoint: tuple structural propagation

**Current state.** Equal-length tuple constraints enqueue one child pair per positional zip.
Different lengths immediately construct the general error.

**Required change.**

- Equal-length decomposition records a `TupleElement(index)` edge on each child provenance record.
- Arity failure retains container-level lower and upper anchors from the current record.
- Nested tuple failures follow exact child paths and do not inherit unrelated sibling ownership.

**Semantic isolation.** Tuple length checks, element order, and child constraints are unchanged.

### 7.5 Touchpoint: record and variant structural propagation

**Current state.** Records fail when an upper required field is absent, otherwise corresponding field
types are constrained. Variants fail when a lower tag is absent from the upper set, otherwise
corresponding payloads are constrained.

**Required change.**

- matching record children advance by `RecordField`;
- matching variant payloads advance by `VariantPayload`;
- missing field/tag failures retain the exact container relationship witness because one side has no
  materialized child;
- alternate container owners remain separate graph edges rather than one flattened anchor set.

**Semantic isolation.** Field/tag matching, optionality, order, and payload constraint emission remain
unchanged.

### 7.6 Touchpoint: specialize open variables and bounds

**Current state.** `Type::OpenVar` uses task-local slots, bound vectors, and replay-like propagation
inside TypeGraph.

**Required change.** Characterize which root anchors reach slot lower/upper bounds and preserve exact
parent relationships for covered paths. The model must support a typed `OpenVarBound` provenance edge
without making slot identity portable or semantic.

The final rule for multi-parent open-variable relationships remains open until measured under
Section 13. Unsupported cases are incomplete, not guessed.

**Semantic isolation.** Slot allocation, bound insertion, successors/predecessors, weighted edges,
and closeout remain unchanged.

### 7.7 Touchpoint: general `UnsatisfiedSubtype`

**Current state.** `unsatisfied_subtype` receives only lower and upper `mono::Type` and creates
`origin: None`.

**Required change.** The three general failure arms also resolve the current
`SpecializeSubtypeProvenanceRecord` and project optional lower/upper portable anchors into
`SubtypeFailureProvenance`.

The error remains constructible without provenance. Existing structured origins continue through
their current code paths.

**Semantic isolation.** Provenance cannot convert success to failure, failure to success, or one
error kind to another.

## 8. Query, diagnostic, and presentation touchpoints

### 8.1 Expected query chain

A covered tuple mismatch should traverse:

```text
SpecializeError::UnsatisfiedSubtype
    -> lower/upper portable endpoint anchors
    -> TypeGraph exact structural relation
    -> materialized occurrence path
    -> poly occurrence ownership
    -> portable CPROV canonical constraint/bound node
    -> existing replay/structural/generalization/instantiation parents
    -> source/internal origin
    -> portable source site
```

The generic tuple case may traverse PUSP generalized and scheme-instantiation witnesses before
reaching the original infer bound. An expression or pattern endpoint may enter directly through its
own occurrence ownership. Both paths terminate in the same portable CPROV snapshot.

### 8.2 CPROV-H remains the traversal engine

**Decided:** no new unbounded subtype-explanation walker is introduced.

`crates/infer/src/constraints/explain.rs` gains a portable-snapshot adapter around the existing
bounded traversal engine. The adapter accepts one or more `ProvenanceAnchor` values and an explicit
`ExplanationBudget`. It uses the same:

- node/edge/depth accounting;
- visited-set semantics;
- typed edge interpretation;
- stable iteration order;
- completeness result.

The session-local `why_constraint`, `why_lower_bound`, and `why_upper_bound` APIs remain valid.
Portable querying is another root adapter, not a competing algorithm.

### 8.3 Presentation-neutral subtype explanation

The query result is projected inside infer-facing diagnostic code into a public, graph-ID-free
payload such as:

```rust
struct DiagnosticSubtypeExplanation {
    lower_sites: Vec<DiagnosticTypeCause>,
    upper_sites: Vec<DiagnosticTypeCause>,
    completeness: DiagnosticExplanationCompleteness,
}

struct DiagnosticTypeCause {
    role: DiagnosticTypeCauseRole,
    span: SourceSpan,
}

enum DiagnosticTypeCauseRole {
    InferredFromExpression,
    RequiredByAnnotation,
    RequiredByPattern,
    RequiredByBodyUse(BodyRequirementDiagnosticKind),
    RequiredByApplication,
}
```

No `ProvenanceAnchor`, portable graph node ID, infer record ID, poly node ID, or specialize work ID
reaches the renderer.

### 8.4 Yulang rendering

`crates/yulang/src/source/mod.rs` currently maps structured specialize errors plus adjacent source
tables into `SpecializeDiagnosticContext` and related information.

The final slice adds general-subtype explanation rendering only after the structured payload is
complete and tested. It should:

- preserve the existing primary mismatch wording;
- choose a primary source span only from complete, source-located evidence;
- add related sites with stable deterministic wording;
- avoid displaying duplicate locations;
- retain the spanless diagnostic when no safe primary site exists.

Exact wording and whether the first version shows both endpoint chains remain Section 13 decisions.

### 8.5 Unavailable and incomplete provenance

These cases degrade without additional explanation:

- full cache hit;
- imported prefix occurrence;
- synthetic poly arena with no sidecar;
- unsupported generalized witness;
- expression/pattern position without exact ownership;
- snapshot export budget exhaustion;
- materialization projection gap;
- TypeGraph propagation gap;
- query truncation;
- source-site resolution failure.

No layer substitutes a nearby span or equal rendered type.

## 9. Performance, storage, and completeness policy

### 9.1 Required measurements

The characterization and inert slices must record:

- occurrence keys by owner kind and role;
- occurrence paths by depth and final step;
- occurrence anchors considered, inserted, deduplicated, incomplete, and absent;
- exported snapshot nodes and edges by kind;
- shared snapshot parents and dedup ratio;
- snapshot logical-byte proxy and maximum reachable closure per anchor;
- generalized witnesses complete/incomplete by structural path;
- materialized mappings considered, inserted, deduplicated, and incomplete;
- maximum mapped positions per scheme, expression, pattern, and materialization;
- specialize provenance records and typed structural edges;
- semantically duplicate TypeGraph constraints receiving alternate provenance;
- maximum incoming provenance edges per specialize record;
- open-variable provenance edges and incomplete cases;
- failure endpoint anchors present by lower/upper side;
- query nodes, edges, depth, elapsed time, and truncation;
- cold/cache/prefix route availability;
- semantic constraint, instance, emitted-program, diagnostic-existence, cache, and output parity.

### 9.2 Storage shape

The infer snapshot shares canonical ancestors across every occurrence. Occurrence entries store small
anchor IDs. Materialized positions store paths and anchor IDs, not graph copies. TypeGraph stores
typed parent edges, not transitive explanation trees.

Growth should be:

```text
O(exported canonical graph nodes and edges)
+ O(realized occurrence positions)
+ O(realized materialized mappings)
+ O(realized specialize structural relations)
```

It must not scale with the number of complete proof paths.

### 9.3 Budgets and incomplete policy

Exact storage budgets are chosen from SUBP-A/B/E/F measurements. The following dimensions require
hard limits before their producing slice closes:

- snapshot nodes, edges, depth, and logical bytes;
- anchors per occurrence;
- paths per materialization;
- incoming edges per specialize provenance record;
- provenance-only pending work, if used;
- query nodes, edges, and depth.

Budget exhaustion preserves semantic behavior and marks only provenance incomplete. Existing
retained records remain valid.

### 9.4 Performance gates

Each inert slice compares:

- representative mismatch fixtures;
- full std lowering once;
- repeated generic instantiation;
- deep nested tuple/record structure;
- the 226-case contract corpus at final integration;
- peak RSS and wall/CPU time against the pre-slice baseline.

Any nonlinear growth, semantic requeue, or proof-path combination stops the slice for redesign.

## 10. Implementation stages and slices

All Rust changes are deferred to follow-up tasks. The slices follow the established pattern:
characterize occurrence seams, introduce portable inert identity, complete structural ownership,
project through materialization, propagate in specialize under shadow observation, prove bounded
queries, then integrate presentation separately.

### Slice SUBP-A: endpoint and occurrence characterization

Size: S-M. Risk: low.

Extend the `4f3cf396` corpus to inventory the exact definition, expression, and pattern occurrences
that feed each lower and upper mismatch endpoint. Capture current materialization entry points,
semantic TypeGraph keys, open-variable involvement, and source-site availability.

Add tuple, record, variant, generic, cache, prefix, and duplicate-semantic-constraint controls.

No portable IDs, sidecar fields, or diagnostic changes.

Exit witness: every initial mismatch endpoint is classified as scheme-, expression-, pattern-, or
specialize-generated; the last exact infer record and first identity-loss point are fixed in tests;
all semantic output is unchanged.

### Slice SUBP-B: portable graph snapshot and anchor export

Size: L. Risk: high.

Add poly-owned portable anchor, snapshot node/edge, source-site, completeness, and metrics types.
Implement deterministic multi-root export from selected CPROV records using the existing incoming
edge visitors. Keep the result test-only or adjacent to lowering; do not pass it to specialize yet.

Set the initial snapshot storage budget from characterization measurements.

Exit witness: exported anchors reproduce the same bounded explanations as their session-local
records for all initial fixtures; shared ancestors are exported once; forced budget exhaustion is
prompt and incomplete; semantic counts, schemes, diagnostics, and caches are byte-identical.

### Slice SUBP-C: shared path and generalized structural coverage

Size: L-XL. Risk: very high.

Introduce `poly::provenance::TypePositionPath`, migrate PUSP path storage losslessly, and extend exact
generalized witness capture/projection to the tuple, record, variant, row, constructor, and function
positions required by the corpus.

Preserve PUSP-C's explicit incomplete handling for sandwiches, recursive extraction, or other
transformations without exact output-to-parent mapping.

Exit witness: complete covered scheme positions resolve to the exact original infer records; path
encoding is stable across poly arena cloning; PUSP-A-F behavior and fingerprints are unchanged;
unsupported transformations remain visibly incomplete without whole-definition fallback.

### Slice SUBP-D: expression/pattern ownership and cold-build sidecar

Size: L-XL. Risk: very high.

Capture exact expression actual/expected and pattern input/requirement owners. Build
`SubtypeProvenanceSidecar` at infer quiescence and carry it adjacent to fresh `poly::Arena` through
`BuildPolyOutput`.

All cached/full-prefix constructors install an explicit empty or suffix-only sidecar. Do not modify
cache serialization.

Exit witness: every initial fresh-source occurrence resolves to its exact portable anchor; unrelated
occurrences sharing one poly node remain distinct; cache-loaded occurrences report unavailable;
semantic poly output and cache bytes remain unchanged.

### Slice SUBP-E: provenance-aware materialization shadow

Size: L-XL. Risk: very high.

Add adjacent materialization results and project occurrence paths during the existing
`SchemeMaterializer` recursion. Cover substitutions, tuple/record/variant children, function shape,
and required simplifications. Run in shadow beside existing materialization without feeding
TypeGraph or diagnostics.

Set and enforce materialized mapping budgets.

Exit witness: shadow semantic types are byte-identical to existing materialization; expected paths
map to exact portable anchors; structurally shared poly nodes retain occurrence-specific owners;
unsupported transformations are incomplete; no instance or emitted output changes.

### Slice SUBP-F: TypeGraph propagation and failure-anchor shadow

Size: XL. Risk: critical.

Add canonical specialize provenance records beside semantic subtype keys. Seed them from
materialized definition/expression/pattern mappings, propagate typed edges through exact structural
children and characterized open-variable relations, and compute lower/upper failure anchors.

Keep public `SpecializeError` and rendering unchanged initially. Record shadow failure provenance
for comparison.

This slice must prove that duplicate provenance does not requeue semantic work and that edge growth
is linear. It carries the same CPROV-G stop condition as CPROV-F/PUSP-D.

Exit witness: all initial failures have correct shadow lower/upper anchors; nested failures exclude
unrelated siblings; duplicate semantic constraints merge alternate edges without semantic requeue;
storage and timing remain within the approved budget; specialize output is unchanged.

**Implementation note added after SUBP-F landed (`9be09b6e`).** The canonical provenance table,
structural propagation, dedup-merge safety, and budget management described above were implemented
and proved entirely with synthetic `MaterializedTypeWithProvenance` values in tests. Attempting to
satisfy Section 7.2 ("resolve the matching definition/expression/pattern occurrence ... attach its
materialized anchor set") against real compilation revealed that no production call site can reach
that data yet: `SubtypeProvenanceSidecar` reaches `BuildPolyOutput` (Section 6.5) but is dropped at
the first specialize entry call (`crates/yulang/src/source/mod.rs:514`) and never reaches
`Specializer2`, `TaskSolver`, or the four scheme-instantiation functions that build
`InstantiatedScheme`. `constrain_materialized_subtype` therefore remains dead-code-annotated,
exercised only by tests. SUBP-F's own exit witness ("specialize output is unchanged") is satisfied;
the additional public-API threading needed to reach Section 7.2 in production is factored out as
Slice SUBP-I below, inserted into the dependency order between SUBP-F and SUBP-G.

### Slice SUBP-I: materialized provenance sidecar threading through specialize's public API and task roots

Size: L-XL, staged as three sub-slices (I-1/I-2/I-3); a fourth family of sites is an explicit
deferred follow-up (I-4), not part of this slice. Risk: high across I-1/I-2, high approaching
critical for I-3 (it is the first slice where real occurrence identity reaches
`constrain_materialized_subtype`, though it changes no dedup/merge/structural-propagation logic
proven in SUBP-F).

**Motivation.** See the implementation note above. This slice closes the gap between "shadow
infrastructure exists" and "Section 7.2's touchpoint is satisfied in production," without touching
the dedup/merge/structural-propagation logic SUBP-F already proved safe.

#### I-1: public API and struct storage plumbing (shadow only)

Add a required `&SubtypeProvenanceSidecar` parameter (not `Option` -- follow the existing
`SubtypeProvenanceSidecar::empty()` precedent already used at the cache-restoration route,
`crates/yulang/src/source/mod.rs:314`) to the six public `specialize` functions that reach
`Specializer2`/`TaskSolver`: `specialize`, `specialize_with_runtime_evidence`,
`specialize_with_runtime_evidence_and_application_provenance`,
`specialize_with_runtime_evidence_and_source_provenance`, `specialize2`, `role_method_check`. Thread
it through `Specializer2::with_source_provenance` and `TaskSolver::new`, storing it as
`sidecar: &'a SubtypeProvenanceSidecar` beside the existing `arena: &'a poly_expr::Arena`. Update
`crates/yulang/src/source/mod.rs:514` (the current drop point) and the mono-only route at `:4113` to
pass `&output.subtype_provenance` / `SubtypeProvenanceSidecar::empty()` respectively.

Nothing reads the sidecar's contents at this stage -- this proves the plumbing compiles and is
semantically inert (identical instances, identical output, identical contract suite) before any
consumption logic is added.

Exit witness: sidecar reaches `TaskSolver` at every real call site; specialize's output, instance
count, and emitted programs are byte-identical to pre-I-1; full contract suite unchanged.

#### I-2: `InstantiatedScheme` materialized provenance (shadow only)

The four scheme-instantiation functions (`instantiate_scheme_with_fresh_and_roles`,
`instantiate_principal_scheme_for_inference_with_fresh_and_roles`,
`instantiate_scheme_with_expected_fresh_and_roles`,
`instantiate_monomorphic_scheme_with_fresh_and_roles`) switch from `materialize_pos`/
`materialize_neg`/`materialize_neu` to the SUBP-E `_with_provenance` companions and additionally
return the projected `MaterializedTypeProvenance`.

`InstantiatedScheme` currently derives `Hash, Eq`; confirm at implementation time whether that
equality participates in any dedup key. Do not add a provenance-bearing field directly to
`InstantiatedScheme` -- return provenance as an adjacent value (a wrapper or tuple, mirroring
`MaterializedTypeWithProvenance`'s existing "semantic value plus unhashed adjacent metadata" shape)
so `InstantiatedScheme`'s own `Hash`/`Eq` derivation is untouched. This follows Section 4.1 directly:
semantic and provenance identity must not entangle.

Exit witness: a characterization test fixes `InstantiatedScheme`'s `Hash`/`Eq` output as unchanged;
the four instantiation functions produce byte-identical `ty` values; the new provenance wrapper is
constructed but not yet consumed outside tests.

#### I-3: root wiring for owner-compatible task roots

Using the call-site classification gathered during this slice's investigation, replace
`constrain_subtype`/`constrain_weighted_subtype` with `constrain_materialized_subtype` at each site
where an owner-compatible, unambiguous occurrence identity is already in scope without new plumbing:
definition-body and computed-def signature roots (`task_solver.rs:37,81`); expression actual/consumer
chains (`task_solver.rs:129,143,150,219,387,402`); let-binding and literal/tuple/list/variant-pattern
roots (`task_solver/control.rs:211,216,340,354,366,383`); reference-pattern scrutinee
(`task_solver/control.rs:533`). Resolve through the sidecar's sparse occurrence table; a missing
table entry for a specific `(owner, role, path)` key is expected and must produce an
incomplete/no-anchor root, not an error or a panic.

Explicitly out of scope for I-3, deferred to I-4: `task_solver.rs:58` (no `DefId` in scope for the
signature side), `task_solver/control.rs:283` (lambda's own `ExprId`/`DefId` not in scope),
`task_solver/control.rs:442,456,489,516` (parent record/constructor `PatId` lost before these
calls), `task_solver.rs:536`'s upper endpoint (ambiguous between child-expression and
outer-record-path representations). These need an identity-plumbing design decision, not mechanical
wiring.

Exit witness: for at least the def-body, expression-actual, and pattern-input root families, an
end-to-end test against real lowered source (not only synthetic `materialized_root()` helpers) shows
a non-empty, correct anchor on `subtype_provenance_records`/`shadow_subtype_failures`; specialize's
output remains byte-identical; the full regression suite (specialize, infer, cross-crate build, both
known false-positive repros, contract suite) passes unchanged.

#### I-4 (explicitly deferred, separate future slice)

The container-identity-missing sites listed above need a design decision: whether to thread parent
record/constructor/lambda identity down through pattern and lambda solving so I-3's mechanism can
reach them, or whether those roots remain permanently-incomplete provenance. Do not resolve this
inside SUBP-I; it is recorded as open decision 15 in Section 13.

### Slice SUBP-G: bounded portable query and diagnostic projection

Size: M-L. Risk: high.

Attach opaque failure anchors to an internal/test-visible failure payload. Add the portable root
adapter to CPROV-H's bounded traversal and project complete results into
`DiagnosticSubtypeExplanation`.

Do not render new public text.

Characterize cycles, alternate causes, endpoint selection, source-site absence, cache/prefix
degradation, and forced truncation.

Exit witness: the portable query returns the same typed source leaves as the retained-session control;
ordering is deterministic; truncation is explicit; internal IDs do not cross into the diagnostic
payload; public diagnostics remain byte-identical.

### Slice SUBP-H: additive general-subtype diagnostic integration

Size: M. Risk: critical.

Expose the approved presentation-neutral explanation on covered general
`SpecializeError::UnsatisfiedSubtype` failures and render primary/related source information in
`crates/yulang/src/source/mod.rs`.

Preserve the primary mismatch wording and all structured existing origins. Imported, cached,
incomplete, and truncated cases remain unchanged.

Run infer, poly, specialize, yulang library, CLI, contract, prefix/cache, and performance gates.

Exit witness: shallow, nested, generic tuple, record, and variant fixtures explain the correct causal
source locations; structurally equal unrelated occurrences are never conflated; cache/import controls
retain today's diagnostic; all 226 contract cases and semantic characterization gates pass; deleting
the integration leaves the portable graph and shadow evidence intact.

## 11. Slice dependencies and activation gates

The required order is:

```text
SUBP-A occurrence characterization
    -> SUBP-B portable snapshot
    -> SUBP-C shared path and generalized structural coverage
    -> SUBP-D expression/pattern ownership and cold-build sidecar
    -> SUBP-E materialization projection shadow
    -> SUBP-F TypeGraph propagation and failure-anchor shadow
    -> SUBP-I sidecar threading through specialize's public API and task roots
    -> SUBP-G bounded portable query and diagnostic projection
    -> SUBP-H additive diagnostic integration
```

Before SUBP-E begins:

- portable anchors reproduce session-local explanations;
- occurrence keys distinguish unrelated owners of one interned poly node;
- required generalized structural positions are complete or explicitly incomplete;
- cache routes have an explicit empty-sidecar behavior;
- no semantic type contains provenance.

Before SUBP-F closes:

- materialized semantic output is byte-identical;
- exact child-path projection is verified for each initial structural family;
- duplicate semantic constraints do not requeue;
- open-variable gaps are enumerated;
- edge and logical-byte budgets are approved;
- scaling tests rule out proof-path combinations.

Before SUBP-I closes:

- every public `specialize` entry point threads the sidecar (or its canonical empty value) without
  behavior change through I-1;
- `InstantiatedScheme`'s `Hash`/`Eq` output is unchanged after I-2;
- at least the def-body, expression-actual, and pattern-input root families show real non-empty
  anchors sourced from actual compilation, not only synthetic test helpers;
- the I-4 site list is recorded, not silently dropped or guessed at.

Before SUBP-H begins:

- portable query results match retained-session controls;
- endpoint explanation policy is approved;
- primary-span and related-site selection are presentation-neutral and deterministic;
- incomplete/cache/import behavior is verified;
- rollback removes only diagnostic integration.

## 12. Compatibility, rollback, and failure policy

SUBP-A through SUBP-G are observational/inert with respect to source-language semantics and public
diagnostic content. They may add sidecar records, metrics, debug APIs, shadow mappings, and optional
opaque error metadata. They must preserve inferred schemes, materialized types, specialize queue
work, errors, emitted programs, runtime behavior, and caches.

If an inert slice changes semantic output:

1. compare infer constraint/bound counts and scheme fingerprints with the characterization baseline;
2. compare materialized `mono::Type`, specialize semantic constraint cardinality, queue order,
   instances, and output;
3. verify no path, anchor, role, or completeness value entered semantic `Hash`/`Eq`;
4. verify provenance-only merging did not enqueue TypeGraph work or mutate open-variable bounds;
5. roll back the slice without updating semantic expectations.

If storage or timing exceeds the approved budget:

1. preserve semantic compilation first;
2. identify whether growth comes from snapshot closure, occurrence fan-in, materialized paths,
   duplicate specialize mappings, or query traversal;
3. verify canonical edge dedup;
4. mark affected provenance incomplete under an explicit budget;
5. never flatten origins or store proof-path combinations as an optimization.

SUBP-H is the only public diagnostic-content change. Its rollback removes failure explanation
projection and rendering while retaining the poly sidecar, shadow TypeGraph mappings, and bounded
portable query for diagnosis.

Cold-only provenance is an explicit compatibility boundary. Lack of explanation on cache-loaded
code is not treated as a compilation error or as evidence that no cause exists.

## 13. Open decisions

The following are decided and must not be reopened as incidental implementation choices:

- the sidecar is poly-owned and adjacent to semantic `poly::Arena`;
- cold-only/same-build provenance is the initial project boundary;
- cache serialization is deferred;
- occurrence keys, not bare interned poly node IDs, establish ownership;
- the shared structural path is poly-owned and layer-neutral;
- CPROV records are exported as a bounded shared graph snapshot, not copied proof trees;
- materialization projects provenance while source and destination positions coexist;
- TypeGraph provenance is adjacent to, and excluded from, semantic subtype identity;
- no unbounded query walker is added;
- incomplete provenance degrades to today's diagnostic.

The following points remain open for the named slices:

1. **Poly-layer escape hatch (SUBP-B).** The default location is `poly::provenance`. If dependency
   layering makes source-site or graph-rule representation impossible without contaminating
   semantic poly types, stop for a design amendment. A separate lower-level provenance crate is the
   approved escape direction, not moving the sidecar back into mutable infer session state.
2. **Snapshot closure and storage budgets (SUBP-B).** Choose exact node, edge, depth, per-anchor
   fan-in, and logical-byte limits from characterization. Decide whether one session-wide multi-root
   closure or partitioned shared chunks gives the smaller bounded artifact without graph copies.
3. **Path details beyond the decided shared type (SUBP-C/E).** Specify record spread,
   union/intersection alternative, invariant neutral-position, runtime function-shape, and recursive
   bound advancement. Missing exact rules remain incomplete.
4. **Container-level witnesses (SUBP-C/F).** Decide the exact witness role for a missing record field
   or variant tag when no child node exists on one side. The model requires a container relation; it
   must not fabricate a payload child.
5. **Open-variable relationships (SUBP-A/F).** Determine whether slot bound insertion/replay can use
   one exact parent edge, needs an ordered multi-parent edge, or must remain incomplete for the first
   integration.
6. **Duplicate specialize provenance settlement (SUBP-F).** Choose canonical parent indirection or a
   bounded provenance-only worklist for late mappings. Semantic requeue is not an option.
7. **Endpoint retention and presentation (SUBP-G/H).** The internal failure witness can retain both
   lower and upper anchors. Decide whether the first diagnostic renders both, chooses one primary
   chain plus related context, or shows one chain when the other is redundant.
8. **Portable source-site encoding (SUBP-B/G).** The high-level representation is module identity
   plus byte range and semantic role. Confirm the exact path/range types that let yulang resolve
   fresh-source text without creating a poly-to-infer dependency.
9. **Public query budget and cause selection (SUBP-G/H).** Choose the diagnostic budget and the
   deterministic policy for multiple complete source causes. Storage retains exact alternates
   regardless of presentation.
10. **Diagnostic wording and primary location (SUBP-H).** Preserve the existing mismatch message;
    decide the additional related-information wording and which complete endpoint, if any, owns the
    primary span.
15. **Container-identity-missing task roots (SUBP-I, deferred as I-4).** `task_solver.rs:58,536` and
    `task_solver/control.rs:283,442,456,489,516` lose the parent record/constructor/lambda identity
    before they construct a subtype root. Decide whether to thread that identity down through pattern
    and lambda solving so these sites can reach `constrain_materialized_subtype`, or accept them as
    permanently-incomplete provenance. Not resolved by SUBP-I proper.

The following are deferred by scope, not open implementation choices:

11. **Cache/build explanation parity.** Serializing and versioning the portable snapshot and
    occurrence sidecar is a future project.
12. **Cross-package imported provenance.** Imported artifacts do not carry their original CPROV
    graph in this project.
13. **Arbitrary public graph exploration.** CLI/LSP graph browsers and user-issued "why this type"
    queries are separate presentation work.
14. **Truth maintenance.** Portable provenance remains append-only explanation data and does not
    make semantic retraction sound.

## 14. Overall project exit criteria

The general subtype explanation bridge is complete only when:

- every initial tuple/record/variant mismatch endpoint has a characterized occurrence owner;
- exact infer canonical records are exported through portable anchors without session-local IDs;
- the portable snapshot shares canonical ancestors and obeys approved hard budgets;
- definition, expression, and pattern occurrence keys distinguish structurally equal unrelated
  owners;
- PUSP generalized paths migrate without changing existing witnesses or diagnostics;
- required non-function generalized positions have exact parents or explicit incompleteness;
- the poly sidecar remains outside semantic poly nodes and cache serialization;
- cache and imported routes install explicit absent/incomplete provenance;
- `SchemeMaterializer` projects ownership during its existing recursion without changing semantic
  types;
- TypeGraph semantic `Hash`/`Eq`, queue admission, work count, slot behavior, and termination remain
  unchanged;
- tuple, record, and variant propagation retain only exact matched structural ownership;
- missing child failures use honest container-level evidence;
- duplicate provenance merges produce no semantic requeue;
- storage grows linearly in exported graph structure and realized mappings;
- no nested proof-path combinations or per-occurrence graph copies exist;
- general failures can retain complete lower/upper portable anchors;
- CPROV-H's bounded traversal explains portable anchors deterministically and cycle-safely;
- query truncation or mapping gaps remain explicit;
- no internal graph or arena identity reaches yulang presentation;
- covered general `UnsatisfiedSubtype` diagnostics identify correct causal source locations;
- unrelated equal types never share causal explanation by accident;
- existing structured subtype origins and primary mismatch wording remain unchanged;
- cache/import/incomplete controls retain today's spanless diagnostic;
- infer, poly, specialize, yulang library, CLI, contract, cache, and performance gates pass;
- removing SUBP-H presentation leaves all provenance infrastructure inert and queryable.

Completion of this project does not claim cache-portable or cross-package provenance. It does not
change subtype validity, specialize scheduling, or semantic type identity. Every implementation
slice requires separate authorization and review.

Investigation and specification design: Codex (gpt-5.6-sol), 2026-07-22 session. Whether and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a feasibility and design specification, not an implementation commitment.

Reference specification approved by Claude Sonnet 5, 2026-07-22 session, with the user's explicit approval. This signature approves the document as a reference specification for future implementation slices — it does not itself authorize implementation of any slice, including Slice SUBP-A. Each slice requires its own explicit scoping and authorization before write-enabled work begins, following this project's established discipline (as used for the constraint-provenance-redesign project's CPROV-A..J slices and the parameter-use-site-provenance project's PUSP-A..F slices).

**Amendment, 2026-07-23 session.** SUBP-A through SUBP-F implemented and pushed (`bbddd3b3`..`9be09b6e`). Attempting to wire SUBP-F's shadow infrastructure into real production call sites (per Section 7.2) surfaced a public-API threading gap not characterized in the original document: the sidecar built through SUBP-D/E never reaches `Specializer2`/`TaskSolver`/`InstantiatedScheme` in production. Investigation was delegated to Codex (gpt-5.6-sol, read-only); Slice SUBP-I (public API and task-root sidecar threading, staged I-1/I-2/I-3, with I-4 explicitly deferred as open decision 15) was designed by Claude Sonnet 5 from that report and inserted into the dependency order between SUBP-F and SUBP-G, following the same per-slice authorization discipline as the rest of this document. Approved by the user's explicit request to proceed with this design.
