# Constraint provenance and derivation graph redesign

Date: 2026-07-21

Status: reference design for a staged constraint-provenance project. This document specifies the
representation, invariants, rollout order, and activation gates, but does not authorize
implementation of any stage. Ordinary-cast semantic activation remains paused until the provenance
coverage and shadow-classification gates in this document are met.

Current-code citations were re-verified against the working tree on 2026-07-21. The working tree may
contain unrelated uncommitted work; line references identify the code shape investigated for this
design and must be rechecked at the start of each implementation slice.

The immediate related specifications are:

- `notes/design/2026-07-21-ordinary-cast-resolution-spec.md`, which defines ordinary value-cast
  cardinality and the infer/specialize activation project;
- `notes/design/2026-07-13-role-impl-method-two-stage-lifecycle.md`, especially Sections 5.1.1 and
  10.2, which previously investigated origin tagging for selective constraint subtraction and
  rejected that use without an independent constraint-representation redesign.

## 1. Purpose and problem statement

This project gives the constraint solver a persistent, append-only account of why each canonical
constraint and bound exists. It has one immediate correctness consumer and one longer-term
explainability goal.

### 1.1 Immediate correctness problem: false ordinary-cast boundaries

The paused OCAST-F activation treated every `NominalCastNeeded` event as a required source-level
ordinary-cast boundary. That assumption is false.

The constraint machine emits `NominalCastNeeded` whenever propagation reaches two distinct nominal
constructors at `crates/infer/src/constraints/machine/propagate.rs:120-132`. The event currently
carries the lower and upper type nodes, constructor paths, and weights, but no identity for the
constraint that produced it and no source-boundary derivation
(`crates/infer/src/constraints/mod.rs:211-242`).

Bounds replay is the concrete false-positive mechanism. When a new lower bound is added to a type
variable, it is paired with every projected upper bound already stored for that variable; when a new
upper bound is added, it is paired with every projected lower bound
(`crates/infer/src/constraints/machine/bounds.rs:262-314`). Those pairs are valid internal
consequences of the solver's bound representation, but they are not all independent requests made by
one source expression.

This distinction was exposed by two regressions:

- `examples/config-file-text/config_read.yu`, where independent `ref`-bound loop accumulators of
  unrelated types were reported as requiring casts between one another;
- `tests/yulang/regressions/runtime/file_mock_text_with_rollback_on_error.yu`, where `&buffer` inside
  `text_with_mock` and caller-local `&store` were reported as a cast pair despite belonging to
  different source scopes and never participating in a direct ref-to-ref assignment.

Both failures arise after bounds from different source obligations coexist at a shared internal
variable and replay forms a lower/upper cross-product. The error is not in ordinary-cast candidate
lookup. It is the loss of the distinction between a source-level boundary and an internal propagated
consequence before `NominalCastNeeded` reaches its consumer.

The immediate requirement is therefore:

> A `NominalCastNeeded` consequence may be classified as an enforceable ordinary-cast boundary only
> when its derivation contains an eligible source-level boundary in the correct proof chain. Mere
> coexistence of its endpoint constructors in one bound component is insufficient.

This document supplements the OCAST specification. It does not alter that specification's
`Missing | Unique | Ambiguous` cardinality rule. It supplies the missing proof that a nominal pair is
actually a source boundary to which that rule may be applied.

### 1.2 Longer-term goal: explain inferred bounds

The same infrastructure should support a bounded read-only query of the form:

```text
why does type variable v have lower bound L?
why does type variable v have upper bound U?
```

The answer should trace the bound through source-origin leaves and solver transformation rules,
rather than only pointing at the final error span. This is analogous in purpose to an inference
explanation that follows contributing expressions through a TypeScript-like inferred type, not to
the existing diagnostic provenance tables that attach source spans to an already-known error kind.

This project does not promise a complete user-facing explanation UI. It establishes the persistent
derivation data and a bounded debug query from which such diagnostics or editor features can later be
built.

### 1.3 Relationship to the prior provenance-subtraction rejection

The 2026-07-13 role-impl lifecycle investigation considered tagging requirement constraints so that
their propagated consequences could later be removed from an inferred method view. It found that an
immediate mutation journal could not identify later mixed replay consequences. A sound origin tag
would have to survive `SubtypeConstraint`, `ConstraintWork`, lower/upper/evidence bounds, subtract
facts, row residual work, events, replay, subsumption, and deduplication
(`notes/design/2026-07-13-role-impl-method-two-stage-lifecycle.md:393-400`).

That design rejected selective provenance subtraction because propagation is not invertible and the
machine has no persistent derivation graph
(`notes/design/2026-07-13-role-impl-method-two-stage-lifecycle.md:661-665`). This project deliberately
takes on the representation work that was out of scope there, but for a narrower semantic contract:

- record forward derivation;
- explain why an extant fact exists;
- classify whether an extant event is backed by an eligible source boundary.

It does **not** remove a fact when an origin is removed. Provenance recording does not make
propagation invertible and does not by itself provide truth maintenance.

## 2. Goals, non-goals, and scope boundary

### 2.1 Required goals

The project must provide:

1. stable identities for canonical subtype constraints, ordinary bounds, evidence bounds, subtract
   facts, and derivation edges within one inference session;
2. a source-origin seam at every root constraint entry point, with an explicit internal/unknown
   fallback during migration;
3. typed derivation rules for structural propagation, bound insertion, replay, row residual work,
   and subsumption;
4. exact binary parentage for bounds replay: one lower-bound record and one upper-bound record joined
   through one pivot variable;
5. origin-aware merging when a semantically duplicate constraint or bound acquires another
   derivation, without requeueing duplicate semantic work;
6. bounded explanation queries over the stored derivation graph;
7. a shadow classifier that distinguishes eligible source boundaries, internal-only consequences,
   and incomplete provenance for `NominalCastNeeded`;
8. measurement proving that provenance does not alter solver output, semantic fixed points, or
   termination.

### 2.2 Explicit non-goals

This project does not include:

- selective constraint subtraction or retraction;
- recomputation after deleting one origin;
- materializing every possible proof path;
- changing subtype, weight-composition, row-reduction, subsumption, or replay semantics;
- changing co-occurrence analysis, polarity elimination, or generalization to protect provenance;
- serializing a derivation graph into compiled schemes or reconstructing provenance across sessions;
- activating missing/ambiguous ordinary-cast errors before the final separately authorized slice;
- building a final CLI, LSP, or playground explanation presentation;
- rescanning CST or source text to recover an origin that lowering failed to register.

### 2.3 Same-session boundary

The provenance graph is session-local. Imported or compiled schemes may enter through an explicit
`UnknownInternal` or imported-summary root, but this project does not serialize their original proof
graphs. Same-session constraints must still retain their full covered derivation even when they
interact with imported types.

## 3. Current constraint lifecycle and the information-loss point

### 3.1 Semantic constraint entry and queueing

`Arena::subtype` currently accepts only `lower` and `upper` and immediately forwards them to the
machine (`crates/infer/src/arena.rs:76-83`). Weighted and batch entry points similarly have no cause
parameter. Inside the machine, `subtype` canonicalizes and drains work immediately
(`crates/infer/src/constraints/machine/entry.rs:195-220`).

`SubtypeConstraint` is exactly `lower`, `upper`, and `weights`
(`crates/infer/src/constraints/mod.rs:553-561`). `ConstraintWork` contains either that value or a
queued subtract fact (`crates/infer/src/constraints/mod.rs:244-261`). Canonicalization erases trivial
relations and normalizes terminal/var-var weights before the resulting value is inserted into the
global `seen` set (`crates/infer/src/constraints/machine/entry.rs:377-430`).

There is no identity between one root request and its later derived work. A derived constraint is
represented only by the same semantic triple as a root constraint.

### 3.2 Bound storage and replay

Each variable stores ordinary and evidence lower/upper bounds as values plus four exact-dedup sets
(`crates/infer/src/constraints/mod.rs:355-413`). Ordinary insertion promotes an equal evidence bound
by removing it from the evidence vector/set and storing it in the ordinary collection
(`crates/infer/src/constraints/mod.rs:292-335`). The stored values retain endpoint and weights, not
the constraint or derivation that created them.

`step_subtype` decomposes structures, inserts bounds at variables, and emits terminal events
(`crates/infer/src/constraints/machine/propagate.rs:4-165`). Each child is enqueued with endpoints and
transformed weights only. Its parent identity and transformation rule are discarded.

On accepted lower or upper insertion, replay enumerates the opposite projected bounds and composes
weights (`crates/infer/src/constraints/machine/bounds.rs:39-128` and `262-314`). Replay currently
prefilters trivial, globally seen, and evidence-only results before actions are materialized
(`crates/infer/src/constraints/machine/bounds.rs:316-343`). A semantically duplicate replay result is
therefore dropped precisely where its additional derivation would need to be recorded.

### 3.3 Events and current consumption timing

Events are stored as endpoint payloads in a vector and extracted with `take_events` by moving the
whole vector (`crates/infer/src/constraints/machine/entry.rs:98-135`). `NominalCastNeeded` is emitted
at the final constructor comparison, after any number of structural and replay transformations, but
the event has no stable constraint record to query.

This creates two timing hazards for provenance:

1. an event can be routed before a semantically duplicate constraint contributes a later derivation;
2. a provenance-only merge can occur without any new semantic queue work, so the existing fixed-point
   signals do not cause the consumer to reconsider an already-routed event.

The intended design is to classify `NominalCastNeeded` eligibility only at constraint quiescence,
after semantic work and pending provenance merges have settled. The feasibility and exact ownership
of that resolution point must be confirmed during Stages C and F; per-generation irreversible
classification is not the intended model.

## 4. Required invariants

### 4.1 Semantic key and provenance are separate domains

The primary invariant is:

> Provenance must never participate in the semantic constraint `Hash`, `Eq`, deduplication key,
> queue-admission key, or termination criterion.

The semantic key remains:

```text
SubtypeConstraintKey = (lower, upper, weights)
```

Its canonicalization, equality, and replay semantics remain unchanged. Provenance is an append-only
record layer associated with the canonical semantic record.

If origin were added directly to `SubtypeConstraint` equality, the same semantic constraint could be
queued once per origin or proof path. Solver work and termination would then depend on origin count,
and cyclic/dense graphs could generate an unbounded family of otherwise identical constraints. That
design is forbidden.

### 4.2 Semantic progress and provenance progress are distinct

The current machine uses global `seen.len()` changes as a result witness in several direct
constraint APIs (`crates/infer/src/constraints/machine/entry.rs:223-272`) and increments
`ConstraintEpoch` for effective solver mutations
(`crates/infer/src/constraints/machine/bounds.rs:130-141`).

Adding a derivation edge to an existing semantic record must not:

- enqueue the semantic constraint again;
- change `seen.len()` or its replacement's semantic cardinality;
- bump `ConstraintEpoch`;
- update a variable's semantic bound epoch;
- report semantic progress to generalization, role solving, or cache reuse.

Provenance receives a separate monotone `ProvenanceEpoch` or equivalent generation counter. Any
provenance-only worklist and quiescence test must be isolated from semantic fixed-point decisions.

### 4.3 Provenance is append-only, not invertible

Once recorded, a source leaf, transformation edge, alternate derivation, or tombstoned bound remains
queryable for the life of the inference session. Pruning a semantic frontier does not delete its
proof record. This supports explanation and classification, not retraction.

### 4.4 Derivations preserve exact parents

Every derived fact records the rule and the exact parent records used for that derivation. A global
set of all origins reachable from a semantic node is not a substitute for the edges that connect
those origins.

For replay specifically, the derivation must retain:

```text
Replay(pivot, lower_bound_record, upper_bound_record) -> constraint_record
```

Flattening the parents to an origin set loses which lower bound paired with which upper bound. That
pairing is exactly the information needed to distinguish a genuine source chain from incidental
co-occurrence at one shared variable.

### 4.5 Explanation is bounded and cycle-safe

The stored structure is a canonical derivation hypergraph, not a materialized list of proof paths.
Derivation edges are explicitly deduplicated. Query traversal has node/edge/depth budgets and a
visited set.

Individual derivation edges point to the exact pre-existing parent witnesses that produced them,
which gives a binary derivation DAG for replay. Canonical semantic records may nevertheless be
connected by cyclic subtype structure after record interning. Queries must therefore treat the
canonical-record projection as a graph and never assume unrestricted recursive tree expansion.

## 5. Decided provenance model

### 5.1 Canonical semantic records

The design introduces small session-local IDs for canonical facts. Exact names remain an
implementation detail, but the representation must support this separation:

```rust
struct SubtypeConstraintKey {
    lower: PosId,
    upper: NegId,
    weights: ConstraintWeights,
}

struct ConstraintRecordId(u32);
struct LowerBoundRecordId(u32);
struct UpperBoundRecordId(u32);
struct SubtractFactRecordId(u32);
struct DerivationEdgeId(u32);
```

The canonical subtype index maps `SubtypeConstraintKey` to `ConstraintRecordId`. Bound and fact
tables similarly map their existing semantic keys to stable records. The records own or reference
their incoming derivation edges; the semantic tables and queues use the IDs without including those
edges in equality.

### 5.2 Source leaves and internal roots

A root origin identifies why a caller requested a constraint. The minimum source taxonomy is:

```text
ApplicationArgument
Annotation
Return
Field
Assignment
Internal
```

During migration, unconverted entry points use `UnknownInternal`. `UnknownInternal` is coverage debt,
not evidence that a source-level cast boundary exists. The taxonomy may gain more source categories
through the open decision in Section 13, but it must not use file, module, function, variable, or
fixture names as semantic classification.

A source leaf must carry a stable same-session source-boundary ID. Spans and expression/definition
identity remain metadata behind that ID, not part of constraint equality.

### 5.3 Typed derivation edges

Transformation rules must be typed rather than free-form strings. The initial rule family needs at
least:

- root source request and unknown/internal root;
- stack/non-subtract normalization;
- union branch and intersection branch;
- function argument, argument-effect, return-effect, and return decomposition;
- invariant constructor argument expansion;
- tuple, record, variant, and row decomposition;
- lower-bound and upper-bound insertion;
- evidence-bound insertion or promotion;
- binary lower/upper replay with pivot variable;
- row residual creation/reuse and unweighted row reduction;
- filter/payload invariant generation;
- subtract-fact introduction/use;
- semantic duplicate, trivial, equivalent, and subsumed outcomes where an alternate proof would
  otherwise disappear.

Rule payloads may contain structural indices, a pivot variable, a residual record, or another stable
record ID. They must not duplicate whole source trees or unconstrained debug strings.

### 5.4 Binary replay derivation DAG

Bounds replay uses the binary derivation strategy. Each replay action records the exact lower-bound
record and exact upper-bound record, plus their pivot variable and the resulting canonical constraint
record.

This is a decided point. A flattened set of source origins is not an acceptable replacement because
it cannot answer whether a particular lower proof was paired with a particular upper proof. Replay
classification must be able to follow each parent independently and preserve alternate binary
pairings when they yield the same semantic result.

The graph stores canonical records and deduplicated hyperedges; it does not enumerate the Cartesian
product of complete parent proof paths. One replay pairing contributes one binary hyperedge. Parent
records may themselves have several incoming derivations, which remain shared graph structure.

### 5.5 No full proof-path materialization

Full unbounded proof-path enumeration is explicitly out of scope. Cyclic and dense constraint graphs
can contain exponentially many paths even when the number of semantic facts is bounded. The
implementation stores:

- one canonical record per semantic constraint/bound/fact;
- a deduplicated set of typed incoming derivation edges;
- references from each edge to canonical parent records or immutable witness records;
- bounded traversal summaries only when a consumer asks a question.

If measurement shows that retaining every distinct derivation edge is itself too large, an explicit
edge-budget or summary policy must be approved under Section 13. It must report incomplete provenance
rather than silently treating dropped evidence as internal-only or source-eligible.

## 6. Nominal-cast eligibility model

### 6.1 Shadow-classification vocabulary

The provenance consumer for ordinary casts uses three states:

```text
EligibleSourceBoundary
InternalOnly
Incomplete
```

- `EligibleSourceBoundary` means the event's exact derivation contains a recognized source boundary
  whose typed relation is eligible for ordinary-cast enforcement.
- `InternalOnly` means every covered derivation shows that the nominal comparison was introduced
  only by internal propagation, including incidental bound co-occurrence. Its parents may ultimately
  descend from source syntax, but no single eligible source boundary owns the lower-to-upper relation
  represented by this nominal comparison.
- `Incomplete` means at least one required root, transformation, replay parent, pruned fact, or edge
  is not covered strongly enough to prove either of the first two states.

This classification answers whether ordinary-cast resolution should be consulted. It does not
replace `Missing | Unique | Ambiguous`, choose a cast declaration, or change cast cardinality.

### 6.2 A source leaf alone is not sufficient

Many internal facts ultimately descend from some source syntax. Eligibility therefore cannot mean
"any reachable source span exists." A source-boundary leaf identifies a requested relation, not just
an expression that contributed one endpoint. The query must retain the typed path from that specific
boundary relation through structural decomposition and replay to the nominal mismatch. Binary replay
parentage is what prevents separate source obligations behind unrelated lower and upper bounds from
being flattened into one apparently source-backed event.

The exact source-boundary eligibility predicate is activated only after Stage I shadow evidence. It
must be structural and boundary-kind based. It must not inspect user names or fixture paths.

### 6.3 Quiescent classification

`take_events` currently removes events as soon as the consumer asks for them
(`crates/infer/src/constraints/machine/entry.rs:133-135`). A semantic duplicate can later add an
alternate derivation without adding semantic work. Permanently classifying the first event at its
emission time could therefore observe an incomplete graph.

The intended policy is:

1. record a pending nominal event keyed by its canonical constraint record;
2. drain semantic work;
3. settle any provenance-only merge work to the same resolution boundary;
4. classify the canonical record at constraint quiescence;
5. expose or route the classification once for that quiescent graph state.

Stage C must establish where the source-boundary ID is created, and Stage F must prove that duplicate
replay derivations arriving after first semantic insertion are visible before classification. If the
current session lifecycle has no safe quiescent routing point, implementation stops for a design
amendment rather than reverting to per-event classification.

## 7. Required changes at the nine propagation touchpoints

### 7.1 Touchpoint 1: `SubtypeConstraint`

**Current state.** `SubtypeConstraint` directly derives `Hash`/`Eq` over `lower`, `upper`, and
`weights` (`crates/infer/src/constraints/mod.rs:553-561`). Canonicalization returns this value and the
global `seen` set owns it (`crates/infer/src/constraints/machine/entry.rs:377-430`).

**Required change.** Make the semantic triple an explicit `SubtypeConstraintKey`, intern it once,
and represent queued/derived identity with `ConstraintRecordId`. The constraint record stores the
key and incoming derivation-edge references. Root creation adds a source/internal leaf edge; derived
creation adds a typed transformation edge.

**Semantic isolation.** Canonicalization and `Hash`/`Eq` remain defined only on the key. Adding an
incoming derivation to an existing record is provenance progress, not a new constraint and not a
queue admission.

### 7.2 Touchpoint 2: `ConstraintWork`

**Current state.** The queue owns `ConstraintWork::Subtype(SubtypeConstraint)` or
`ConstraintWork::SubtractFact(QueuedSubtractFact)` (`crates/infer/src/constraints/mod.rs:244-261`).
`drain` pops each item and dispatches it immediately
(`crates/infer/src/constraints/machine/entry.rs:339-363` and `486-493`).

**Required change.** Subtype work carries a `ConstraintRecordId`; subtract work carries a stable fact
record or an equivalent tracked work ID. `step_subtype` obtains the immutable semantic key from the
record and emits child derivation edges that point back to the parent record and rule.

Root enqueue and derived enqueue should be distinct APIs even if they share canonical interning. A
root API requires an `OriginId`; a derived API requires a rule plus parent record IDs. This prevents
`UnknownInternal` from being applied accidentally to a child whose parent is known.

**Semantic isolation.** Queue membership remains one item per newly admitted semantic constraint.
Provenance-only merges do not append `ConstraintWork::Subtype` and do not affect drain work counts.

### 7.3 Touchpoint 3: lower, upper, and evidence bounds

**Current state.** `VarBounds` stores four bound vectors and four exact-dedup sets
(`crates/infer/src/constraints/mod.rs:355-368`). `WeightedLowerBound` and `WeightedUpperBound` carry
only endpoint and weights (`crates/infer/src/constraints/mod.rs:401-413`). Equal evidence bounds are
removed when an ordinary bound is inserted (`crates/infer/src/constraints/mod.rs:292-335`).

**Required change.** Introduce stable lower/upper bound records. Active ordinary and evidence
frontiers store record IDs; a semantic bound index maps the existing endpoint/weight key to its
canonical record. Each record retains:

- bound direction, owning variable, endpoint, and weights;
- ordinary/evidence/active/tombstone state as appropriate;
- incoming insertion, replay-evidence, promotion, or equivalence derivations.

A duplicate bound merges a new derivation edge into the canonical bound record. Promotion from
evidence to ordinary must preserve the stable record and its old derivations, changing frontier state
rather than deleting and recreating history.

**Semantic isolation.** The active projected bound sequence, exact semantic dedup, replay eligibility,
and mutation epochs must remain behavior-identical. A provenance-only duplicate merge must not emit
another `LowerBoundAdded`/`UpperBoundAdded`, run replay again, or bump the semantic bound epoch.

### 7.4 Touchpoint 4: subtract facts

**Current state.** `SubtractTable` maps a type variable to a `Vec<SubtractFact>` and deduplicates with
`Vec::contains` (`crates/infer/src/constraints/mod.rs:415-450`). A queued fact contains effect and
fact; accepted facts bump the semantic epoch and emit `SubtractFactAdded`
(`crates/infer/src/constraints/machine/entry.rs:288-320` and `495-509`). Declared subtract IDs are
tracked separately in `declared_subtracts`.

**Required change.** Intern subtract facts as stable `SubtractFactRecordId` values under their current
semantic key. The fact record retains root declaration/import/internal provenance and later uses by
weight, filter, row reduction, or payload-invariant generation. Declared membership must be linked to
the source declaration origin rather than represented only as an unprovenanced `SubtractId` set.

Weights continue to carry semantic `SubtractId` values; they do not grow provenance fields. A
derivation edge records which fact record justified a transformation that interprets a weight.

**Semantic isolation.** Duplicate fact provenance merges do not bump `ConstraintEpoch`, re-emit
`SubtractFactAdded`, or rerun semantic work. Existing declaration-versus-inferred subtract behavior
and generalization pruning remain unchanged.

### 7.5 Touchpoint 5: row residual work

**Current state.** Weighted row processing derives retained items and a residual weight, interns a
fresh gamma by `RowResidualKey`, and enqueues source-to-row and gamma-to-tail constraints
(`crates/infer/src/constraints/row_effect.rs:6-85`). Unweighted row reduction scans multiple existing
lower bounds, stores a reduced upper without ordinary replay, and enqueues per-lower consequences
(`crates/infer/src/constraints/row_effect.rs:87-185` and `204-241`). Filter and subtractability helpers
can emit further invariant constraints and filter-violation events.

**Required change.** Give each residual construction/reuse a stable residual record and derive each
enqueued constraint from the exact input constraint, bound records, subtract facts, retained-item
decision, and residual rule. Reusing a gamma must add the specific new derivation for that input; it
must not union every origin ever associated with the gamma into every gamma edge.

Unweighted reduction may depend on several lower bounds. The general graph therefore permits
multi-parent hyperedges for transformations that genuinely consume multiple records, even though
replay itself remains exactly binary. Row-item matching, filter-generated invariants, payload
invariants, and the `store_upper_bound_without_replay` path must not bypass provenance coverage.

**Semantic isolation.** `RowResidualKey` and gamma reuse semantics remain unchanged. Origin is not
part of the residual key. Multi-parent derivation recording must not cause another reduction or
change which lower bounds are matched.

### 7.6 Touchpoint 6: events

**Current state.** Events carry copied endpoints and weights, not producer records
(`crates/infer/src/constraints/mod.rs:211-242`). Lower/upper events are emitted at bound insertion
(`crates/infer/src/constraints/machine/bounds.rs:39-128`), and `NominalCastNeeded` is emitted at the
distinct-constructor terminal (`crates/infer/src/constraints/machine/propagate.rs:120-132`).

**Required change.** Every constraint-derived event carries the producing `ConstraintRecordId`,
bound record ID, fact record ID, or another stable producer ID. Existing endpoint payloads may remain
temporarily for compatibility, but provenance queries use the record identity. Nominal events are
deduplicated by canonical semantic record and held for quiescent classification.

If a late provenance merge changes a pending record's classification, the resolution boundary must
observe it through canonical graph indirection or a provenance-only worklist. It must not depend on
re-emitting the semantic event.

**Semantic isolation.** Event record IDs are observational metadata. Lower/upper/fact event count and
solver scheduling remain unchanged until a separately authorized consumer activation. Nominal event
routing timing may change only in the dedicated quiescence slice and must preserve pre-activation
compiler behavior.

### 7.7 Touchpoint 7: replay

**Current state.** A new lower is crossed with all projected uppers and a new upper with all projected
lowers (`crates/infer/src/constraints/machine/bounds.rs:262-314`). The replay snapshot stores only
canonical `SubtypeConstraint` values (`crates/infer/src/constraints/machine/bounds.rs:5-21`). Exact
duplicates are discarded during prefilter or application
(`crates/infer/src/constraints/machine/bounds.rs:316-343` and `465-499`).

**Required change.** `BoundReplayPlan` and each replay action carry:

```text
pivot TypeVar
lower BoundRecordId
upper BoundRecordId
result ConstraintRecordId or result semantic key pending interning
replay rule/polarity metadata
```

When the result is semantically new, interning records the binary replay edge and queues the result
once. When the result is already globally seen, replay still records and deduplicates the binary
derivation edge against the existing canonical record, but does not queue it. When the result is
trivial or routed to evidence-only storage, the disposition must still have a stable explanation
record sufficient to prove why the path was dropped or represented as evidence.

The edge identity is based on result record, replay rule, pivot, and exact lower/upper parent record
IDs. It is not based on flattened source-origin sets and not on every combination of parent proof
paths.

This makes the false-positive distinction queryable:

- a genuine source chain can retain the source-boundary leaf and the exact lower/upper transformations
  that connect that boundary to the nominal result;
- incidental co-occurrence is represented as a replay edge whose lower and upper parents descend
  from separate obligations without one eligible boundary spanning their pairing.

Replay remains a semantically valid transitive consequence. Provenance does not suppress replay or
declare the consequence invalid. It only prevents that internal consequence from being mistaken for
an independently enforceable source cast boundary.

**Semantic isolation.** Weight composition, opposite-bound enumeration order, replay frontier,
evidence-only routing, duplicate prefiltering, and queue admission remain unchanged. Recording a new
edge for a duplicate result is provenance work only.

### 7.8 Touchpoint 8: subsumption and pruning

**Current state.** Upper-bound insertion can return early when an existing bound subsumes it, and can
prune active row uppers before insertion (`crates/infer/src/constraints/machine/bounds.rs:83-100` and
`505-617`). Alias-cycle checks similarly discard var bounds. Row upper reduction has a separate
store-without-replay path (`crates/infer/src/constraints/row_effect.rs:204-241`). These boolean/early
return paths do not preserve why the candidate was equivalent, subsumed, or pruned.

**Required change.** Subsumption helpers return a structured disposition such as:

```text
Inserted(record)
EquivalentTo(record)
SubsumedBy(record)
Trivial(reason)
```

The discarded candidate's derivation is linked to the surviving canonical record or to a stable
tombstone/disposition record. Bounds removed from the active frontier by pruning become tombstones in
the provenance store; their descendants and earlier event identities remain valid.

**Semantic isolation.** Active bound vectors and subsumption decisions stay exactly as today.
Tombstones are not projected bounds and never participate in replay. Recording an equivalence or
subsumption edge must not reactivate pruned semantic work.

### 7.9 Touchpoint 9: deduplication

**Current state.** `ConstraintMachine::seen` is `FxHashSet<SubtypeConstraint>`
(`crates/infer/src/constraints/mod.rs:50-73`). `enqueue_canonical_subtype` inserts the complete value
and queues only on first insertion (`crates/infer/src/constraints/machine/entry.rs:421-430`). Bounds
have analogous per-direction exact sets.

**Required change.** Replace the global set conceptually with:

```text
FxHashMap<SubtypeConstraintKey, ConstraintRecordId>
```

The first semantic insertion allocates a record and may queue it. A later identical key resolves to
the same record and merges a new derivation edge. Bounds and facts use the same semantic-index plus
record pattern. Derivation edges have their own exact dedup key, minimally:

```text
(result record, rule, ordered parent record IDs, pivot/projection payload)
```

Structurally identical constraints with different origins must merge; keeping them as separate
semantic records would multiply queue work and make termination origin-dependent. Merging only a
flattened origin set is also insufficient because it destroys proof pairing.

**Semantic isolation.** The semantic map's key cardinality replaces `seen.len()` wherever the current
code observes semantic progress. Derivation-map cardinality is observed only by
`ProvenanceEpoch`/provenance metrics. Exact semantic duplicates remain duplicate for solver timing
even when they add a new proof edge.

## 8. Fixed-point and lifecycle requirements

### 8.1 Separate provenance quiescence

The machine needs a monotone provenance generation distinct from `ConstraintEpoch`. It may be a
counter, an explicit provenance work queue, or both. The required contract is:

- semantic work reaches its existing fixed point under unchanged keys;
- derivation edges produced by that work are interned;
- late edges that require summary propagation reach provenance quiescence;
- no provenance-only change is reported as a semantic mutation;
- a query or nominal classification runs only against a declared settled generation.

Whether canonical-graph indirection alone is sufficient or a provenance-only worklist is required is
an open Stage E/F decision. The public invariant is not open.

### 8.2 Source-entry ordering

`Arena::subtype` has no origin parameter today (`crates/infer/src/arena.rs:76-95`). Stage C must add a
new entry seam and migrate callers without forcing origin data into semantic keys.

Application lowering has a specific ordering problem. `make_source_app` calls `make_app`, and
`make_app` creates the function subtype constraints before `make_source_app` registers
`ApplicationProvenanceTable` metadata (`crates/infer/src/lowering/expr/tail.rs:421-490`). A source
application boundary ID must therefore be allocated before constraint creation, or attached through
a stable pending handle after creation without losing the root record. Reconstructing it later from
the expression tree is forbidden; the table itself documents that source ownership is captured only
while CST nodes are available (`crates/infer/src/lowering/application_provenance.rs:7-23`).

### 8.3 Imported provenance

No stage requires serialization of record IDs, derivation edges, or source leaves into poly schemes,
caches, or compiled artifacts. Imported constraints use an explicit incomplete/imported/internal
origin according to the Stage C taxonomy. Stage I measurements must keep imported-unknown cases
separate from fully covered same-session cases so that activation policy is not inferred from a mixed
bucket.

## 9. Performance and storage policy

Changing the semantic index from `FxHashSet<SubtypeConstraint>` to
`FxHashMap<SubtypeConstraintKey, ConstraintRecordId>` is expected to be low cost: the key hash is the
same semantic triple and the value is a small integer. Record indirection and bound-ID vectors add a
smaller constant factor that must still be measured.

The dominant new risk is derivation-edge storage during replay. Replay already exposes generated,
accepted, evidence-only, duplicate, trivial, and prefiltered counts in `ConstraintTiming`
(`crates/infer/src/constraints/timing.rs:37-77`) and records per-lower/per-upper aggregates and maxima
at `crates/infer/src/constraints/timing.rs:199-268`. Stage A extends this instrumentation with at
least:

- canonical constraint/bound/fact record counts;
- derivation edges considered, inserted, and deduplicated;
- replay derivation edges inserted for semantically duplicate results;
- maximum incoming edges per canonical record;
- provenance-only work items and generations, if a worklist exists;
- explanation query nodes/edges visited, budget exhaustion, and maximum depth;
- provenance bytes or a stable allocation proxy.

The design forbids:

- one semantic queue item per origin;
- copying complete origin sets into every replay result;
- expanding all combinations of parent proof paths;
- rebuilding a source index per query;
- unbounded recursive explanation formatting;
- silently dropping edges and then classifying the record as complete;
- using provenance cardinality as a solver termination guard.

If edge storage exceeds the budget chosen in Section 13, the system must preserve semantic behavior
and mark affected provenance `Incomplete`. It must not change replay, subsumption, or dedup semantics
to reduce explanation cost without a separate design amendment.

The derivation-edge storage budget is decided as follows:

- one inference session may retain at most 64 MiB of replay derivation logical-byte proxy;
- one canonical constraint record may retain at most 4,096 incoming replay derivations;
- the proxy charges `size_of::<BinaryReplayDerivation>()` for a canonical edge, twice that size when
  an evidence-only replay edge is retained on both bound records, and the arena plus hash-index
  key/value sizes for a trivial replay drop;
- exceeding either limit stops only the affected new provenance insertion. Semantic constraint
  interning, replay, queue admission, events, bounds, subsumption, and dedup continue unchanged;
- an affected canonical record is marked `Incomplete`; evidence bounds receive an explicit
  incomplete replay derivation marker; and the session records that some replay provenance is
  incomplete. Existing retained edges are not discarded.

This policy was chosen from CPROV-F measurements on repository std lowering. A
`BinaryReplayDerivation` is 16 bytes and the 880,497 replay pairings have a 17.023 MiB logical-byte
proxy. Capacity slack, the added per-record vector header, the enlarged bound-derivation enum, and
the trivial-drop hash index bring the stable requested-storage estimate to about 31.286 MiB before
allocator metadata. Non-empty canonical records have median incoming fan-in 5, p95 27, p99 30, and
maximum 1,285. Across all five characterization entries, replay edges per canonical constraint range
from 6.0645 to 6.1612. The 64 MiB session budget is 3.76 times the measured std proxy; the 4,096
per-record limit is 3.19 times the observed maximum and over 136 times p99. These limits preserve
complete provenance for the characterized workloads while bounding cross-product pathologies.

## 10. Implementation stages and slices

All Rust changes are deferred to follow-up tasks. The slices follow the established pattern:
characterize, introduce inert identity, migrate origins and transformations, complete graph coverage,
add debug queries, shadow the intended semantic consumer, and activate only in a final separate
slice.

### Slice CPROV-A: semantic and replay characterization

Size: S-M. Risk: low.

Capture baseline counts on representative regression fixtures, full std lowering, and the two known
false-positive repros. Record:

- canonical semantic constraints and duplicate admissions;
- ordinary/evidence lower and upper bounds;
- subtract facts and row residuals;
- lower/upper replay inputs, generated, accepted, evidence-only, duplicate, trivial, and prefiltered
  outcomes;
- nominal-cast event count and constructor pairs;
- compile/check output hashes or golden output sufficient to prove zero behavior change.

This slice adds characterization and instrumentation only. It adds no record IDs, origin fields, or
consumer classification.

Exit witness: one checked-in report or test surface records baseline counts for fixtures plus std,
including `config_read.yu` and `file_mock_text_with_rollback_on_error.yu`; all compiler outputs and
existing tests are unchanged.

### Slice CPROV-B: semantic key and record-ID split

Size: M. Risk: high.

Introduce `SubtypeConstraintKey`, `ConstraintRecordId`, and a semantic-key-to-record-ID map with an
empty provenance payload. Queue subtype record IDs instead of owned constraint values. Preserve
canonicalization and every semantic equality decision. Adapt all current `seen.len()` observers to
the semantic map's key count.

Do not add source origins or derivation edges. This slice proves that stable identity alone can be
introduced without changing solver behavior.

Exit witness: solver output is byte-identical on the Stage A corpus; semantic counts, queue work,
replay results, event payload behavior, and termination are identical; no provenance consumer exists.

### Slice CPROV-C: root origin seam

Size: M-L. Risk: high.

Add an opaque `OriginId`/`SourceBoundaryId` parameter to constraint root entry points, including
`Arena::subtype`, weighted/batch variants, and direct helper seams. Unmigrated callers use explicit
`UnknownInternal`. Add source-boundary leaf records and coverage counters, but no classifier.

Bridge the `make_app`/`make_source_app` ordering by allocating a source application boundary before
the corresponding constraints or by another reviewed stable-handle mechanism. Characterize possible
integration with `ApplicationProvenanceTable` and `SelectionProvenanceTable`; do not conflate their
span ownership with the solver's derivation graph by accident.

Confirm a feasible quiescent resolution point for nominal eligibility. If no such lifecycle point
exists, stop before later slices and amend this specification.

Exit witness: every root constraint is counted by origin kind; converted source applications and
annotations retain stable boundary IDs; unknown coverage is reported; semantic output and event
routing remain unchanged.

### Slice CPROV-D: unary structural propagation and event identity

Size: L. Risk: high.

Make `step_subtype` carry parent constraint record and typed rule into every unary or per-child
structural consequence: stack normalization, union/intersection branches, function positions,
constructor invariance, records, variants, tuples, and row item decomposition. Events carry producer
record IDs. No event consumer changes behavior.

Multi-parent cases may remain explicitly incomplete only if enumerated by coverage counters and
reserved for Slice G. Unknown rule fallbacks must be visible in the characterization output.

Exit witness: covered direct structural paths can be traced from child record to root leaf; event
record IDs resolve to the same endpoint payloads; unknown transformation counts are bounded and
explained; compiler output remains identical.

### Slice CPROV-E: stable bound and subtract-fact records

Size: L. Risk: very high.

Replace raw active bound/fact values with stable canonical records while preserving their semantic
indexes and active order. Cover ordinary bounds, evidence bounds, evidence-to-ordinary promotion,
subtract facts, declaration identity, duplicate provenance merge, and fact use by weights/filters.
Introduce `ProvenanceEpoch` and prove that duplicate provenance does not change `ConstraintEpoch`,
bound epochs, method-role mutation output, or semantic progress APIs.

Choose the late-provenance propagation mechanism—canonical graph indirection, provenance-only
worklist, or a bounded combination—before this slice closes.

Exit witness: bound/fact queries return stable IDs and root/parent derivations; promotion preserves
identity; duplicate origins merge without replay or semantic events; semantic vectors, projected
bounds, epochs, and compiler output match Stage A.

### Slice CPROV-F: binary replay provenance

Size: L-XL. Risk: very high.

Replace raw replay actions with tracked actions containing exact lower/upper bound parents and pivot.
Record one deduplicated binary derivation edge for every replay pairing disposition. A semantically
duplicate result records its edge against the canonical constraint without queueing. Evidence-only
replay either receives full provenance here or remains explicitly incomplete under the decision in
Section 13.

Settle late duplicate edges before quiescent nominal classification would run. Extend replay metrics
to quantify derivation-edge cost and duplicate-result edge volume.

Exit witness: a debug graph distinguishes the lower and upper parents of every covered replay result;
the two false-positive repros retain separate obligation chains rather than a flattened shared origin;
semantic replay counts, queue work, outputs, and termination remain identical.

### Slice CPROV-G: row, subsumption, and pruning completion

Size: XL. Risk: very high.

Cover weighted residual creation/reuse, unweighted row reduction, recursive lower consumption,
row-item matching, filter/payload invariant generation, subtract-fact transformations, evidence-only
paths deferred from Slice F, and every subsumption/pruning early return. Introduce structured
subsumption dispositions. Preserve pruned/equivalent bounds as provenance tombstones while keeping
them outside active replay frontiers.

This slice closes coverage gaps; it must not change row or effect semantics.

Exit witness: the Stage A corpus has no unexplained propagation path in the categories required for
nominal classification; tombstoned records remain queryable; active bounds, row residuals, events,
generalized schemes, and output remain behavior-identical.

### Slice CPROV-H: bounded read-only explanation API

Size: M. Risk: medium.

Add debug-only queries such as:

```text
why_lower_bound(var, bound_record, budget)
why_upper_bound(var, bound_record, budget)
why_constraint(constraint_record, budget)
```

Queries return typed graph nodes/edges, source leaves, completeness state, and truncation reason. They
must be deterministic under a defined stable ordering and cycle-safe under explicit node/edge/depth
budgets. No public diagnostic or editor surface is activated.

Exit witness: focused tests explain root, unary decomposition, duplicate derivation, binary replay,
row multi-parent, evidence promotion, subsumed, and tombstoned examples; budget exhaustion returns
`Incomplete`/truncated metadata without affecting inference.

### Slice CPROV-I: OCAST shadow eligibility classifier

Size: M-L. Risk: high.

At the quiescent resolution point, classify each `NominalCastNeeded` producer record as
`EligibleSourceBoundary`, `InternalOnly`, or `Incomplete`. Run the classifier beside current
permissive ordinary-cast behavior. It must not emit a new error, suppress a constraint, instantiate a
different cast, or alter specialization.

The comparison corpus includes:

- `config_read.yu` and `file_mock_text_with_rollback_on_error.yu` as known internal false positives;
- source-level missing-cast characterization cases from the ordinary-cast project;
- the str/path fixtures already repaired by explicit conversions, which should no longer rely on a
  missing cast;
- source annotations, returns, fields, assignments, and application arguments;
- imported/unknown provenance cases, reported separately as incomplete.

Exit witness: known false positives classify `InternalOnly`; known genuine source boundaries classify
`EligibleSourceBoundary`; coverage gaps classify `Incomplete` rather than being guessed; repeated and
late-merged events receive a stable quiescent result; performance and provenance coverage gates are
recorded for Stage J review.

### Slice CPROV-J: OCAST semantic activation

Size: S-M. Risk: critical.

This is a separate follow-up slice requiring explicit authorization. Activate ordinary-cast
`Missing | Unique | Ambiguous` enforcement only for the eligibility states allowed by the approved
policy. The policy for `Incomplete`/unknown provenance—fail open or fail closed—is an explicit open
decision and is not resolved by this document.

Activation must retain the ordinary-cast specification's classifier and diagnostic rules. It must not
add fixture/name-based exceptions or infer source eligibility from constructor shape alone.

Exit witness: the false-positive ref repros do not produce cast diagnostics; genuine missing and
ambiguous source boundaries produce the approved diagnostics; unique casts remain unchanged; the
full ordinary-cast, constraint, std, CLI, contract, cache, and performance gates pass under the
approved incomplete-provenance policy.

## 11. Slice dependencies and activation gates

The required order is:

```text
CPROV-A characterization
    -> CPROV-B semantic identity split
    -> CPROV-C root origins
    -> CPROV-D unary propagation and event IDs
    -> CPROV-E bound/fact records and provenance epoch
    -> CPROV-F binary replay provenance
    -> CPROV-G row/subsumption completion
    -> CPROV-H explanation query
    -> CPROV-I OCAST shadow classifier
    -> CPROV-J separately authorized semantic activation
```

Some code preparation may be divided into independently reviewable commits, but the semantic order
does not change. In particular:

- replay provenance must not precede stable bound records;
- nominal shadow classification must not precede root taxonomy, structural propagation, bound
  identity, replay, duplicate merging, and required row/subsumption coverage;
- explanation-query success on a few direct cases is not proof that OCAST eligibility is complete;
- semantic activation must not be bundled with provenance infrastructure.

Before CPROV-I closes:

- every eligible source-boundary category used by the classifier has a characterized root seam;
- semantically duplicate replay results retain alternate derivation edges;
- late provenance merges are visible at the quiescent classifier boundary;
- incomplete coverage is measurable and never silently mapped to `InternalOnly`;
- the two known false positives and known genuine cast requests are separated by structure, not name;
- provenance cost is within the approved budget.

Before CPROV-J begins:

- the `Incomplete` fail-open/fail-closed policy is explicitly approved;
- OCAST shadow results are stable across cold/warm/cache routes in supported same-session scope;
- no provenance field participates in semantic equality or progress;
- ordinary-cast activation and rollback are a separate diff from provenance recording.

## 12. Compatibility, rollback, and failure policy

CPROV-A through CPROV-I are observational/inert with respect to source-language semantics. They may
add memory, timing, debug APIs, and shadow records, but must preserve inferred types, generalized
schemes, diagnostics, emitted programs, runtime behavior, and solver termination.

If an inert slice changes semantic output:

1. compare semantic key cardinality, active bound order, replay counts, epochs, and event count with
   the Stage A baseline;
2. verify that origin did not enter a semantic `Hash`/`Eq`, residual key, subsumption rule, or replay
   frontier;
3. verify that a duplicate provenance merge did not enqueue semantic work or bump a semantic epoch;
4. roll back the slice while retaining characterization evidence;
5. do not update test expectations to accept the changed semantic output.

If storage or query cost exceeds the approved limit:

1. preserve semantic constraint behavior first;
2. identify whether growth comes from replay edge candidates, duplicate alternate edges, row
   multi-parent edges, or query traversal;
3. add an explicit, measurable completeness/budget policy only after review;
4. never collapse replay to a flattened origin set as a performance shortcut;
5. never drop provenance silently and classify the result as complete.

CPROV-J is the first semantic change. Its rollback must restore permissive OCAST behavior while
retaining the provenance graph and shadow observations for diagnosis.

## 13. Open decisions

The binary replay parent model, semantic/provenance separation, no full path enumeration,
append-only scope, and same-session boundary are decided and must not be reopened as incidental
implementation choices. The following points remain open until the named slice:

1. **Non-replay multi-parent fidelity (before CPROV-D/G).** Replay always retains both exact parents.
   Decide whether union/intersection/tuple decomposition remains one parent plus a child index, and
   exactly which row, invariant, or aggregation rules require all contributing parents rather than a
   single witness.
2. **Source boundary taxonomy (before CPROV-C closeout).** The minimum categories are application
   argument, annotation, return, field, assignment, and internal. Decide whether pattern binding,
   constructor payload, handler/effect boundary, explicit cast, or other structured categories are
   required for complete coverage.
3. **Late provenance merge mechanism (during CPROV-E/F).** Choose canonical-graph indirection,
   provenance-only worklist, or a bounded hybrid. The result must settle before quiescent
   classification and must not report semantic progress.
4. **Derivation-edge storage budget — resolved.** Use the 64 MiB session logical-byte proxy and
   4,096 incoming replay edges per canonical record decided in Section 9. Budget exhaustion marks
   the affected provenance and session `Incomplete` while semantic work continues unchanged.
5. **Explanation-query budget and ordering (before CPROV-H).** Choose node, edge, and depth defaults;
   decide whether queries return one deterministic witness first or all stored contributors within
   budget. This does not change replay's requirement to store exact binary pairings.
6. **Evidence-only replay coverage (before CPROV-F).** Decide whether the optimized evidence-only path
   receives full derivation edges in CPROV-F or is explicitly incomplete until CPROV-G.
7. **Existing source provenance tables (during CPROV-C).** Decide whether
   `ApplicationProvenanceTable` and `SelectionProvenanceTable` are registries behind source-leaf IDs
   or remain separate span tables referenced by a new registry. Do not duplicate source ownership or
   make those tables semantic solver dependencies.
8. **Incomplete OCAST policy (before CPROV-J).** Decide whether `Incomplete`/`UnknownInternal` is fail
   open, fail closed, or split by boundary kind. This is a source-semantic policy and cannot be
   inferred from shadow counts alone.

The following are deferred by scope, not awaiting implementation choices:

9. **Cross-session proof serialization.** Imported/compiled schemes do not carry full derivation
   graphs in this project.
10. **Selective constraint subtraction.** Removing a source origin and retracting only its semantic
    consequences requires truth maintenance or recomputation. Append-only provenance does not make
    that operation sound.
11. **Public explanation UX.** CLI/LSP/playground rendering, source related-information layout, and
    user-facing wording follow only after the bounded debug API proves the graph useful.

## 14. Overall project exit criteria

The constraint-provenance project is complete only when:

- semantic constraint, bound, fact, queue, replay, subsumption, row, and event behavior remains
  unchanged through all inert slices;
- semantic keys and provenance records are structurally separate, and no provenance value enters a
  semantic dedup or termination key;
- every same-session root constraint has a classified source/internal/unknown origin;
- structural propagation carries typed parent rules;
- ordinary/evidence bounds and subtract facts have stable records and preserve duplicate origins;
- replay records exact lower and upper bound parents even when its semantic result is duplicate and
  not requeued;
- row residual, filter/payload, subsumption, pruning, and tombstone paths meet the approved coverage
  floor;
- semantic and provenance epochs are independent;
- bounded `why_constraint`, `why_lower_bound`, and `why_upper_bound` queries are deterministic,
  cycle-safe, and honest about incompleteness;
- quiescent OCAST shadow classification separates the two known ref false positives from genuine
  source cast boundaries without source-name or fixture-path special cases;
- derivation-edge and query costs satisfy the approved budgets on fixtures plus std;
- imported/cross-session incompleteness is explicit and not confused with internal-only proof;
- CPROV-J, if separately authorized, uses the approved incomplete-provenance policy and passes the
  ordinary-cast semantic gates;
- no selective subtraction, truth-maintenance claim, full proof-path enumeration, or cross-session
  serialization was smuggled into the project.

Completion of CPROV-A through CPROV-I does not by itself authorize or complete ordinary-cast semantic
activation. Completion of CPROV-J does not claim that arbitrary origin removal is sound. Those are
separate semantic boundaries with separate evidence.

Investigation and specification design: Codex (gpt-5.6-sol), 2026-07-21 session. Whether and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a feasibility and design specification, not an implementation commitment.

Reference specification approved by Claude Sonnet 5, 2026-07-21 session, with the user's explicit approval. This signature approves the document as a reference specification for future implementation slices — it does not itself authorize implementation of any slice, including Slice CPROV-A. Each slice requires its own explicit scoping and authorization before write-enabled work begins, following this project's established discipline (as used for the "generic role impl conformance" Stage 5 project and the ordinary-cast-resolution project).
