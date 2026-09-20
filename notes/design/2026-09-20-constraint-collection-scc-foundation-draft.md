# Constraint collection and SCC inference foundation

Status: Reviewed

Date: 2026-09-20

Reviewed by: compiler-referee, specification, and performance M3 reviews on
2026-09-20; clean after two bounded repair/delta rounds.

Scope: replace fixture-led type-inference growth with a structure-first,
lightweight port of Yulang's constraint-collection and definition-SCC
lifecycle. This foundation is implemented before function syntax, identity
inference, application typing, or per-fixture generalization rules.

User direction: Yulang3 must recover the owning inference structure from the
frozen Yulang implementation and simplify its machinery without inventing a
new inference path for each small expression. The first construction target is
constraint collection plus SCC collection/scheduling.

Oracle: `yulang2-oracle@a58eefc31e22141574b6f20c6a5748151`. The complete
compiler tree and history are already available in local Git objects; copying
the files into this branch would add a second mutable source tree and is not
required. A detached temporary worktree may be used only when a filesystem
tool cannot read Git objects directly.

The user's current direction withdraws
`2026-09-20-identity-function-simple-sub-r1-supersession-draft.md` from the
active implementation sequence. Upon approval this record becomes its active
replacement. The former record's identity derivation remains
evidence for a later Function/generalization gate, but its definition-order
generalization, ordinary-self failure classification, whole-module
`UnsupportedValueExpansion`, and no-SCC assumptions are withdrawn.

It also narrowly supersedes the completed directed-integer and binding-root
gates only by adding a dependency record for a resolved Name occurring inside
an admitted binding body. F0-F2 retain their existing rule that the Name has no
value/effect component, emits no subtype fact, contributes no body-to-root
fact, and projects `Unknown`. The existing integer facts, exact five-fact
integer-binding witness, store/provenance authority, failure isolation, and
public solved projections remain unchanged. A later semantic-use gate must
explicitly supersede those retained exclusions before adding an occurrence
value or a name constraint.

## Oracle invariant

Yulang's semantic order is not source order:

1. predeclare the definition namespace;
2. register each definition root immediately before lowering its body;
3. lower/collect every admitted body and resolved definition use, queuing all
   lifecycle work before analysis drains;
4. form and update the open definition-component graph;
5. connect uses inside an open SCC to live roots;
6. close dependency sinks first;
7. generalize every member of one ready SCC behind one publication barrier;
8. instantiate each incoming occurrence from the newly closed schemes;
9. reconsider predecessor components until no work remains.

The graph edge is `parent/user -> target/dependency`. A component cannot close
until all members are registered and finished, it has no outgoing open
dependency, and every admitted delayed dependency is released. Consequently,
condensation sinks close first. Source order determines deterministic event
order, not generalization order.

An open use and a closed use are different operations:

```text
open use:   target live root <: occurrence value
closed use: fresh(target scheme).positive_predicate <: occurrence value
```

Internal/self/mutually recursive uses are never instantiated from a scheme that
does not yet exist. A component publishes none of its schemes until every
member scheme has been constructed.

Oracle owners include `crates/infer/src/scc.rs`, `scc/graph.rs`,
`lowering/body/mod.rs`, `lowering/name_ref.rs`, `uses.rs`, and
`analysis/session/instantiate.rs` at the frozen commit.

## Lightweight-port boundary

Yulang3 keeps the oracle lifecycle and directed semantics while removing
unneeded mechanisms from the first gate. It does not reproduce arena layout,
proof kernels, role/method selection, conformance blockers, dirty schedulers,
shadow oracles, caches, incremental invalidation, eager explanations, or the
lowering/solving interleave.

F0-F2 use a sealed static module batch and a linear static SCC/condensation
kernel. This preserves the oracle's semantic component partition and
dependency-first order without copying its DFS-per-edge incremental graph,
whole-map merge rebuilds, or per-append payload sorting. Those oracle mechanisms
are observably superlinear on adversarial insertion orders and are not the
lightweight implementation target.

The first input is:

```text
DefinitionUse {
    id,
    parent,
    target,
    occurrence,
    cause,
}
```

The immutable output is:

```text
SccPlan {
    components_in_dependency_first_order,
    component_of_definition,
    internal_uses_by_component,
    incoming_uses_by_component,
}
```

`DefinitionUseId` is the semantic payload handle. Batch, graph adjacency, and
plan all store that ID rather than cloning the use record. `cause` is provenance
only. F0-F2 create no `occurrence_value`, `OpenUse`, `InstantiateUse`, scheme,
or publication event. A later execution gate attaches value components to the
same use IDs and implements the oracle's open/closed split over this plan.

Dependencies first discovered during solving are not admitted by F0-F2. Before
methods, roles, or conformance add such dependencies, a later approved gate must
either introduce readiness blockers plus an incremental owner or recollect a
sealed plan. No published component may be reopened.

## Phase and fact ownership

`yu-hir` continues to own resolved `DefId` identity. It does not own inferred
types or SCC membership.

F0 introduces an opaque, artifact-branded `DefinitionOrderId` allocated from
the admitted binding's HIR order. It is independent of spelling, source range,
module path text, and hash order. `DefId` remains the semantic resolution
endpoint; `DefinitionOrderId` is only the total key for deterministic graph
members, component identity, and scheduling.

`ConstraintBatch::collect` owns one complete immutable collection result:

```text
CollectedDefinition {
    definition,
    root,
    body_fact_range,
    body_status,
}

DefinitionUse {
    id,
    parent,
    target,
    occurrence,
    cause,
}
```

Collection performs the existing one physical HIR traversal. During that pass
it records definitions/roots and unresolved endpoint pairs for uses; after the
traversal, one logical pass over those collected records resolves every endpoint
against the completed definition table. It never traverses HIR or CST a second
time. This strengthens the oracle's per-body root registration into a complete
Yulang3 root table before static SCC planning without changing the authoritative
one-HIR-traversal count. Every admitted definition receives exactly one record
even when its body fails. It retains every use occurrence and emits no
scheme, occurrence component, name constraint, or generalization result. Graph
arcs may deduplicate `(parent, target)`, but their ordered `DefinitionUseId`
payloads never deduplicate merely because the arc does. Direct-root resolved
names have no parent `DefId` and are explicitly outside F0-F2.

The solver owns:

- the canonical directed constraint store;
- the static SCC plan and component membership;
- dependency-first component order;
- later, open-use versus closed-instantiation decisions and the atomic
  publication barrier;
- eventually, component generalization and closed schemes.

`ConstraintBatch::collect` constructs and owns the immutable `SccPlan` as part
of the batch artifact after its one HIR traversal. `SolvedModule::solve` is its
sole phase consumer; F0-F2 do not yet execute component semantics. Temporary
SCC state and adjacency construction are discarded after the plan freezes.
The batch exposes decisive-one artifact-checked component lookup for every
admitted definition, `full set` internal/incoming use-ID queries per component
with worst-case `U` retained IDs in either result, and decisive-one use lookup.
Foreign query IDs return
`ArtifactMismatch`; missing same-artifact IDs return `MissingIdentity`.
Construction-time foreign endpoints, duplicate IDs, exhaustion, or non-total
maps are collection availability errors. `SolvedModule` will own eventual
public inference results; neither the plan nor HIR becomes a peer type
authority.

| Fact | Stable key | Sole writer | Lifecycle / failure |
|---|---|---|---|
| collected definition | artifact + `DefinitionOrderId` | F0 collector | one per admitted definition; immutable batch |
| definition use | artifact + occurrence | F0 collector | one per resolved binding-body occurrence; immutable batch |
| distinct graph arc | `(parent, target)` | F1 graph builder | transient adjacency; owns ordered use-ID payloads |
| SCC member | canonical component key + `DefId` | F1 SCC kernel | retained in immutable plan |
| component order | canonical component key | F1 condensation scheduler | retained in immutable plan |

Foreign construction artifacts, duplicate use IDs, missing definition endpoints, identity
exhaustion, and inconsistent total maps are collection/plan availability errors;
they never become local type `Unknown`. Body errors remain local `body_status`
and do not prevent an otherwise valid plan from freezing.

## Construction sequence

### F0 — collected dependency model

Add artifact-branded definition-use identities and immutable collection output.
Collect all definition roots, existing integer/body constraints, and resolved
module-definition uses before solving begins. Local names do not create module
dependency edges. Ambiguous and unresolved names retain their existing total
HIR state but create no resolved-use edge.

F0 does not infer a name type. It proves that forward, backward, duplicate-use,
self, and mutual-use graphs are collected completely and deterministically.

### F1 — static SCC plan

Build the complete directed definition graph, then run one iterative
Tarjan/Kosaraju traversal with explicit heap worklists:

- directed component arcs `parent -> target`;
- one SCC membership result for every admitted definition;
- deterministic member, component, arc-payload, and plan ordering;
- condensation sinks before their predecessors;
- exact internal/incoming use-ID partitions;
- no solving, generalization, or partial publication.

F1 is exercised against synthetic definition/use records, not by adding a new
language expression merely to drive it.

Members are sorted by `DefinitionOrderId`; the first member is the canonical
component key. Arc payloads are sorted once by `DefinitionUseId`. The
condensation scheduler chooses among ready sinks by canonical component key.
The raw frozen plan, not a post-hoc normalized comparison view, must be identical
under perturbed map insertion order.

### F2 — collected-batch integration

Freeze one `SccPlan` from the complete F0 batch and expose an artifact-checked
read-only query by definition/use ID. F2 establishes membership, use partition,
and dependency-first order only. It emits no close/instantiate event and does
not fabricate `Unknown`, equality, reverse edges, or copied root results.
Generalization, freshening, Function structure, and identity syntax follow as
separate gates over this foundation.

## Required structural witnesses

The first gates are tested as graph/inference structures:

- isolated definition;
- backward and forward acyclic chains produce the same dependency-first order;
- diamond dependency closes the shared sink once;
- two occurrences on one graph arc retain two payloads;
- self-use remains one singleton SCC with one internal use;
- mutual use forms exactly one SCC with both internal uses;
- independent SCCs continue deterministically;
- local HIR uses add no module-definition edge;
- ambiguous/unresolved names add no false edge;
- direct-root names remain outside the definition-use graph;
- foreign artifact identities fail at the ownership boundary;
- perturbed hash insertion order does not alter the raw frozen plan;
- alpha-renaming every definition/use and changing module path text preserves
  the raw component/order topology modulo the artifact brand;
- an error body still receives one definition record, creates no false use edge,
  and cannot strand an independent component.

These witnesses do not decide the inferred type of an unconstrained recursive
cycle. They establish the lifecycle required before that semantic decision can
be made.

## Complexity and measurements

For `H` HIR items, `D` definitions, `U` retained use occurrences, and `E`
distinct dependency arcs, one HIR traversal, one collected-record endpoint
pass, and graph/SCC construction are `O(H + D + U + E)`, followed by one
canonical sort whose comparisons are accounted separately. Record in
production-visible counters:

- definition-index and body-pass visits, definitions, roots, and body statuses;
- distinct arcs and retained occurrence payloads;
- forward/reverse adjacency entries and payload lengths/capacities;
- Tarjan/Kosaraju node/edge visits, stack pushes, lowlink/component writes, and
  peak stack/temporary-set bytes;
- SCC count, maximum component size, internal/incoming use counts;
- condensation node/edge visits, ready-set operations/comparisons, and maximum
  ready-queue size;
- sort count, comparisons, and total elements sorted;
- generated, accepted, and duplicate constraint facts;
- map/set probes, capacities, rebuilds, clone count/payload bytes, retained plan
  bytes, and peak batch+graph+plan workspace.

Use chain, diamond, duplicate-payload, independent-component, long final-cycle,
self-cycle, and mutual-cycle 1,000/2,000/4,000 synthetic families. Named linear
counters and retained/peak bytes must grow by less than 2.5x at each doubling;
canonical sort comparisons are reported separately under their `O(N log N)`
budget; ready-queue comparisons belong to the same canonical-order budget.
Timing is added only if counters expose a second graph traversal beyond
the chosen SCC algorithm, repeated sorting, clone growth, or an allocation
anomaly.

## Stop conditions

Stop and return to design if implementation:

- constructs the plan before the complete admitted dependency batch is sealed;
- uses source order as semantic generalization order;
- loses occurrence payloads while deduplicating graph arcs;
- derives SCC identity from spelling, ranges, or hash iteration order;
- uses recursive DFS on a source-sized graph;
- adds expression-specific scheduling branches;
- creates a parallel typed HIR or persistent graph as a peer type authority;
- copies full use payloads between batch, adjacency, and plan instead of using
  stable IDs;
- uses the oracle's DFS-per-edge/global-rebuild incremental algorithm in this
  sealed static gate;
- silently admits a dependency discovered only during solving.

## Deferred semantic gates

This foundation deliberately does not yet decide:

- scheme representation, freshening, or generalization variables;
- value restriction and the non-generic environment;
- the result of unconstrained alias/self cycles;
- recursive function skeletons and named-self lowering;
- Function/effect structure, parameter-local HIR, or `my f x = x`;
- application, methods, roles, conformance, imports, or Core IR;
- SCC-local error recovery once a member's semantic solve fails.
- dynamic SCC updates and readiness blockers for dependencies discovered while
  solving.

Those are attached to the SCC lifecycle in later structure gates rather than
implemented as isolated fixture paths.
