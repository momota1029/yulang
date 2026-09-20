# SCC lifecycle executor R1

Status: Reviewed; withdrawn as implementation candidate

Date: 2026-09-21

Scope: the first structure-only execution gate over the completed F0-F2 batch
and static SCC plan. R1 fixes global activation, open/closed use routing,
transactional publication, and terminal failure without choosing schemes,
generalization, freshening, recursive-cycle results, or public inferred-name
behavior.

Drafted-by: architect role from the frozen Yulang oracle and current Yulang3
implementation

Reviewed-by: compiler-referee, specification, and performance M3 reviews on
2026-09-21; clean after three bounded design repair rounds

Supersedes: none. `SolvedModule::solve` remains the sole plan consumer; R1 is a
private `SolveSession` sub-owner. User approval of R1 also authorizes the
solve-failure API change described below.

Withdrawn-by: user selection of recoverable inference on 2026-09-21. R1 is
historical lifecycle evidence only; R2 is the active successor candidate.

## Decision and ownership

```text
SolvedModule::solve(batch)
    -> SolveSession::new(batch)
    -> session.run()
    -> CompletedSolveSession::finish()
```

`SolveSession<B>` owns the consumed batch, backend/store, a private execution
run lifetime, lifecycle/poison state, dense publication slots, dense component
visibility, temporary component transactions, and counters. `SccPlan` remains
immutable planning data. No public phase/API, HIR authority, or plan mutation
is introduced.

The transaction is generic over publication payload `P`. R1 uses a structural
payload; the future scheme gate must use this same transaction with its approved
prepared-scheme payload. A parallel scheme map or later per-definition
publication path is forbidden. R1 changes no public solved projection and
creates no placeholder scheme, root alias, closed-use `Unknown`, or no-op fact.

The exact result family is:

```text
SolveSession<B>::run(self)
    -> Result<CompletedSolveSession<B>, ExecutionFailure<B::Error>>

CompletedSolveSession<B>::finish(self) -> SolvedModule

ExecutionFailure<E> {
    stage: ExecutionFailureStage,
    cause: ExecutionFailureCause<E>,
    counters: ExecutionCounters,
}

ExecutionFailureStage =
    Activate | OpenRoute | Prepare | Validate | PublicationLookup | ClosedRoute

ExecutionFailureCause<E> =
    Backend(E) | ArtifactMismatch | MissingIdentity | NotPublished
  | InvalidLifecycle | DuplicatePublication | NonTotalPublication
```

`ExecutionFailure` contains the frozen counters needed to report poison,
discard, and failure-stage metrics, but no backend state, payload, publication
slot, or retry capability. `finish` exists only on the completed success type.

The public `SolvedModule::solve` signature remains a `Result`, but R1 adds an
explicit variant to its existing public error boundary:

```text
SolveAvailabilityError::ExecutionFailed {
    stage: SolveExecutionStage,
    kind: SolveExecutionFailureKind,
    counters: ExecutionFailureCounters,
}

ExecutionFailureCounters {
    poison_count: usize,
    discarded_prepared_payloads: usize,
    discarded_committed_payloads: usize,
}
```

The public stage mirrors the six stages above. The public kind is limited to
the structural causes `ArtifactMismatch`, `MissingIdentity`, `NotPublished`,
`InvalidLifecycle`, `DuplicatePublication`, and `NonTotalPublication`. R1's
production `StructuralBackend` uses `Infallible`; generic injected
`Backend(E)` is private test-runner evidence and never crosses the public API.
A later semantic backend must separately approve how its own error maps to the
public solve boundary. This new variant and its supporting copyable types are
the sole public API change in R1 and prevent lifecycle failure from being
mislabeled as an existing receipt or identity error.

`ExecutionFailureCounters` and its fields are `Clone + Copy + Debug + Eq +
PartialEq`; `SolveAvailabilityError` retains its existing `Clone + Copy +
Debug + Eq + PartialEq` contract. The complete internal `ProductionCounters`
remains non-`Copy` and does not enter the public error. The new enum variant is
source-breaking for downstream exhaustive matches because the current enum is
not `non_exhaustive`. User approval of R1 explicitly authorizes that exhaustive-
match break and the three new public copyable types/variants; it does not
authorize removing any existing trait implementation or changing existing
variant meaning.

## Oracle fidelity and Yulang3 strengthening

The frozen oracle at
`yulang2-oracle@a58eefc31e22141574b6f20c6a5748151` registers all roots and
queues completed bodies/uses before analysis drains, connects internal uses to
live roots, closes dependency sinks, constructs every member scheme before
incoming instantiation, and then reconsiders predecessors:

```text
open:   target live root <: occurrence value
closed: fresh(target scheme).positive_predicate <: occurrence value
```

The oracle builds a component-local generalized vector and then installs
member schemes before later `InstantiateUse` events. It does not have
Yulang3's dense slots or literal one-bit transaction. R1 explicitly strengthens
the sealed static lifecycle under the repository's plan/validate/infallible-
commit rule: activate all definitions before drain, consume the complete F2
plan, expose publication through one component barrier, discard the entire
private session on error, and never reopen or add a dependency. The oracle's
incremental graph, worklists, blockers, arenas, and dual scheme maps are not
copied.

## Phases

### E0 — construction

Consume one artifact-owned batch. Allocate dense publication slots for `D`
definitions and visibility state for `C` components. Create the private run
lifetime. Make one bounded `O(C)` prepass over component member-slice lengths,
reserve the verified maximum once, then reuse that single session-owned
preparation buffer for every component. Clear it after committed payloads move
out; E2 performs zero buffer growth/reallocation. The prepass performs no
member visit and builds no index. Run no backend command, sort, graph traversal,
new identity map, or stable-ID clone.

### E1 — global activation

Visit every `CollectedDefinition` once in `DefinitionOrderId` order before the
first component event:

```text
ActivateDefinition<'a> {
    definition: &'a DefinitionOrderId,
    root: &'a DefinitionRootId,
    body_fact_range: &'a Range<usize>,
    body_status: CollectedBodyStatus,
}
```

The synchronous command borrows its fields. R1 passes but never iterates,
clones, or rescans body facts. Direct-root expressions remain outside SCC
publication. No use routes during activation.

### E2 — dependency-first drain

Visit each component once in frozen plan order:

1. route every internal use;
2. prepare every member payload;
3. validate the complete hidden transaction;
4. commit the component infallibly and atomically;
5. route every incoming closed use.

Internal commands precede every preparation in their SCC. Incoming commands
follow target commit and precede every preparation in the parent SCC. No plan
slice is re-sorted or globally rescanned.

## Borrowed commands

```text
OpenUseCommand<'a> {
    use_record: &'a DefinitionUse,
    target_root: &'a DefinitionRootId,
}

ClosedUseCommand<'run, 'a, P> {
    use_record: &'a DefinitionUse,
    target: PublishedDefinition<'run, P>,
}
```

Commands are synchronous borrowed views and cannot be retained. Open commands
receive no publication; closed commands receive no live root. Use ID and cause
pass unchanged. Production retains no trace and clones no stable identity or
use record.

## Generic transaction

The private backend contract is:

```text
trait ExecutionBackend {
    type Payload;
    type Error;

    activate(&mut self, ActivateDefinition<'_>) -> Result<(), Self::Error>;
    route_open(&mut self, OpenUseCommand<'_>) -> Result<(), Self::Error>;
    prepare(
        &mut self,
        member: PreparedMember<'_>,
        visibility: PublicationView<'_, Self::Payload>,
    ) -> Result<Self::Payload, Self::Error>;
    validate_payload(
        &self,
        member: PreparedMember<'_>,
        payload: &Self::Payload,
    ) -> Result<(), Self::Error>;
    route_closed(
        &mut self,
        command: ClosedUseCommand<'_, '_, Self::Payload>,
    ) -> Result<(), Self::Error>;
    payload_owned_bytes(&self, payload: &Self::Payload) -> usize;
}
```

R1's production backend payload is the explicit zero-sized
`StructuralPublication`. `activate`, `route_open`, `prepare`,
`validate_payload`, and `route_closed` are the only fallible backend calls.
`payload_owned_bytes` is observation-only and must not mutate backend,
publication, or scheduling state. `PreparedMember` borrows the canonical
definition/root/status/range; pairing is positional with the current member
slice and performs no identity clone. `PublicationView` is read-only and is the
only reentrant lookup seam.

For R1 production, every `StructuralBackend` callback is `O(1)`, performs no
allocation, scan, stable-ID/use clone, or publication lookup, and
`payload_owned_bytes` returns zero. Reentrant lookup probes belong only to the
small test adapter. Generic future backends are outside R1's complexity claim
until their own approved gate supplies a resource contract. Future payload
referent-byte accounting must exclude the `P` slot itself and any storage
already reported as backend-owned, preventing double counting.

The backend prepares one `P` per canonical member into executor-owned local
hidden storage. Preparation may fail but cannot mutate external publication
state or expose a payload.

Before slot mutation, one pass over the canonical member slice validates
artifact/run ownership, exact cardinality/order, one payload per member, no
duplicate/already committed dense slot, exact component ownership, and backend
payload invariants. It uses expected member ordinals and existing F2 component
lookup: no whole-definition scan, per-component map/set, or plan rescan.

Commit then performs no allocation, fallible lookup, backend callback, or
observer call. It moves each payload into its prevalidated dense slot and flips
component visibility once after all moves. Lookup checks component visibility
before exposing a slot, so no partial component is observable.

## Publication authority and lookup

Slots and visibility are run-local facts. `SolveSession` is their sole writer;
only synchronous backend routing reads them through an executor-bound view.
They are publication authority for that run, not inferred-type authority or a
second membership table.

| Fact | Identity key | Class | Sole writer | Sole query | Physical authority | Lifecycle |
|---|---|---|---|---|---|---|
| prepared/published payload slot | current run + `DefinitionOrderId` | current-value | `SolveSession` transaction | `PublicationView` | dense run-local slot vector | allocated in E0; hidden until commit; dropped on finish/error |
| component visibility | current run + `SccComponentId` | current-value | infallible `SolveSession` commit | `PublicationView` | dense run-local component-state vector | false in E0; flips once; dropped on finish/error |

F2 remains the authority for definition membership and component ownership;
R1 validates against it and does not duplicate that fact.

`PublishedDefinition<'run, P>` is a private lifetime-bound borrow and cannot
escape or be reconstructed from IDs. It allocates no ordinal. Lookup errors are:

```text
ArtifactMismatch  // foreign collection
MissingIdentity   // same artifact, no admitted definition
NotPublished      // valid definition, barrier not committed
```

Wrong-run use is unrepresentable. `NotPublished` never becomes missing or
`Unknown`; closed routing treats it as structural failure.

## Failure and poison

`run(self)` returns `CompletedSolveSession` or `ExecutionFailure`. Activation,
open routing, preparation, validation, lookup, closed routing, and backend
callbacks may fail only outside the infallible commit region.

On failure, poison the session, run no further command, expose no retry, return
`Err`, and drop backend state, hidden payloads, slots, and earlier component
commits. Earlier commits never escape a failed solve; rollback is whole-session
discard, not reverse mutation.

`CollectedBodyStatus::Error` remains activation metadata. R1 does not decide
future semantic abort/error-payload/local-recovery behavior. Test injection is
structural backend failure, not that deferred language decision.

## Order, provenance, and test seam

Activation uses definition order; components use dependency-first plan order;
members and use IDs use existing canonical slices; closed routing immediately
follows target commit. Use ID/cause and body-fact causes remain existing
provenance. Spelling, path, component position, and publication order are not.

A `#[cfg(test)]` observer records scalar ordinal summaries for small fixtures.
Production has no event vector or trace branch. Test adapters can fail at
activation, open routing, chosen member preparation, validation, lookup, and
closed routing. Events are:

```text
DefinitionActivated | InternalUseRouted | MemberPrepared | MemberValidated
| ComponentCommitted | IncomingUseRouted
| LookupObserved(ArtifactMismatch | MissingIdentity | NotPublished | Published)
| SessionPoisoned
```

Acceptance requires all definitions active before component work; each
definition prepared/validated/published once; each component committed once;
each use routed once through exactly one partition; internal uses before SCC
prepare; incoming uses after target commit and before parent prepare; one
barrier for self/mutual cycles; hidden-before/visible-after lookup behavior;
no completed/partial session after injected failure; distinct foreign/missing/
unpublished results; deterministic small traces under insertion, alpha, and
path perturbation; and unchanged public facts/projections/diagnostics/Name.

Small witnesses include isolated, forward/backward chain, diamond, duplicate,
independent, self, mutual, mixed internal/incoming, error plus independent,
first/middle/final prepare failure, post-prepare validation failure, closed-use
failure after target commit, and no retry after poison.

## Complexity and resources

Executor overhead is `O(D + C + U)` and independent of body-range length.
Preparation, validation, and commit each make one bounded current-member pass.
Publication lookup is `O(1)` through dense definition slots, dense visibility,
and existing F2 component position. There is no whole-batch rescan after E1,
nested component/member scan, new hash table, graph traversal, sort, or stable
ID/use clone.

Counters cover activations; component visits/commits; member preparations/
validations/commits; internal/closed routes; definition/use/publication/
visibility probes; slot/state requested lengths, capacities, and growth;
maximum prepared length/capacity; publication/prepared payload slot bytes;
backend-reported payload bytes; poison and discarded prepared/committed payload
counts; component-size prepass visits; preparation-buffer growth/allocation
counts; and exact-zero sort,
map/set/index rebuild, trace, and stable-ID clone counts/bytes. The preparation
buffer has at most one E0 allocation and exactly zero E2 growth/reallocation.

Maintained `capacity * size_of::<slot>()` aggregates record construction,
activation, prepare/validate, commit transition, closed routing, and completed
retained peaks. Integrated peak is max(existing F2 build peak, co-resident F2
retained batch + store/backend + execution/publication + prepared capacity),
without recounting F0/F1 inputs. Instrumentation never scans source-sized state
inside execution loops.

Scaling at N=1,000/2,000/4,000 uses:

| Family | D | C | U | Max prepared |
|---|---:|---:|---:|---:|
| isolated | N | N | 0 | 1 |
| chain | N | N | N-1 | 1 |
| fan-in | N+1 | N+1 | N | 1 |
| repeated diamonds | 4N | 4N | 4N | 1 |
| one long cycle | N | 1 | N | N |
| independent mutual pairs | 2N | N | 2N | 2 |

A range-only witness fixes D/C/U while body ranges scale 1/2/4; execution
counters/capacities remain unchanged. Scale tests use a constant-space discard
backend, not traces. Exact counts are D activations/preparations/validations/
member commits, C commits, U routes, and zero sorts/rebuilds/clones/traces.
Named linear counters/bytes grow below 2.5x per doubling. Timing is added only
if counters reveal extra traversal, allocation, clone, or sorting.

## Stop conditions and deferrals

Return to design if implementation consumes outside private solve state,
drains before global activation, prepares before required routing, separates
future schemes from this transaction, performs fallible commit work, retries
after poison, returns partial output, leaks capabilities, conflates unpublished/
missing/foreign/Unknown, iterates body facts, retains production events, adds a
map/sort/graph walk/global rescan/stable-ID clone, treats closed use as a live
root, reopens a component, or admits a solving-time dependency.

Later gates decide schemes, generalization, freshening, value restriction,
occurrence components and facts, recursive-cycle results, semantic error
recovery, and Function/effect/application/method/role/import/Core IR behavior.

R1 is not an implementation candidate.
