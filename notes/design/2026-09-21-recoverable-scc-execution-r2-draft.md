# Recoverable SCC execution R2

Status: Superseded; withdrawn as implementation candidate

Date: 2026-09-21

Approved-by: user

Approved-at: 2026-09-21

Scope: replace R1's whole-session semantic failure model with recoverable,
component-atomic SCC inference while retaining terminal failure for structural
unavailability.

Drafted-by: architect role after explicit user selection of recoverable type
inference

Reviewed-by: compiler-referee, specification, and performance M3 reviews on
2026-09-21; clean after three bounded repair rounds

Supersedes: `2026-09-21-scc-lifecycle-executor-r1-draft.md` upon approval.

Superseded-by:
`2026-09-21-oracle-aligned-static-scc-inference-session-draft.md` in the full
R2 authority scope on 2026-09-21. Direct inspection of the frozen Yulang2
oracle showed that its recoverable inference closes and generalizes erroneous
definitions normally; it does not use Failed/Blocked SCC outcomes or a generic
publication executor. Retain this document as rejected design history only.

## Approved direction

The user selected these decisions on 2026-09-21:

- semantic type failures return `Ok(SolvedModule)` with partial facts;
- structural/availability failures remain terminal `Err`;
- failed dependencies conservatively block predecessors;
- dependent failures retain provenance but emit no primary cascade diagnostic;
- `CollectedBodyStatus::Error` seeds component failure without duplicating its
  existing diagnostic;
- the public structural error is named `ExecutionUnavailable`.

`Unknown` remains a recovery projection only. It is never a constraint leaf,
scheme, `Any`, `Never`, or quantifiable placeholder.

## Result and failure boundary

```text
SolveSession<B>::run(self)
    -> Result<CompletedSolveSession<B>, ExecutionUnavailability<B::AvailabilityError>>

CompletedSolveSession<B>::finish(self) -> SolvedModule
```

A completed session has drained the whole plan and may contain published,
locally failed, and dependency-blocked SCCs. Only artifact/identity/lifecycle,
compiler-invariant, resource, or backend-availability failure poisons and
discards the session.

The public boundary adds:

```text
SolveAvailabilityError::ExecutionUnavailable {
    stage: SolveExecutionStage,
    kind: SolveExecutionUnavailableKind,
    counters: ExecutionUnavailableCounters,
}
```

The compact counters preserve the existing public `Copy`/equality traits.
Existing variant meanings remain unchanged. Because the enum is exhaustively
matchable, approval explicitly accepts the downstream exhaustive-match source
break.

## Ownership and states

`SolvedModule::solve` remains the sole consumer. A private `SolveSession`
owns the batch, backend/store, dense run-local component transactions,
publication slots, final component outcomes, blocked-use provenance, counters,
and poison state. F2 remains membership/order authority.

```text
ParentCondition = Ready | Blocked

ComponentLifecycle =
    Pending(ParentCondition) | Preparing | Published | Failed | Blocked

DefinitionPublication<P> =
    Published(P) | Failed(ComponentPosition) | Blocked(ComponentPosition)
```

Final precedence is local semantic failure (including body error) → `Failed`;
otherwise failed/blocked dependency → `Blocked`; otherwise → `Published`.
Every member of one SCC receives the same outcome class. `Failed` and `Blocked`
expose no payload.

## Backend channels and parent-owned transactions

```text
SemanticStep<T> = Ready(T) | LocalFailure

trait ExecutionBackend {
    type Payload;
    type AvailabilityError;
    type ComponentState: Default;

    activate(..., owner: &mut ComponentTransaction<ComponentState>)
        -> Result<SemanticStep<()>, AvailabilityError>;
    route_open(..., owner: &mut ComponentTransaction<ComponentState>)
        -> Result<SemanticStep<()>, AvailabilityError>;
    prepare(..., owner: &mut ComponentTransaction<ComponentState>, ...)
        -> Result<SemanticStep<Payload>, AvailabilityError>;
    validate_payload(..., owner: &ComponentTransaction<ComponentState>)
        -> Result<SemanticStep<()>, AvailabilityError>;
    route_closed(..., parent: &mut ComponentTransaction<ComponentState>)
        -> Result<SemanticStep<()>, AvailabilityError>;
}
```

Before returning `LocalFailure`, a future semantic backend records its
structured cause in the owner transaction. Availability errors alone poison.
Closed-use work always mutates the parent/user SCC's hidden transaction, never
the published target or global visible state. This prevents partial mutation
when one of several incoming uses fails.

R2's structural backend uses a zero-sized payload, `Infallible` availability,
scalar component state, and `Ready` callbacks. Body-error seeds are executor
owned. Future semantic backends require their own approved resource contract.

## Phases

E0 allocates from known totals: `D` publication slots, `C` lifecycle/outcome
states and parent transactions, `C` failure summaries, and `U` blocked-use
slots. One `O(C)` prepass finds maximum member count; one preparation buffer is
reserved once and has zero E2 growth. No graph/index rebuild or sorting occurs.

E1 activates all definitions in definition order before drain. It resolves the
owner component through F2, seeds local failure for body error without a new
diagnostic, invokes backend activation, and records `LocalFailure` in that
component. Body fact ranges are borrowed, never iterated.

E2 visits each component once in dependency-first order:

1. transition pending to preparing;
2. route internal uses into the same hidden transaction;
3. attempt preparation for every member, even after blocker/local failure;
4. validate every prepared payload;
5. select Published/Failed/Blocked by precedence;
6. prevalidate total member-slot outcome;
7. commit every member outcome and component state atomically and infallibly;
8. route incoming uses into each parent transaction.

Continuing preparation after failure retains independently decidable errors.
Prepared successes in a final failed/blocked SCC are discarded before commit.
Commit allocates nothing, calls no backend/observer, performs no fallible
lookup, and exposes no partial SCC.

## Closed-use routing and propagation

```text
ClosedUseTarget<'run, P> =
    Published(PublishedDefinition<'run, P>)
  | Failed(FailedDefinition<'run>)
  | Blocked(BlockedDefinition<'run>)
```

Only `Published` exposes a payload. For failed/blocked targets, resolve the
parent through F2, require it still pending, mark it blocked, write the target
component position into the dense slot for that exact use ID, and invoke the
failure-view closed callback only to stage future occurrence recovery. Never
freshen, instantiate, or expose a live root.

Propagation uses existing incoming slices: a failed/blocked target marks direct
parents; those parents later commit and mark their parents. Every use is still
visited once. There is no reverse graph, worklist, rescan, mutation, or reopen.
An already preparing/final parent is `InvalidLifecycle` and terminal.

## Diagnostics, provenance, and retained result

`SolvedModule` privately retains component outcomes and one optional blocked
target position per use. This is derived solve output, not membership authority.
Local semantic failures own primary diagnostics. Body errors remain HIR-owned.
Blocked uses create no primary diagnostic, but retain exact `DefinitionUseId`,
cause, and target outcome for explanations. Diagnostic order remains existing
source/cause order. Failed-use projections may be `Unknown`; constraints and
schemes never contain `Unknown`.

## Invariants and recovery

- exactly one final `Published | Failed | Blocked` outcome per SCC;
- `Published` iff all required dependencies published and every member payload
  prepared/validated;
- failed/blocked SCCs expose zero payloads;
- one member failure makes the whole recursive SCC failed;
- blocked SCCs still run preparation to collect independent local failures;
- local failure never poisons, stops independent SCCs, or removes partial facts;
- structural unavailability poisons and returns no `SolvedModule`;
- previously published dependencies remain usable when a user SCC fails;
- no retry, reopen, late dependency, fake recovery scheme, or mixed SCC outcome.

## Counters and complexity

Execution remains `O(D + C + U)` with dense `O(D + C + U)` recovery state.
Production counters distinguish published/failed/blocked components and member
slots, body-error seeds, local failures by stage, successful/failed/blocked
target routes, parent transaction probes/mutations, blocked-use writes, local
payload discards, and availability-session discards. Required identities are:

```text
published_components + failed_components + blocked_components = C
published_payloads + failed_slots + blocked_slots = D
successful_routes + failed_routes + blocked_routes = external_use_count
blocked_use_writes = failed_routes + blocked_routes
```

Preparation attempts equal D. Sorts, graph walks, maps/sets/index rebuilds,
stable-ID clones, trace retention, and E2 vector growth remain exactly zero.
Phase peaks include transactions, outcome/failure state, blocked-use slots, and
the reused preparation buffer without double-counting F2 retained input.

In addition to the existing 1,000/2,000/4,000 graph families, recovery scaling
covers one failed sink with an N predecessor chain, one failed sink with N
parents, alternating independent failed/published SCCs, and independent failed
mutual pairs. Named linear counters/bytes remain below 2.5x per doubling.

## Required tests

- body error returns `Ok(SolvedModule)`, Failed, and no duplicate diagnostic;
- failed chain/diamond blocks only predecessor cone while independent SCCs
  publish;
- blocker plus local failure ends Failed and retains blocker provenance;
- one failed member makes self/mutual SCC wholly Failed;
- blocked SCC records another local failure;
- duplicate blocked uses remain distinct without cascade diagnostics;
- failed/blocked targets expose no payload/root/instantiation;
- closed routing mutates only the parent transaction;
- hidden before commit and exact outcome after commit;
- semantic failure injection continues independent SCCs;
- availability injection poisons/discards the whole session;
- semantic failure does not increment poison/availability-discard counters;
- current CrossKind isolation remains unchanged;
- insertion/alpha/path perturbation preserves raw outcomes/provenance.

## Stop conditions

Return to design if semantic failure returns public `Err`; failed/blocked target
exposes payload/root/instantiation; blocked SCC publishes; SCC members receive
mixed outcomes; independent inference/diagnostics are lost; dependent failure
emits primary cascades; `Unknown` enters constraints/schemes; closed routing
mutates target/global state; propagation adds a graph walk/worklist/rescan; or
outcome commit is fallible/partially visible.

Schemes, generalization, freshening, concrete Name/open/closed facts,
recursive-cycle semantic results beyond failure propagation, and later language
features remain separate gates.

R2 is approved for implementation.

## Normative round-1 repair

This section supersedes any less-specific protocol above.

R2 has three distinct mutation systems. Existing `ConstraintTransaction`
immediately mutates `ConstraintStore` and is never used as the recoverable
component transaction. New `ComponentTransaction` is run-local hidden state for
staged semantic/recovery/cause deltas. Infallible publication commit consumes a
prevalidated component transaction. Structural R2 admits no facts and leaves
existing store/provenance counts unchanged; a later semantic gate must design
its staged delta and canonical commit.

Blocked and body-failed components run only `check_local` for every member.
This dependency-independent callback receives collected member metadata but no
publication view, target root/payload, semantic store, or ordinary delta sink.
It returns `Continue` or `IndependentLocalFailure`. Only the latter changes a
Blocked candidate to Failed. Blocked/body-failed SCCs run zero open, prepare,
validate, or published-route callbacks. Ordinary semantic preparation stops at
its first local failure and discards prior hidden deltas/payloads.

Published and unavailable routes are separate borrowed commands.
`route_published` may return an owner-local semantic failure.
`recover_unavailable` may return only availability failure and a bounded
occurrence-recovery receipt; it cannot emit diagnostics, ordinary constraints,
payload/root access, freshening, or `LocalFailure`. Structural R2's recovery
receipt is empty because current projections already default to `Unknown`.

Callbacks append through bounded executor sinks. Each call checkpoints cause
and staged-delta cursors. Returned contiguous ranges must name the current
component/command owner. Continue has no failure cause; independent/local
failure has at least one. Receipt/range/owner mismatch is structural
unavailability. Causes are retained in dense command slots and materialized at
finish by one accounted merge of definition order and existing use-occurrence
order, with fixed stage and owner-local sequence ties. No comparison sort,
HIR/CST traversal, or cause clone is allowed. Body errors reuse HIR diagnostic
authority. Partial facts mean pre-existing collected facts and facts from
independent Published SCCs, never hidden facts/payloads from Failed/Blocked SCCs.

### Fact registry

| Fact | Key/class | Sole writer | Query/physical owner/lifecycle |
|---|---|---|---|
| membership/order | artifact + F2 IDs; immutable | F1/F2 | borrowed `SccPlan`; whole batch |
| pending blocker/local failure | run + component; current-value | executor | hidden component transaction; until outcome |
| staged semantic/recovery/cause delta | run + command owner; staged | bounded backend sink | component transaction/arena; commit or discard |
| definition publication | run + definition; current-value | infallible commit | dense slot; retained solved outcome |
| component outcome | run + component; current-value | infallible commit | dense outcome slot; retained solved outcome |
| blocked-use provenance | run + use ID; derived | unavailable route | dense use slot; retained solved result |
| solver error/provenance | artifact + existing cause order; immutable result | finish | `SolvedModule` |

Lookup distinguishes foreign artifact, same-artifact missing, hidden/not final,
Published, Failed, Blocked, and invalid lifecycle. Wrong-run handles are
lifetime-unrepresentable. Failed/Blocked are payload-free results, not errors.

### Exact backend and commit contract

Commands are synchronous borrowed `ActivateDefinition`, `LocalCheckMember`,
`OpenUseCommand`, `PrepareMember`, `ValidatePayload`, `PublishedUseCommand`, and
`UnavailableUseCommand`. The backend has separate `AvailabilityError`,
`Payload`, and bounded `ComponentState`; exact methods are `activate`,
`check_local`, `route_open`, `prepare`, `validate_payload`, `route_published`,
and `recover_unavailable`. Structural callbacks are O(1), allocation/scan/
clone/store/publication-lookup free, with ZST payload/state and zero owned bytes.
Generic future backend costs require a later approved contract.

Precommit validates exact member order/cardinality, one uniform outcome,
owner/range/receipt totality, hidden slots, and reserved capacities. Commit is
allocation-, lookup-, callback-, observer-, and failure-free. Published commit
applies staged deltas and payloads. Failed commit retains local causes and
blockers but discards semantic deltas/payloads. Blocked commit retains blockers
and recovery receipts while discarding ordinary semantic state.

### Unavailability boundary

Internal stages are Construct, Activate, LocalCheck, OpenRoute, Prepare,
Validate, PublicationLookup, PublishedRoute, UnavailableRecovery, Precommit,
and Finish. Causes are backend unavailable, artifact/missing/not-published,
invalid lifecycle, duplicate/non-total publication, capacity exceeded, and
continuation/cause/staged/recovery mismatch. E0 uses checked arithmetic and
`try_reserve_exact`; capacity failure is Construct/CapacityExceeded.

Public mapping is
`SolveAvailabilityError::ExecutionUnavailable { stage, kind, counters }`.
Stage/kind/counter types and the error preserve Clone+Copy+Debug+Eq+PartialEq.
Counters are poison count plus discarded prepared and previously committed
payload counts. Existing variants retain meaning; exhaustive matches are
source-broken as explicitly user-approved. Semantic failure never maps here.

### Resource ledger and evidence

E0 names and accounts D publication slots; C lifecycle, transaction, and
failure-summary slots; U blocker and recovery-receipt slots; maximum-member
preparation buffer; bounded semantic/cause arenas and command ranges; finish
output/scratch; and backend-owned state. Each records requested length, actual
length, capacity, element/retained bytes, allocation/growth counts, and phase
peak. Structural backend semantic/cause capacities and referent bytes are zero.
All E2 growth, graph walks, worklists, maps/sets, sorts, index rebuilds,
stable-ID clones, and production traces are zero.

Counters separately cover local checks, internal routes, prepare/validate,
published routes/results/skips, unavailable recoveries, blocked writes,
transaction mutations, staged/cause/recovery receipts and discards, three
component/member outcomes, poison, and availability discards. Required totals
include outcome components = C, outcome members = D, internal uses = I, and
published attempts/skips plus failed/blocked recoveries = external uses.

Recovery scaling at 1,000/2,000/4,000 covers failed predecessor chain, failed
sink with N parents, D=2/C=2/U=N duplicate blocked uses, alternating independent
failed/published SCCs, one N-member failed cycle, one N-member blocked cycle
plus failed sink, and independent failed mutual pairs. It asserts uniform
outcomes, exact blocker/recovery writes, full dependency-independent local
checks, zero forbidden work, and below-2.5x linear counters/bytes.

Test-only observers cover activation, body seed, local check, ordinary callback
start/success/failure/skip, delta validation, unavailable recovery, three
component outcomes, four lookup outcomes, and poison. Injection covers every
fallible stage and every receipt/continuation/publication invariant. Production
has no event branch/vector.

### Normative execution closure

The exact hidden candidate mode is `Ready | DependencyBlocked | LocalFailed`.
Every definition receives structural activation, but after the first independent
local failure all later ordinary backend activation, published-route, open,
prepare, and validate callbacks for that SCC are skipped and counted. Hidden
ordinary deltas/payloads are discarded immediately. Unavailable recovery still
records blockers, and `check_local` still visits every member. Final precedence
is LocalFailed→Failed, else DependencyBlocked→Blocked, else Published. This
state machine replaces the earlier prose requiring preparation after failure.

For E2: run all local checks first; Failed candidates commit Failed; Blocked
candidates commit Blocked; only Ready candidates run internal callbacks then
prepare/validate until first local failure. Incoming published callbacks run
only while the parent candidate is Ready. Exact accounting is:

```text
local_check_attempts = D
internal_use_visits = I
internal_route_callbacks + internal_route_skips = I
prepare_callbacks + prepare_skips = D
validate_callbacks + validate_skips = successful_preparations
published_route_callbacks + published_route_skips
  + failed_target_recoveries + blocked_target_recoveries = X
```

All R2 structural semantic/cause/recovery arenas and callback append bounds are
hard zero; structural callbacks append no deltas or causes. Nonzero bounds and
their capacity formula belong to the later semantic gate. Finish performs one
explicit D+U dense-slot scan and a comparison-sort-free multiway merge of
pre-existing occurrence-ordered solver errors (including direct roots),
definition-owned causes, and use-owned causes. Every record carries the existing
HIR occurrence/source-order key plus fixed stage/local sequence; records move,
never clone. Counters record D+U finish visits, output count, requested/capacity
bytes, and zero finish growth/sort/clone.

### Exact unavailability API

```text
ExecutionUnavailability<E> {
  stage: ExecutionStage,
  cause: ExecutionCause<E>,
  counters: InternalExecutionCounters,
}

ExecutionStage = Construct | Activate | LocalCheck | OpenRoute | Prepare
  | Validate | PublicationLookup | PublishedRoute | UnavailableRecovery
  | Precommit | Finish

ExecutionCause<E> = Backend(E) | ArtifactMismatch | MissingIdentity
  | NotPublished | InvalidLifecycle | DuplicatePublication
  | NonTotalPublication | CapacityExceeded | InvalidContinuation
  | CauseDeltaMismatch | StagedDeltaMismatch | RecoveryDeltaMismatch
```

The public `SolveExecutionStage` has the same eleven variants. Public
`SolveExecutionUnavailableKind` has `BackendUnavailable` followed by the twelve
non-backend causes above. Mapping is same-name; `Backend(_)` maps to
`BackendUnavailable`. `ExecutionUnavailableCounters { poison_count,
discarded_prepared_payloads, discarded_committed_payloads }` and both public
enums are public and derive Clone+Copy+Debug+Eq+PartialEq; fields have public
read accessors. `try_reserve_exact` failure maps Construct/CapacityExceeded.
Every unavailable result has poison_count=1. Existing error traits/variants
retain meaning; the exhaustive-match source break becomes authorized only when
R2 is approved.

### Exact structural callback surface

All command structs borrow the current definition/use/root and owner component
position. `activate`, `check_local`, `route_open`, `prepare`,
`validate_payload`, `route_published`, and `recover_unavailable` receive the
named borrowed command plus an executor-owned bounded view of the current
transaction and return `Result<StructuralStep, AvailabilityError>`;
`StructuralStep` is Ready or IndependentLocalFailure except that activation and
unavailable recovery are availability-only. Prepared payload pairing is by the
current canonical member index. Cause/delta/recovery range tokens are explicit
zero-length structural receipts. Over-bound/nonzero structural receipts map to
the corresponding mismatch cause. Every remaining callback after LocalFailed
uses the skip path above.

### Exact registry classification and query

Membership/order and collected records are current-value facts owned/read by
F2/ConstraintBatch for the batch lifetime. Candidate/lifecycle/publication/
component outcome slots are current-value facts keyed by run+component or
run+definition, solely written by SolveSession and read by its publication
view until finish. Blocked-use links are append-only occurrences keyed by
run+use ID, solely written by unavailable routing and read by finish/result.
Local cause drafts and final explanation links are historical provenance keyed
by existing cause/use occurrence order, written by bounded sinks/finish and
queried from SolvedModule. Staged deltas are current-value hidden transaction
state and are discarded or committed, never queried as facts. Physical owners,
not HIR or SccPlan, are the named dense vectors/arenas.

Queries return ArtifactMismatch or MissingIdentity for foreign/absent IDs;
Hidden for valid pending/preparing state; Published/Failed/Blocked for final
state; and InvalidLifecycle for wrong transition, duplicate write, or access
after poison. Wrong-run handles are lifetime-unrepresentable.

### Exact recovery scale dimensions

Use the table in the performance review contract: predecessor chain
`D=C=N,X=N-1,B=1`; failed sink with parents `D=C=N+1,X=N,B=1`; duplicate
blocked uses `D=C=2,X=U=N,B=1`; alternating independent `D=C=2N,B=N`;
wide failed cycle `D=N,C=1,I=N,B=1,M=N`; wide blocked cycle plus sink
`D=N+1,C=2,I=N,X=1,B=1,M=N`; failed mutual pairs `D=2N,C=N,I=2N,B=N`.
Tests pin all equations above, seven lookup outcomes, public derives/mapping,
hidden-delta discard, unchanged ConstraintStore facts, and zero structural
arenas/growth/forbidden work.

### Final normative closure

Structural R2 creates no cause stream, so finish reuses/moves the existing
solver-error vector wholesale without reading its elements; it performs only
the D+U dense outcome/provenance-slot scan. Any later nonzero semantic-cause
gate must separately design/account a global error merge.

The structural callback signatures are:

```text
activate(ActivateDefinition<'_>, StructuralTxnView<'_>) -> Result<(), A>
check_local(LocalCheckMember<'_>, StructuralTxnView<'_>) -> Result<Step, A>
route_open(OpenUseCommand<'_>, StructuralTxnView<'_>) -> Result<Step, A>
prepare(PrepareMember<'_>, StructuralTxnView<'_>) -> Result<Prepare, A>
validate_payload(ValidatePayload<'_, StructuralPublication>, StructuralTxnView<'_>)
  -> Result<Step, A>
route_published(PublishedUseCommand<'_, '_>, StructuralTxnView<'_>)
  -> Result<Step, A>
recover_unavailable(UnavailableUseCommand<'_, '_>, StructuralRecoveryView<'_>)
  -> Result<StructuralRecoveryReceipt, A>
```

Definition/member commands borrow only collected member metadata and owner
position. Only `OpenUseCommand` has a target live root. Published routing has a
use plus payload-bearing published target and no root. Unavailable routing has
a use plus payload-free Failed/Blocked target and no root/payload. `Prepare`
contains a ZST payload iff Ready, paired by canonical member index. Production
steps are Ready and receipts/ranges are zero. Test-only local failure uses one
executor-owned fixed injected-cause slot; it is absent from production/scale
tests and satisfies the one-cause invariant without a backend append.

The public stage enum has the eleven listed stages. The public unavailable-kind
enum has `BackendUnavailable` plus the eleven non-backend causes; mapping is
same-name and Backend maps to BackendUnavailable. Required lookup of Hidden
maps to NotPublished. Duplicate publication or duplicate blocked-use write maps
to DuplicatePublication; wrong transition/access-after-poison maps to
InvalidLifecycle.

Counter partition equations apply to completed recoverable sessions; an
unavailable result reports its frozen prefix. Completed sessions also satisfy
`activation_visits = D` and `activation_callbacks + activation_skips = D`, and
every recovery scale family asserts both.
