# Resumable private candidate suspension contract

Status: Reviewed; not user-approved; no implementation authority
Scope: private candidate execution suspension and lifecycle continuation for the
approved contextual-attachment admission gate
Authority basis: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§4–6; this draft proposes an implementation contract for that approved gate
and does not change language semantics, supported-input policy, or public APIs
Supersedes: none
Reviewed-by: independent compiler-referee and spec-auditor; exact-wording delta reviews passed 2026-10-11

## 1. Purpose

The approved lifecycle gate requires retaining a newly accepted edge and its
exact contextual obligations when a component falls outside the two certified
cycle classes. The candidate must withdraw every dependent observation and
defer publication until an exact general path can finish the component. The
current implementation executes freshening, bound restoration, replay, typed
dispatch, source actions, and member publication through nested synchronous
loops. Returning from a nested loop loses its local continuation; retrying the
outer operation can allocate a second fresh use, reinsert a bound, repeat a
completed child, or skip a pending obligation.

This draft selects a private defunctionalized continuation stack to preserve
that existing execution order. It is a private implementation mechanism, not
a new type rule, error result, resource bound, or public pending-inference API.

## 2. Execution outcome and outward boundary

The private candidate driver has an outcome distinct from availability failure
and ordinary completion:

```text
CandidateRun = Complete(result) | Suspended(session, wait_set)
```

`Suspended` retains the inference session, accepted graph mutations, pending
obligations, withdrawn observations, and publication state. An unchanged wait
set and lifecycle generation must return the same suspended state promptly;
it must not spin or replay completed work. A relevant later mutation or an
explicitly restored supported generation may resume it.

`SolveAvailabilityError` remains reserved for failed construction, resource
failure, or corrupted identity/accounting. Suspension is not mapped to that
error, a language diagnostic, a source rejection, or completed `Ok`.

This gate does not alter `CandidateInference::solve` or expose a new public
resume API. Production certificate creation remains unavailable until the
separate readiness/filter/recognizer gate supplies complete evidence. Any
private test driver or internal caller that can observe `Suspended` must retain
the session; the completed-result API may only receive `Complete`.

## 3. Continuation ownership

One owned stack records the active nested execution. Each frame owns the data
currently held only in its caller's stack frame. The innermost frame resumes
first; its parent advances only after the child operation completes.

Required frame classes:

1. **Source/SCC plan:** loose or root action cursor; component and member
   position; phase; active roots/uses; staged member graphs; publication group.
2. **Source action:** current action and its substage. Construction and
   publication are separate for `LocalAnnotation`/`Install`; an already
   constructed exposed root is retained across suspension.
3. **Freshening:** source graph/use identity; constructed terms, rows, views,
   contexts, bundles, and evidence remaps; current captured-bound position.
   A fresh-use identity and completed remaps are never recreated on resume.
4. **Bound restoration:** accepted emission and canonical bound; saved opposite
   count; current opposite index; current relation/fiber identity; next step.
   The accepted bound is never inserted again.
5. **Replay:** frozen lower/upper fiber heads, prior progress, quadrant and
   cursors, and exact generated child batch. Existing generated replay progress
   is not treated as completed child consumption.
6. **Child consumption:** exact ordered child list and next child index. A
   child advances only after its constraint drain completes. Retain child
   completion provenance so invalidation can identify which earlier children
   must be recomputed.
7. **Typed drain:** initial task/provenance, current item and dispatch stage,
   remaining worklist, processing scope, transition total, diagnostic
   completion, and replay continuation.
8. **Function dispatch/extrusion:** already admitted parent/diagnostic edges,
   child ordering and next port/enqueue stage; extrusion maps, work stacks,
   pending bounds and current work stage.
9. **Recomputation:** ordered invalidated child/observation roots, the exact
   retained input relation and origin, and the stage needed to remove only
   certificate-derived consequences before replaying them.

Replace closures that borrow local vectors with explicit dispatch operations
whose inputs and progress can be retained. Do not reconstruct a frame from
endpoint spellings or unordered graph adjacency.

## 4. Suspension boundary and ordering

Lifecycle validity is checked before any dependent observation is reused. When
a mutation changes the exact dependency set, the route first reserves journal
and continuation capacity, then:

1. records the accepted edge and exact source/context evidence;
2. increments the lifecycle mutation generation (distinct from intrusion's
   equality generation);
3. marks dependent observations dirty and withdraws their memo/completion and
   publication results before reuse;
4. attempts the exact approved two-class recognizer using complete witnesses;
5. if the component is supported, recomputes dependent observations before
   publication;
6. if unsupported, retains the edge and frames and returns `Suspended` before
   the next dependent child, replay, source action, or member publication.

The physical-bound restore contract remains sequential: install one accepted
bound, save the opposite count, then for each index re-read the current
canonical owner and its direct/exact opposite vectors using the existing
`candidate_opposite_count` / `candidate_opposite_bound` behavior. Same-component
callbacks may append bounds or intrusion may redirect the canonical owner
before a later index is read; resumed execution must observe those changes in
the same way as uninterrupted execution. The continuation stores the original
count and next index, not a frozen endpoint list. Do not pre-expand all
products across a suspension; that would change callback ordering.

Intrusion representative changes may occur before a suspended frame resumes.
Every resumed relation construction canonicalizes its retained raw endpoints
using the current representatives, while preserving the original saved
opposite count, fiber identity, and product order. Any case where this fails to
preserve existing replay semantics remains a blocking proof obligation; the
implementation must defer cross-component mutations that can alter a suspended
frame's incidence until that obligation is resolved.

## 5. Mutation dependency and publication ownership

Certificate validity is keyed to a lifecycle generation and exact dependency
identities; intrusion generation alone is insufficient. Mutations that can
change evidence without allocating a relation/context or changing an SCC must
participate, including dependency-only Function-port incidence, origins,
attachment/filter registrations, bound fibers, evidence imports/transforms,
and capture incidence.

All observations that consume a certificate generation must register that
dependency. This includes typed memo/completion results, replay progress and
generated child batches, derived bounds, captured graph slots, incoming-use
eligibility, and group publication. Before old-generation reuse, withdraw every
dependent result. A reverse edge is not sufficient evidence that the
observation inventory is complete.

Invalidation may occur after an earlier sibling child completed. The lifecycle
must enqueue a recomputation frame ahead of the saved continuation for every
withdrawn dependent child/observation, in original dependency order. Recompute
uses retained typed relations, origins, context, and accepted physical bounds;
it must not repeat bound emission, source freshening, or construction that was
already completed. Removing a certificate-derived result does not erase the
underlying exact relation or a newly accepted edge. The original continuation
resumes only after required recomputation completes. If recomputation itself
suspends, the original continuation remains blocked behind it; neither cursor
advances past unfinished recomputation.

Member graphs are staged for the whole SCC and become visible together only
after every member's source actions and dependent observations are complete.
A suspended member prevents publication of the group and routing of incoming
uses through its graph. Independent components may continue only when their
dependency sets are disjoint from the suspended continuation.

## 6. Transaction, accounting, and retry

The existing route transaction journals, as one unit:

- lifecycle generation, certificates, dependency registrations and dirty sets;
- withdrawn/recomputed observations and generated-versus-consumed replay
  progress;
- continuation frames, cursors, wait registrations, source/SCC frontier, and
  staged/replaced/removed graph slots;
- accepted bound/context/evidence mutations and retained-byte accounting.

A route failure or allocation failure restores the exact pre-route state. A
successful suspension commits the accepted edge and unfinished obligations
without publishing affected results. Resume starts from the innermost saved
frame. A supported retry after rollback uses only the restored generation.
Duplicate dependency admission does not advance the lifecycle generation or
withdraw unrelated observations.

All frame, child-batch, dependency, and journal storage is fallibly reserved
before the mutation that relies on it. Retained and rollback bytes are included
in existing resource accounting. This draft adds no time/size cap and no
source-level rejection.

## 7. Required verification before enabling production certificates

The lifecycle adapter may use a test-only synthetic certificate to exercise
state transitions. Such a test is not source authorization or evidence that
the exact recognizer is complete. Before any production certificate is minted,
the implementation also needs genuine readiness, filter-obligation, transport,
and dependent-observation witnesses plus exact source-generated recognition.

The lifecycle regression must suspend during a real source-owned fresh-use
restoration after an accepted bound, with multiple opposite products and child
relations remaining. Begin with an initially certified component that has
existing certificate-dependent memo/completion observations and a published
member graph. Admit a late unsupported Function/swap edge while preserving its
exact source incidence. The test must assert that every old-generation
dependent observation and publication is withdrawn before reuse, the new edge
and unfinished obligations remain retained during private suspension, failure
rolls back the whole transition, and a supported retry completes from the
restored generation. It must also establish:

- no second fresh-use identity or bound emission on resume;
- exact children and popped/queued typed work remain owned;
- repeated drive without a relevant mutation is stable and does not spin;
- an injected route failure restores generation, continuation, observations,
  publication and accounting exactly;
- invalidation after one sibling child has completed requeues that child's
  dependent computation, withdraws its old result first, and recomputes it
  before the saved next child without a second fresh use or bound emission;
- supported retry completes remaining work once and in original order;
- source/SCC execution reaches completion and publishes all members together;
- a second suspension during Function-port admission retains the newly made
  relation before its enqueue step;
- ordinary identity/zero-word routes without certificate dependencies remain
  unchanged.

Use one compiler-referee review for obligation preservation, ordering and
rollback, and one spec-auditor review for §§4–6 conformance. Performance review
is required only if measured or structural analysis finds material hot-path or
retained-space risk. No broad suite runs between intermediate repairs.

## 8. Explicit limits

This contract does not implement a general mixed recursive-context solver,
Call/Catch completion, concrete negative formal-row admission, default/production
routing, F5 retirement, or the final Oracle hygiene proof. It preserves the
approved two-circuit acceleration boundary and leaves all-source source
completeness, principality and soundness as separate gates.
