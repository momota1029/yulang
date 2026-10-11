# Lifecycle constructor-to-consumer feasibility

Date: 2026-10-11
Status: bounded static source characterization; unreviewed research checkpoint;
frozen for primary handoff. No authentic lifecycle witness or closure claim.
Baseline: `d7e87c63723213550ac28ddab45e2ef47ce17f6e`
Branch: `research/simple-sub-intrusion`
Lease: this file only

## Objective, authority and decisive result

Trace one certificate-dependent observation from its actual construction through
support, invalidation and final consumption under private suspension §§4–7.
The governing sources are the Authoritative
[suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md)
§§3–7 and [contextual admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§4–6. Accepted behavior retains unsupported late edges and exact obligations,
withdraws old observations before reuse, recomputes before continuation and
publication, preserves physical restoration order, and keeps production
certificates disabled until genuine witnesses exist.

**First decisive missing premise:** `candidate_context.rs:1013–1016` still
unconditionally returns incomplete filter, producer-readiness and
dependent-observation evidence. No authentic certificate-dependent observation
can be supplied by this retained-input constructor. The existing `PublishLocal`
control has a complete, narrowly traceable synthetic support-to-consumer route;
its observation is permission to install an already constructed local root,
not a result derived from a genuine circuit certificate. The missing bridge is
constructor-owned authorization plus a complete observation subscription that
travels with the constructed result to every consumer. Searching for another
source spelling or composing synthetic controls would leave that premise intact.

This extends the prior
[authentic source-route obstruction](2026-10-11-authentic-lifecycle-source-route.md)
with the precise synthetic observation boundary and downstream owners at this
baseline. It does not repeat its source-candidate search. The
[lifecycle architecture proposal](2026-10-11-retained-lifecycle-admission-architecture-proposal.md)
remains unapproved; none of its representation choices is adopted here.

## Claim class and hypotheses

Established source facts below mean direct observations of the pinned code,
not independently reviewed results. The result is a bounded characterization
of these owners, not an all-source absence theorem, a compiler counterexample,
or a general lifecycle correctness theorem.

For the producer obstruction, hypotheses are exactly: this baseline, this
`State::retained_input` implementation, and a call that returns successfully.
Regardless of roots, views, parents, selected dependency closure or earlier
gap flags, lines 1013–1015 append the three named gaps and line 1016 constructs
`InputCompleteness::Incomplete(reasons)`. Therefore a successful call cannot
yield `Complete`. Allocation failure instead returns an availability error;
it cannot supply the missing witness. This derivation needs no transition
model or source-reachability assumption.

For the synthetic control, additionally assume a live `PublishLocal` frame,
existing watched relation IDs, successful fallible reservations, and successful
route commit. A new exact `FunctionPort` touching its watched parent or child
invalidates that registration. The next source step suspends before installing
the local term. These hypotheses deliberately include test-only supplied
support; this conditional statement does not establish source authorization.

## Concrete construction, support and consumer trace

All locators refer to `crates/yu-solver/src/` at the pinned baseline.

| Stage | Exact owner and retained fact | Evidence boundary |
| --- | --- | --- |
| Authentic source action | `candidate_source.rs:644–652`: `Install` resolves its positive initializer; `LocalAnnotation` constructs the annotated exposed root. Both retain the root, slot and boundary in `Stage::PublishLocal`. | Construction is real; no support or circuit certificate is produced there. |
| Support creation | `candidate_source.rs:593–600` calls `candidate_context.rs:2259–2273` only under `cfg(test)`, validates watched IDs, fallibly reserves storage and retains `{watched, generation, valid}` under a fresh `SourceSupportId`. | The test supplies the footprint. It is not a complete source dependency witness or readiness proof. |
| Support attachment | `candidate_source.rs:596–599` requires `PublishLocal` and places the ID in that one source frame. | No support field is forwarded to the installed local scheme or SCC member graph by this operation. |
| Authentic mutation producer | `lib.rs:12476–12523` derives four ports from Function comparison and owns a `FunctionDispatch`; `lib.rs:12639–12647` admits one port before storing it as pending work. `candidate_context.rs:2565–2606` reads the actual processing parent, constructs the child relation/context and records exact `FunctionPort` incidence. | Argument and argument-effect incidence records `Swap` even with identity inherited context; an allocated `Swap` node is not required. This trace does not establish membership in an initially certified SCC. |
| Accumulation/invalidation | `candidate_context.rs:2284–2339` treats an exact duplicate as inert, reserves before the dependent mutation, records dependency edges, marks each touching valid source registration invalid, then publishes the exact dependency and new lifecycle generation. | This producer hook covers `FunctionPort` only. Invalidating a Boolean publication permission is not withdrawal of typed memo, completion, bound, capture or published-graph results. |
| Final permission consumer | `candidate_context.rs:2275–2277` returns a wait for invalid support; `candidate_source.rs:613–618` consults it before caller `Support`, and before `PublishLocal` at 624–630. The exposed term and source cursor remain retained. | Caller `READY` cannot bypass an invalid attached registration. There is no recertification or ordered recomputation at this check. |
| Successful local publication | `candidate_source.rs:625–629` calls `candidate_scheme.rs:1320–1334`, installs `LocalScheme {id, root, boundary}`, clears the registration and advances the source cursor. | This is a local slot, not SCC member publication. Clearing the frame registration ends this observation's support lifetime; it does not prove a later local use remains licensed. |

The smallest static discriminating control is thus
`PublishLocal(exposed, slot) → attach test support watching r → admit new
FunctionPort(parent=r, child=s) → step source`. It distinguishes guarded
future publication from an unguarded step without constructing a second source
root. It is an event schema, not a newly executed test or authentic §7 witness.
The mutation must be new and touch the footprint; duplicates and disjoint
endpoints do not invalidate this permission. An identity inherited context
still permits dependency-only generation change, so inspecting context-node
allocation alone would miss the producer event.

Rollback already has concrete support owners:
`candidate_context.rs:1582–1586` restores pre-existing registration validity and
removes newly registered IDs; 1655–1658 removes new dependency keys and restores
the lifecycle generation. IDs deliberately are not reused (645–647). This
limited inverse does not establish complete observation/publication rollback.
The prior [support ownership note](2026-10-11-source-boundary-support-ownership.md)
records separate focused verification; no historical pass is presented as a
new result at this baseline.

## Downstream observations and missing propagation

The source producer retains useful provenance that must stay distinct from
certificate support. `candidate_scheme.rs:984` allocates one fresh-use identity;
1221–1266 maps captured bound orientation, transports the exact source relation
and attachment bundles, imports the bound evidence antecedent, and passes
`BoundAdmissionCause::FreshUse` to physical restoration. These facts establish
where a future owner can retain input without repeating freshening or emission;
they do not register a certificate generation dependency.

`candidate_extrusion.rs:672–678` accepts one physical bound before saving the
opposite count. A retained Local parent advances `next_bound` only when that
restoration completes (`candidate_scheme.rs:1504–1514`). Native typed return
then consumes replay acknowledgements and retains a completion receipt before
removing its drain (`lib.rs:12595–12616`). These are current ownership and
completion operations, not evidence that an invalidated completed sibling has
a retained support/input record or is recomputed before its next sibling.

The full member publication consumer is separate:
`candidate_scheme.rs:879–911` finishes all source roots, captures all member
graphs into `staged`, then fills `state.graphs`. An incoming use requires its
member slot at 952–960, captures the live root, and enters instantiation. The
inspected publication and eligibility checks do not consume the synthetic
source registration. Therefore this control cannot establish withdrawal of an
already visible member graph, prevent incoming reuse of an invalidated graph,
or satisfy §7's initial published member plus certificate-dependent memo state.
No producer-to-consumer claim is made for uninspected alternate paths.

## Active-child order versus additional mutation

The native restoration already saves a count and an index, rather than frozen
endpoints. `candidate_opposite_count` at `candidate_extrusion.rs:570–593`
canonicalizes the owner and sums its direct and exact opposite vectors.
`candidate_opposite_bound` at 595–613 re-reads current canonical ownership and
the current direct/exact split. At 720–733 the active replay finishes before
the parent advances; at 735–758 the next product canonicalizes retained owner,
bound and opposite and constructs the exact ordered fiber.

Consequently an active child's callback can affect the lookup at the next saved
index. Freezing endpoints or pre-expanding products would change this operation.
That existing behavior is not a proof for an additional cross-component route
interleaved with a retained continuation: changing representatives or incidence
can change what the same saved index denotes. Suspension §4 requires a separate
replay/order correspondence before admitting such a mutation; a lifecycle
registration or endpoint footprint alone cannot discharge it. Keep incidence-
changing cross-component mutation deferred while that premise is open. This
note neither constructs a counterexample nor authorizes a new scheduler.

## Coverage, independence and next owner

One bounded static pass read pinned constructor/consumer slices and the three
assigned handoffs. No repository-wide absence search, Cargo, build, probe,
compiler/parser execution, test, formatting, Git mutation, or delegation ran.
There is no executable oracle, seed, input range or mutation run. The argument
uses direct source statements plus the selected contract; a checker supplied
with the same rules would add consistency evidence, not authenticate readiness
or complete observations. Earlier handoff conclusions are context, not an
independent review of this output.

The initial task-record read and one combined code capture were output-
truncated. Targeted slices supplied every locator used above; the truncated
captures support no exhaustive negative claim. Command calls were serialized;
some read pipelines contain transient Git/nl/sed or Git/rg subprocesses, so a
literal maximum of one OS process was not measured or established. No
heavyweight process ran. Wall time stayed within the assigned 20-minute static
pass; exact CPU, peak RSS and process counts were not measured. Writes stop at
this handoff; the primary owns checks and independent review.

Unverified scope: actual two-circuit recognition, authentic late unsupported
Function membership, source restoration with multiple remaining products at
that mutation, complete readiness/filter/transport witnesses, every observation
owner, ordered invalidated-sibling recomputation, route-wide inverses/accounting,
cross-component replay/order, all-source soundness/principality and production
cutover. No original parent obligation is narrowed or closed.

Recommended next action: assign the retained-input/source-recognition owner a
bounded constructor packet to supply one genuine readiness/filter/observation
witness and retain its support with the resulting observation through publication
and incoming-use eligibility. The consumer handoff must identify the exact
generation, typed retained input and invalidation/recomputation owner. If a new
representation decision is needed, return it through the existing review and
user-approval path before implementation. Do not replace this packet with
another synthetic adapter probe.

## Dependency identities and commit packet

Pinned Git blob identities; this worker changed no dependency. Primary must
recheck these against integration HEAD and independently review before any
status promotion.

| Dependency | Blob SHA-1 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `c38e880f2a2d3df1a97c33845004415baab154e8` |
| `crates/yu-solver/src/candidate_source.rs` | `632fb512ea8086ea8ed2065997ad619d582576ee` |
| `crates/yu-solver/src/candidate_scheme.rs` | `60fef24a74dc0e4d9c8a0c44fc37908cf73af1a9` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `8637ae9217b01ece8d536fc51f4ced220064015f` |
| `crates/yu-solver/src/lib.rs` | `38161f322080f81551486e224d07ab9443ed3ed9` |
| Suspension contract | `fd92fb5c62564455cb66e19059d147dfc20985e7` |
| Contextual admission design | `c99873544ca90aa817c77941514f7868a8023d65` |
| Source support ownership note | `0fd4874a1a3f0c029aa4e86c634e557ea377f12e` |
| Authentic source route note | `a73f758c83bcaafa806c5e678a4731c27acf4c4e` |
| Lifecycle architecture proposal | `998ce637758932b00a2a4574dc9d041ba4bec3e2` |

- Exact leased/changed path: `notes/progress/2026-10-11-lifecycle-constructor-consumer-feasibility.md`.
- Baseline: `d7e87c63723213550ac28ddab45e2ef47ce17f6e`.
- Changed dependency hashes: none by this worker; live dependency revalidation is
  left to the primary.
- Review status: unreviewed bounded static research; frozen, no closure claim.
- Checks already run: pinned `git show` reads, narrow `rg` symbol locators,
  read-only branch/status and `git rev-parse` blob identification. No executable
  checks or final primary integrity check ran.
- Proposed commit message: `research: trace lifecycle support constructor and publication consumer`.
- Shared-record deltas intentionally left to primary/curator: retain genuine
  readiness/filter/observation producer and propagation join as OPEN; record
  guarded future Local publication separately from withdrawal of published SCC
  graphs; keep cross-component replay/order, authentic §7, H3/W/A3 and production
  certificates OPEN. No shared task, index, theory, authority or question file
  changed.
