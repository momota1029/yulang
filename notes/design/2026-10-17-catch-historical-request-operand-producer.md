# Draft: producer contract for a historical Request operand across Catch exit

Status: unadopted source-contract proposal and static producer/consumer map.
No compiler-code authority, accepted source rule, source-semantic theorem,
implementation result, or production promotion. The existing fixed Function
response specimen still fails its response-shape guard before capture/pop.

Sprint: `catch-response-challenge-and-historical-operand-20261017`, contract
revision 2, SHA-256
`f5d781851e0a2babcf3a6ea4746c97ecb97acc0777fc8a73d7a6b7ab08a7e057`.
Source baseline `7eb34a0a9`; exact compiler checkpoint `9d455a6f8`.

## 1. Question and outcome

The proposed `InspectRequest_μ(q; z.c)` needs the same historical Request
operand after the original Catch exit, with the original payload, operation
instance, event evidence and complete saved raw continuation still tied to one
request. This note asks what a producer must retain, how its fields evolve, and
where the outside consumer would take them.

There is no such complete runtime record today. Runtime state retains a staged
partial projection: some Request fields exist at emission, execution creates an
event and observations, unwinding extends a suffix, and capture creates a
template. The target declaration additionally needs typed source/Event,
response, provider and world incidence that runtime IDs and references do not
certify. A separate post-pop metadata operand is not currently exposed to the
selected arm.

The result is an unapplied producer contract and exact missing-input list. It
does not settle whether the proposed source rule is adopted or whether this
fixed Function-response specimen reaches its consumer.

## 2. Required operand at the source boundary

Use the original target proposal's Event telescope and Request derivation δ;
do not select a subset of Event fields. At the original `μ_H`, the desired
operand remains the dependent tuple

```text
q = (declaration, θ, provider/instance, admitted payload view,
     origin and event, emission C_y/J_y/ρ_y where declared,
     original typed observation/evidence fields, Δ_q, whole saved S/raw).
```

`HistoricalMeta(q)` from the target proposal is the authority for this
candidate field order. The following runtime comparison is structural and
does not identify its fields with that semantic telescope:

| Target field | Current runtime carrier | Change/lifetime | Missing semantic evidence |
|---|---|---|---|
| declaration and operation signature | `PendingRequest.declaration: Arc<SourceOperationDeclaration>`; copied into `ResumeTemplate.declaration` on capture | Declaration reference is immutable through this path | No proof that this reference alone gives the complete original `Δ_q.B`, its `D_B/P_B`, or same-tuple hereditary response projection |
| θ, provider and operation instance | Declaration identity, `SourceSite`, and references in the source program | Static identity; not one whole runtime field | No typed family substitution, actual provider view, or same-assignment evidence is assembled into a historical Event certificate |
| payload and admitted payload view | `PendingRequest.payload: ReceivedValue` (`ValueHandle`, interface role, view handle) | Carrier reference stays attached to this pending request; selected variable binder may copy it to the arm environment | A runtime value/view handle does not prove the original complete `P_op[θ]` view or provider-to-port map |
| origin | `PendingRequest.source: SourceSite` | Immutable request-expression site | Source site is not the source Event derivation or all constructor arguments |
| event identity | `execute` mints `event` once and stores it in `PendingRequest.event` | Fixed identity; not a current-state snapshot | Numeric equality alone does not prove a typed Event or authorize restoring its old world |
| observations/evidence | `PendingRequest.observations: Vec<Observation>`; each contains execution view, observer index and event | Created once at event execution; consumed for original pre-pop grant checks; moved into `SavedContinuation` on unhandled stop | These runtime handles do not encode the full typed observation telescope or recreate `C_y/J_y/ρ_y` |
| raw suffix S | `PendingRequest.suffix: Vec<SavedFrame>`; `propagate_request` appends frames while unwinding | Mutable until exit/capture | No complete semantic source frame typing is derived from frame storage |
| captured raw operand | `ResumeTemplate { nodes, root, declaration, original_event }` | Created only on a supported continuation-capture branch | Template omits payload, source, observation vector, provider and typed `Δ_q`; matching IDs only checks lineage |
| outside consumer operand | No field in the selected post-pop arm environment; current arm receives a payload binder and optional opaque continuation binder | Would have to be explicitly passed or retained by a source/runtime extension | No existing post-pop `InspectRequest` consumer or source/native typing certificate |
| current C/J/ρ and eligibility | Live machine/receiving/invocation state, not captured in `ResumeTemplate` | Changes as frames unwind and owners end | Historical evidence cannot be converted to current eligibility or restore `C_y` |

The outside operand cannot be a copied active-handler snapshot. Its historical
indices explain the original Request; current state and eligibility remain the
actual `C_out/J_out/ρ_out/G` after exit.

## 3. Actual producer sequence and exact join

At Request execution, the runtime sequence is structurally:

```text
ExecutableValue::Request { declaration, payload, source }
  -- execute -->
PendingRequest { declaration, payload, source,
                event := next_request, observations := observe(event, views),
                suffix := [] }
```

The `event` is created once at execution, and `observe` records the then-live
executions. It is not created from source text alone. As a Request unwinds,
`propagate_request` appends each converted `SavedFrame` to `suffix`. A
successful continuation-capture branch calls `capture_template` on that
completed suffix, appends the containing owner node, then stores
`ResumeTemplate { nodes, root, declaration, original_event }`. The same
`propagate_request` branch validates installation, declaration, local grant,
signature/effects, payload and supported response shape before capture and pop.

The candidate retained producer is therefore staged, not one fabricated
creation-time tuple:

```text
RequestSeed(q0) := (declaration, payload-view, source, event, observations)
PendingRequest(q0, suffix_i) -- each real unwind step --> PendingRequest(q0, suffix_{i+1})
RequestExit(q0, S) := (same q0, captured template for the completed suffix)
```

This is an unapplied representation sketch. `RequestSeed` and
`RequestExit` are not current runtime types or adopted semantic constructors.
If a real producer is selected, ownership must be linear and explicit: move the
same seed through pending state, append only the actual frames, and join it to
the template built from that exact suffix. A global table keyed by `event`, a
replay of Request emission, or reconstruction from declaration IDs is not an
equivalent producer.

The required validation equations for that future producer are:

```text
exit.declaration       = seed.declaration
exit.payload_view      = seed.payload_view
exit.origin            = seed.origin
exit.event             = seed.event = template.original_event
exit.raw               = the template rooted at the actual completed suffix
exit.observations      = seed.observations (or exact references to the same set)
exit.current_context   = actual post-exit context; never seed/emission context
```

Equality above is a candidate representation invariant. It is not a typed
proof of the corresponding dependent source equality. A future source
constructor must separately produce a dependent correspondence for every
Event telescope field, at the original indices, from δ's actual Request
constructor. A source/native theorem must carry those same witnesses through
the existing exit action. Retention alone proves neither field typing nor
preservation.

## 4. Proposed consumer contract and validation

For the target proposal, the only coherent consumer is its original
`InspectRequest_μ(q; z.c)` at the original `μ_H` after the existing exit ε.
It consumes the already threaded operand `q`; it must not search for q or make
a new observation. A future source constructor must provide these premises
before declaring the use:

1. δ supplies the complete original Event constructor and each field at its
   declaration, including the actual typed payload view and `Δ_q`.
2. The same Request path owns one RequestSeed and one continuation suffix.
3. ε transports that same seed, and the completed suffix becomes that same
   whole raw operand S; the dependent raw schema still names all original
   response/body/answer/future fields.
4. Any capture/pop guard remains at its original active-H phase. No old
   observation, owner or grant becomes a current post-exit fact.
5. `μ_H` receives the operand at its original output-dependent seam. The
   administrative metadata read changes no world/history/evidence and emits
   no event, boundary, grant, response or observation.
6. Dependent substitution is checked field-by-field in the declared order;
   source occurrence, response provider, and output future retain their
   original same-tuple incidence.

Current runtime facts satisfy only a subset of these shape obligations on
successful primitive-response sibling paths. For the fixed specimen,
`propagate_request` rejects the Function response before `capture_template`,
Catch pop and selected outside-arm evaluation; it has no actual post-exit
operand instance. The unhandled-request route moves observations and frames
into `SavedContinuation`, then stops; it supplies no selected outside consumer.
Neither path establishes the proposed source constructor or a source
counterexample.

## 5. Application, gaps and falsifiers

The architectural hypothesis that a retained historical operand could
support outside metadata elimination remains plausible as a *representation
shape*, conditional on an authentic constructor. Exact current owner joins:

| Producer/consumer owner | Evidence present | Still missing |
|---|---|---|
| Request creation and `execute` | Declaration, payload-view, source; runtime event and observations | Complete original typed Event/`Δ_q` construction and an owned outside operand |
| `propagate_request` / `capture_template` | Actual suffix accumulation, ordered template, declaration and event lineage | Full Request record retention on captured template, source-level typed equality and a consumer after pop |
| selected outside Catch arm | Existing payload and optional continuation binding after successful checks | Historical Request metadata input, typed use, full raw/interface preservation; fixed Function response is unreachable before this phase |
| `InspectRequest_μ` target proposal | Candidate same-q read and local unchanged-state clause | Adoption, authentic producer premise, actual outside typing, complete Event and source/native preservation |

Falsifiers for this candidate are: any field is regenerated from an event ID;
the record drops the original payload/provider/observation or raw/future
incidence; retained `C_y` is treated as current `C_out`; a grant is moved past
pop; raw S is narrowed to a primitive response or selected `id`; an outside
consumer is asserted on the fixed Function-response specimen despite its
pre-capture guard.

No source rule is adopted here. No compiler code is warranted: extending
`ResumeTemplate`, changing `propagate_request`, or widening Function-response
support before the missing formation/use laws are settled would create a
provisional runtime surface without a valid typed operand or reachable
consumer.

## 6. Parent application and exact next owner

This contract does not establish `M_exit`, `TypedMatchInput`, target-rule
adoption, full raw continuation typing, source/native correspondence or the
original theorem. It does not repair the separate earlier proof obstruction:
the original operation response/signature owner must first supply complete
`Δ_q.B`, `D_B/P_B`, and its same-tuple hereditary response projection. Only
then can the ApplyOne owner introduce the actual checked `d_B(τ) ∈ D_B`.
Keeping a runtime/declaration handle does not supply that semantic formation.

All original A/B, F1/FK1, `M_exit`, source/native, implementation and
production gates remain OPEN. Parent application is **NO CHANGE**. The next
proof admission needs a concrete versioned response/signature constructor or
a separate source-rule definition packet at that owner, independently frozen
and reviewed before ApplyOne challenge introduction resumes.

## 7. Provenance, review, checks and limitations

Reused only within their stated scope: the target-declaration proposal and
its exact HistoricalMeta/InspectRequest clauses; the corrected rev2 metadata
correspondence; the frozen ApplyOne checked-challenge obstruction; source
contract §3.3; contextual Function §2; and direct static owners
`PendingRequest`, `execute`, `propagate_request`, `capture_template`,
`ResumeTemplate`, and `Receiving::observe`. Their bytes and pins are in the
contract. This note is new and unadopted; none of those sources claims a
complete historical operand producer.

No tests, builds, runtime execution, probes, code edits or expected-output
changes. Static source/design reading and exact SHA-256 checks only. The
Function-response specimen remains rejected before capture/pop, and no
successful fixed-case output is claimed. Independent compiler, spec and
architect reviews are pending. Requested role: Luna/high; effective model
metadata: UNKNOWN. Stop condition: any need to define accepted semantic
formation, change a guard, or infer typed Event evidence returns to the source
formation owner and dispatcher.
