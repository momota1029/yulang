# Operation response instance witness lifecycle proposal

Status: UNADOPTED source/native lifecycle proposal, revision 3; no compiler-code
authority, accepted-source claim, theorem closure or production status.
Sprint: `operation-default-and-instance-lifecycle-20261017`, contract rev2,
SHA-256 `ed45bd2b259173a09897b7121e00fd7000a29286024571606edbfa631ce40f50`.
Author: Luna primary `/root`; bounded source/native design lane. Revision 3
repairs the compiler review's rollback-policy finding without changing other
claims, dependencies, or authority.

## 1. Goal and hard limits

This proposal makes the existing partial source/native joins explicit and names
the smallest durable identity record that could carry one operation-signature
instance from source construction to a matching runtime request and resume. It
is an identity/lifecycle interface, **not** a source typing rule or a complete
semantic substitution `θ`. The actual code currently constructs temporary
value/effect/view maps and drops them; those maps do not amount to complete
`D_B/P_B`, admitted responses, challenge observations, or output-dependent
futures.

`E_in*`, `E_out*`, the entry/default contract and complete original B remain
open under the pinned candidate proposal. This lifecycle proposal assumes none
of those missing fields. It cannot repair `OPRESP-DEFAULT-1`, `OPRESP-ENTRY-1`,
`OPRESP-DOMAIN-1`, or `OPRESP-CONTEXT-1`.

The design preserves these distinct identities and values:

```text
DeclarationKey   = SourceOperationId(family, declaration_source_key)
StaticUseKey     = (source_root, operation_expression_occurrence, DeclarationKey)
DynamicEventKey  = (StaticUseKey, fresh_request_event)
Response B       = original operation's response value interface
Answer A_S       = result after the saved operation suffix consumes B
```

Declaration or family equality alone cannot choose a static use. Equal value
or effect endpoints cannot reconstruct an instance substitution. A saved event
is historical lineage and cannot grant current handler eligibility.

## 2. Existing construction and consumer path

The currently inspected path is:

```text
SourceOperationDeclaration
  → Action::Operation(owner, operation occurrence, target, level)
  → candidate_operation(signature maps, slot 42)
  → Action::CatchOperation(declaration, owner, arm-body occurrence,
                            payload?, continuation?, original, effect, level)
  → candidate_catch_operation(separate signature maps, slots 60–65)
  → source/runtime adapter (identity join not established here)
  → OperationPayload / OperationResultConsumer
  → PendingRequest(declaration, source, fresh event, observations, suffix)
  → capture_template after eligibility / pattern checks
  → ResumeTemplate(nodes, declaration, original_event)
  → ResumeArgument(response check) / ResumeReturn(saved suffix result
                                                   A_S)
```

`SourceOperationId` already pairs family identity with the declaration's
`SourceNodeKey`; `SourceOperationDeclaration` separately retains signature and
name positions. The `Operation` action carries the resolved declaration, source
owner, source expression occurrence, target endpoint and level. Runtime
`PendingRequest` retains the actual `SourceSite` passed to request construction,
the resolved declaration and a fresh event. These field sets are sufficient to
propose `StaticUseKey` as a structural cross-view key, subject to a future
constructor-level identity assertion. The inspected chain does not yet prove
that the candidate Action's `(owner, occurrence)` equals the runtime
`SourceSite` at the source-to-runtime adapter; that equality remains an explicit
correspondence obligation.

The current candidate solver does **not** retain the complete typed mapping:
`candidate_operation` allocates local `values`, `effects` and `views` maps,
builds the positive declaration value and admits slot 42, then drops those
maps. `candidate_catch_operation` allocates a different set of maps. For a
continuation binder it forms response value ports against the original
scrutinee endpoint (slots 62/63), and separate entry/full-scrutinee effect
relations (slots 64/65). For a Unit payload pattern, `payload=None`; slots
60/61 are absent. Neither candidate constructor emits a retained semantic
`θ` or a certificate for all original B cases.

Runtime `PendingRequest` has the resolved declaration, the operation `SourceSite`,
fresh event number, observations and saved suffix. The matched Catch arm is
selected by resolved declaration identity and the actual request's phase data;
its static `CatchOperation` occurrence is the arm body, not a unique originating
operation use. Therefore the match must carry the actual request's use/event
key forward. It cannot look up a unique instance from the Catch arm's source
occurrence.

`capture_template` validates/builds nodes locally and appends one
`ResumeTemplate` only after materialization checks pass. That template currently
retains nodes, root, declaration and original event, but not the request's
source root/operation occurrence or a semantic instance witness. The inspected
candidate constructor does not publish its temporary maps into these runtime
records. Thus no direct candidate-map-to-runtime-consumer edge is established
by this audit.

## 3. Proposed minimum lifecycle interface

The following is a source-identity witness interface, not a newly selected
language constructor or value/effect meaning:

```text
OperationUseWitness {
    key: StaticUseKey,
    source_occurrence: original operation-expression occurrence,
    declaration_signature_identity: original signature SourceNodeKey,
    map_trace: exact constructor-produced value/effect/view map entries,
    generated_constraint_origins: exact originating occurrence/slot IDs,
    completeness: PartialConstructionTrace
}

RequestInstanceWitness {
    key: DynamicEventKey,
    declaration: DeclarationKey,
    original_operation_site: SourceSite,
    provenance: reference to OperationUseWitness,
    response_status: Unresolved | CheckedPrimitiveResponse
}

ResumeInstanceWitness {
    key: DynamicEventKey,
    declaration: DeclarationKey,
    operation_use: StaticUseKey,
    suffix_answer_role: A_S,
    witness_status: PartialConstructionTrace
}
```

`map_trace` records only the exact temporary constructor outputs already
produced for this use. It must be labeled partial and must retain original map
keys/values without asserting that they encode semantic `θ`, complete B, or
all dependent observations/futures. The event record identifies which dynamic
request used that static expression. Repeated evaluation of one static use
creates different event keys; two static uses of one declaration create
different use keys even when their projected ports happen to be equal.

The next design-level steps are:

1. At a source-expression constructor whose identity bridge is independently
   established, mint or preserve one
   `StaticUseKey` from the actual `SourceRootId`, `HirOccurrenceId` and resolved
   declaration ID. Retain it on both the candidate Operation action and the
   runtime Operation instruction. Reject disagreement; never join by spelling.
2. At candidate signature generation, stage the actual `values/effects/views`
   map entries and emitted-origin list under that key. Publish a
   `PartialConstructionTrace` only after the constructor finishes successfully.
   `CandidateInference` must name its source component/epoch if it exposes such
   records, so IDs from another solve cannot be mistaken for this instance.
3. At runtime request creation, derive `DynamicEventKey` from the Operation
   instruction's `StaticUseKey` and the newly allocated event. Store it in
   `PendingRequest` with the same declaration and original `SourceSite`.
4. At a Catch match, check the original resolved `DeclarationKey` against the
   request and carry that request's `DynamicEventKey` into the continuation
   wrapper. A catch pattern is only the consumer selector; it does not supply
   or synthesize the signature mapping.
5. At template capture, include the exact `DynamicEventKey` and
   `StaticUseKey` in the same `ResumeTemplate` object as nodes, declaration and
   original event. The current append-after-validation point is the proposed
   commit boundary. `ResumeArgument` may receive a typed witness only after an
   independent complete response constructor and current admission checks
   exist; the identity record alone cannot authorize or validate B.
6. At resume, assert template/event/declaration consistency, then preserve
   `Response B` as the input value and the suffix's actual result as `A_S`.
   Do not restore the old event as a current event or reuse the old handler
   eligibility.

This interface addresses the missing *identity route*. The actual source-to-
runtime construction edge, candidate solve epoch/retention owner, and
complete semantic field transport remain separate proof and representation
obligations. In particular, the present Function-response specimen is refused
before capture/pop, so it does not demonstrate a successful instance witness
through resume.

## 4. Validation, ownership and failure

The existing constructor fields give useful validation boundaries:

| Boundary | Existing facts | Proposed check | Current status |
|---|---|---|---|
| Source resolution → candidate action | source owner, operation occurrence, declaration ID and target | source root/occurrence/declaration key agrees with the authentic lowered operation node | Not retained as a single key |
| Candidate Operation generation | declaration signature, temporary value/effect/view maps, slot 42 origin | trace key equals the current action key; all map entries and origins belong to this constructor/solve epoch | Maps are dropped; no persistent record |
| Operation → runtime request | pending request's source site, resolved declaration and new request event | source root/occurrence/declaration match; event minted once and is unique | Request retains source/declaration/event but no solver witness link; source/runtime adapter equality remains open |
| Catch selection → capture | request event/observations/suffix, target declaration, local grant and pattern | exact declaration match; carry request key; finish all validation before publication/pop | Runtime ordering exists; key is partial |
| Capture → resume argument/return | template handle, declaration, original event, saved nodes | verify same event/declaration/use; keep old event historical and actual suffix answer A_S | Template lacks source use key and semantic witness |

The source/solver session is the owner of candidate map traces. It should own
the trace until its solve/candidate artifact is disposed; the runtime machine
is not allowed to borrow a dead solver session or silently use a different
solve's component IDs. The runtime machine is the owner of each request-event
record and any captured template. Template-held identity is released when the
machine drops it; it is not a global declaration registry. `SourceOperationDeclaration`
may remain shared through its existing `Arc`, but that lifetime does not own a
per-use substitution.

Failure policy for a future implementation must preserve sound externally
visible results while allowing safe termination or discard of a private attempt:

- Candidate generation may stage new trace entries while the signature
  constructor runs. Constructor, identity, or resource failure must not publish
  a partial candidate result. If constraints have already changed state owned
  by a private inference attempt and the attempt can no longer continue
  soundly, terminate or discard that whole attempt. Rollback is required only
  when the owner establishes an invariant or intended reuse that needs it.
  Publish a completed candidate result and its trace as one externally visible
  result.
- Runtime should stage an extended `ResumeTemplate` fully, including witness
  key, before its existing append/publication point. If template validation or
  allocation fails, no template or witness record becomes visible and the
  Catch frame is not popped. If later arm setup fails after template
  publication, safely terminate or discard the affected private machine attempt
  without exposing an inconsistent result. Add a rollback guard only if the
  machine is meant to continue/reuse that state or its owner identifies a
  semantic invariant that requires rollback; setup need not be made infallible
  as a general rule.
- A stale key, foreign solve epoch, mismatched declaration, or missing
  dependent witness fails closed with the existing unavailable/invalid-source
  path until a reviewed error contract is selected. It must not fall back to
  family equality, same-shaped endpoints, or reconstructed maps.
- Abandoning a suffix may release only records exclusively owned by that
  suffix/event. It must not delete another static use's shared immutable
  operation trace, alter an outer initializer's publication owner, or grant
  current eligibility.

No existing runtime byte/event budget for retained resume templates was found
in the pinned owner path. A code proposal must add checked byte/count accounting
and deterministic limits, and must not externally publish a result that exceeds
those limits. It may stage fallible capacity before mutation when the owning
machine or inference attempt will continue; if a private attempt cannot remain
sound after failure, it may instead terminate or be discarded. In candidate
inference, `Plan::bytes`, `scratch_bytes` and `sample_f4_resources` provide
existing accounting seams; adding retained maps must charge key/value
capacities and source-owner payloads at `SourceDrafts` and `IncomingRoute`,
with checked arithmetic. Exact counters, numeric limits and any rollback need
owner verification before code; no atomic solver rollback is presumed without
an identified invariant requiring reuse.

## 5. Open gates, falsifiers and next owners

The design is falsified as a same-instance route if any of these occur:

- Two operation sites with one declaration or equal endpoint projections
  resolve to the same static-use record.
- Two requests from one static operation site reuse one dynamic event key.
- A Catch consumer chooses a map from arm identity instead of the actual
  request's operation-use/event key.
- A template loses the operation-use key, treats historical event data as a
  current grant, or changes B into the saved-suffix answer A_S.
- Missing semantic θ, challenge/observation fields, or future projections are
  silently inferred from identity fields or candidate map entries.
- Partial publication survives a failed constructor/capture, exceeds the
  selected resource bound, or is not reclaimed by its actual owner.

Remaining gates:

- `OPRESP-DEFAULT-1` / `OPRESP-ENTRY-1`: original owner must select/default
  omission and complete entry meaning; the preceding source audit found no
  governing rule that entails C-OMIT.
- `OPRESP-DOMAIN-1`: original response/descriptor owners must prove
  tuple-preserving coverage of every original response, challenge, observation,
  provider, world and future, in both interface directions.
- `OPRESP-CONTEXT-1`: ApplyOne owner must construct the original typed
  punctured context, current world and complete registered carrier.
- `OPRESP-NATIVE-1`: source/native owner must establish that this partial use
  key and trace survive the actual generator-to-runtime boundary without
  CandidateInference being silently imported.
- A later approved design and code lease must settle resource limits, owners,
  failure handling and atomic externally visible publication. Any rollback
  requirement must be tied to an identified owner invariant or intended reuse.

No compiler code was changed and no safe code slice is selected. This is the
smallest lifecycle design that preserves actual identities while exposing the
first missing fields. A future code review must not treat this proposal's
identity trace as an adopted semantic certificate or as permission to alter
ordinary inference behavior.
