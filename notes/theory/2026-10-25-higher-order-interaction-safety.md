# Higher-order repeated interaction value safety

Status: candidate mathematics; author has NOT_RUN Lean, tests or builds. Fresh
independent review and primary elaboration are pending. No production authority.
Author: `/root/higher_order_interaction_astra_r1`, requested `gpt-6-astra/medium`,
observed model/effort UNKNOWN. No descendants or other contributing authors at
this author freeze. Any primary repair after acknowledged STOP adds coauthorship.
Contract: `GUARD-INTERACTION-THEORY-20261025/r1`, lane B, HO-INTERACTION-1.
Baseline: `e9c0a89d2f92ac0116a75e5c7e24623e4c38acd9` (supplied; no Git invoked).

## Original parent and exact contribution

The original parent is the execution type-safety theorem in
`docs/yulang-operational-type-safety-ja.tex:1139`–1159. It quantifies over every
finite prefix of internal transitions, typed external responses and multiple
resumptions, allowing stopping at a request; returned callback code is typed.
Its graph extension and metadata clauses remain part of that original claim.
The request-cut lemma at 1047–1066 and raw resume discussion at 458–472 are the
precise supporting parent obligations. They are research targets, not adopted
compiler semantics.

The new module `lean/YulangClosure/HigherOrderInteraction.lean` supplies a
candidate repeated-interaction proof for the accepted finite HigherOrder
research grammar. The response, saved handle, outer evaluation context and
finite trace are independently quantified. It extends the accepted internal
trace safety construction with real request capture and arbitrary old-handle
responses. It does not substitute one lambda frame action for F1/FK1 or identify
this value-typing projection with the paper's complete raw Resume operation.

`closed_program_interaction_safety` starts with only a closed typed computation
and an EMPTY saved arena. `finite_saved_response_safety` applies the result to
ANY entry captured during ANY such finite trace and ANY closed response having
that entry's own operation response type. It supplies actual publication
provenance, the original result type, all saved-entry typing, and resumed
progress. Thus captured continuation typing is not an assumed initial resource.

## Raw construction and proof chain

`Saved` retains the full operation instance, exact payload, original
response-binding continuation and entire `Safety.EvalContext`. Its fields carry
no typing derivations. An arena is a finite list. Handles are natural-number
positions; publication appends at the old length. `lookup_append_old`,
`lookup_append_fresh` and `lookup_length_none` establish stable old entries and a
fresh position. No allocation or response mutates any old saved record.

`RawStep.internal` embeds the accepted `Safety.Step`; `RawStep.publish` matches
only a current computation that IS the saved context plugged with that exact
request; `RawStep.response` looks up an existing handle and substitutes the
provided raw value into its original response binder before plugging the entire
saved context. Response is permitted from any phase and any old handle, so an
external scheduler can revisit saved continuations in any order. No raw rule
contains typing, preservation, or a protocol premise. This is an abstract
interaction scheduler, not a claim about native API authentication or scheduling.

`Protocol` is separate. Internal and publication events impose no external
obligation. A response must identify the FULL saved operation instance and have
its exact response type under the empty context. Full-instance equality retains
operation identity, ordered type arguments, payload type and response type;
equality of merely the last type is insufficient. The protocol never postulates
that a response exists. In particular a bottom response type can legitimately
leave the execution waiting forever.

`capture_typed` inverts the actual current computation with
`Safety.context_inversion`, then inverts `CompTyped.request`. This derives exact
payload typing, the continuation under the operation's response binder, and
`ContextTyped` for the whole enclosing context. `saved_resume_typed` uses the
accepted substitution theorem and `plug_typed` on those derived witnesses.
`step_preservation` applies this at publication, preserves all old entries, and
uses independently supplied response typing only at response steps.

`Trace` combines raw steps with the explicit external protocol, without adding a
preservation premise. `finite_interaction_safety` proves the same result type,
ALL saved-entry typings, concrete progress, and exact equality of all initially
saved entries after EVERY finite trace. `trace_origin` additionally shows that
each final entry either existed initially or has an exact publish event at that
handle in the trace. `initial_saved_origin` eliminates the initial-data case.
`typed_response_association` combines the saved payload and continuation facts
with the externally supplied instance and response typing.

`Progress` has precisely four forms: a running Ret, a running failure at a
finite evaluation-context hole, a wait at an existing exact saved request, or
an actual protocol-respecting next step. It has no arbitrary-stuck constructor.
`plug_suspended` and `publication_has_no_internal_step` show that publication
comes from a genuine suspended evaluation position. `state_progress` derives
publication when the accepted closed-progress theorem exposes a request.
No response availability or fairness is required for progress at a wait.

## Distinguishing constructions

All rows below are Lean statements/proofs in the candidate, pending checking.
They are not claims that a native constructor generated the modeled transitions.

| Case | Candidate evidence |
| --- | --- |
| Every finite repetition at the same handle | `repeat_handle`, arbitrary list of independently typed values |
| Different handles in arbitrary order | `handles_in_any_order`; both handles/values independent, revisits the first |
| Old handle after a later capture | `capture_then_old_response`, using append preservation |
| Two distinct responses to one capture | `two_distinct_responses`, false then true; `two_response_safety` applies the parent invariant |
| Another request after resume | `new_request_after_resume`, five real interaction events with two further publications and reuse of handle zero |
| Higher-order response with typed code | `callable_response_trace`, `callable_response_typed`, `callable_response_can_progress` |
| Same types, wrong operation identity | `wrong_operation_example`, plus general `wrong_instance_rejected` |
| Missing handle | `missing_handle_rejected` |
| Uninhabited response type | `bottom_wait_trace`, `bottom_wait_safety`, `bottom_wait_no_response` |
| Retained bind/scope/expose context | `nested_request_typed`, `nested_resume_equation` |
| Exact arena immutability | `step_immutable`, `trace_immutable` |
| Actual capture provenance | `step_origin`, `trace_origin`, `initial_saved_origin` |

## Reuse, source boundary and remaining obligations

The accepted HigherOrderSyntax grammar and typing are unchanged. The accepted
HigherOrderSubstitution binder lifting and `substitute_top` are reused only for
that grammar. HigherOrderEntry supplies its already accepted lambda/wrap entry
constructions; HigherOrderSafety supplies all internal constructor preservation,
closed progress, actual evaluation contexts, context inversion and plugging.
Its old internal-only trace theorem is not reused as though it already included
external responses. The new Trace induction fills that specific gap.

Formal producer-to-consumer evidence is explicit:
`Comp.request` / `CompTyped.request` -> `Saved.request` / `RawStep.publish` ->
append-only arena lookup -> `RawStep.response` / `Saved.resume` ->
`substitute_top` / `EvalContext.plug` -> accepted internal execution. This is a
source-to-construction correspondence within the finite research syntax only.
There is no new inference constraint-generation/accumulation/propagation claim
and no native audit. Simple-sub levels, extrusion, qualifying intrusion,
generalization and every ordinary inference path remain outside this change.
No withdrawn bypass or residual/provider/witness collapse is introduced.

The original paper theorem remains OPEN for graph-bearing responses and fresh
immutable graph extensions, handlers and their arms, mapop, and the paper's Wait
constructor and forwarding frames. `Interaction.Phase.waiting` merely records
an exposed request; it does not implement that omitted language constructor.
The current `HigherOrderSyntax.Comp` and `Safety.EvalContext` lack those forms;
Luna owns any future syntax allocation and their preservation/progress proofs.

Owner/view freshening, live metadata interpretation, effect hygiene, linearity,
full F1/FK1 and native operation/response authenticity remain OPEN. This module
preserves metadata as existing immutable syntax and does not rename saved scope
owners for a fresh resume. Those clauses belong to the paper's full Resume/view
and graph semantics and require independent construction and authority; they
cannot follow from a value-typing theorem. The prior source inventory
`2026-10-25-higher-order-source-constructor-map.md` remains the native/source
ownership locator. Native entry, capture, dispatch and response owners were not
audited by this assignment. No new code TODO is justified without that evidence.

The exact next in-contract step belongs to Luna: elaborate the frozen module,
inspect theorem signatures/axioms and distinguishing constructions, acknowledge
any author-to-primary repair transfer, then appoint a fresh nonauthor reviewer.
The author cannot certify this candidate. No compiler/test or shared-record edit
is requested. A future expanded full-paper lane requires a new exact allocation.

## Frozen dependencies and resources

Contract SHA-256:
`1d872d3972784a4f96be0d86002efa1c3e5ca369dbff6325cde86ce6537dac06`.
The direct import is HigherOrderSafety; the following exact supporting files were
read or pinned. The contract retains the complete transitive dependency manifest.

| Dependency | SHA-256 |
| --- | --- |
| HigherOrderSafety.lean | `16a38dbb649677ed5e6b6371a61228a1724b9e899136eeb2119b755ecab30336` |
| HigherOrderEntry.lean | `c9cb839ff6b34ed97c5d72f9e020437d32175cf517a5841a3a024764747c213b` |
| HigherOrderEnvironment.lean | `84a461fdff85e7321cf090ba2bb72a7d90415515a2da1eb15e1287ef0361ab83` |
| HigherOrderSubstitution.lean | `19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30` |
| HigherOrderSyntax.lean | `ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972` |
| Higher-order research design | `50eb7ebd2ed2d155dfeca2e3ce99f3f5b990cc4f1bf101663949a04d8d4b748f` |
| Operational paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |

Budget: 900 wall seconds from dispatch acknowledgment. First recorded active
receipt was 2026-10-25T06:49:25Z; the primary retains the exact launch receipt.
Final STOP time, elapsed bound and artifact hashes are in the single assigned
inbox. Shell reads, writing and byte hashing only; Lean/build/tests/checker,
Git, external contacts and child spawns all NOT_RUN. No scratch paths or
persistent processes. New paths are exactly this note, the Lean module and
`tasks/agent-loop/inbox/20261025-higher-order-interaction.md`.

## Primary repair and verification intake

After actual author STOP at 06:55:09.325693 UTC and acknowledged lease takeover,
/root became a coauthor. Original author inbox remains immutable. Primary renamed
the reserved Lean binder instance to instanceEq and made saved records explicit
in response_protocol example applications; raw semantics, protocol premises,
trace quantifiers and theorem conclusions were unchanged. The final module
elaborates; all 82 public declarations have signature/axiom queries. The combined
query includes 23 distinguishing examples across both lanes, including repeated
responses, resumed new requests, callable responses, missing/wrong handles,
uninhabited response waits and exact retained context. Row 16 reported no
Classical.choice, sorryAx or other new axiom; allowed closures are only propext
and Quot.sound. Final rebuild will bind this note to the final receipt. Fresh
independent nonauthor review/adjudication remain pending at this note freeze.

Final primary-repaired Lean SHA-256: 45f2b8c74e2837e503db84aed3c9f55767a32d19e4008546e25a01cef1202875.
