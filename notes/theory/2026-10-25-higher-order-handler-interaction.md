# Root publication and repeated higher-order handler interaction

Status: candidate mathematics; UNCHECKED and UNREVIEWED at author freeze.
Author: `/root/higher_order_handler_interaction_astra_r1`; requested
`gpt-6-astra/medium`; observed model/effort UNKNOWN. No descendants.
Contract: GRAPH-HANDLER-INTERACTION-THEORY-20261025/r1, outcome B;
SHA-256 `7f9dd634a1a70b082033518d8d46a936fb4e78b1780c4cb373166d72f5a65467`.
Baseline supplied by primary: `d94c36b61dc140ba9fa1441c9cab9e0577280392`;
no Git invoked. No production authority or independent certification.

## Original claim and application

The parent is HO-SHALLOW-HANDLER-1 and the arbitrary finite execution theorem in
`docs/yulang-operational-type-safety-ja.tex:1139`–1159. Handler semantics at
399–456 and local handler/resume preservation at 1069–1088 retain the distinction
between original K (response Q to handled input A) and forwarded HK (Q to output
B). The parent permits arbitrarily many internal steps, independently typed
external responses, repeated resume and stopping at a request. Callback code is
typed. Its immutable graph extension, full syntax and live metadata clauses
remain part of the original claim and remain OPEN.

`HigherOrderHandlerInteraction.lean` supplies the repeated-interaction argument
for the entire frozen finite Handler grammar, including handler forms recursively
inside values, computations, adapters, trials and saved continuations. It does
not import either new graph-lane artifact. This candidate removes the missing
arena/interaction construction for this grammar; it does not close the original
full-paper, native, F1/FK1, foreign-continuation or inference A/B obligations.

`closed_program_interaction_safety` begins with only a closed typed computation
and EMPTY arena. For EVERY finite trace of raw transitions satisfying the
separate response protocol, it derives the original current result type, all
saved payload/continuation types and concrete progress. `trace_immutable` retains
exact equality of every prior saved record at its original handle. From the
empty arena, `initial_saved_origin` ties EVERY final saved record to a publication
in that trace. `trace_publication_split` supplies the actual prefix, publication
transition and suffix; `publication_root` identifies that transition's current
root request and append position. `empty_arena_safety` bundles typing, progress
and actual root-publication witnesses. `finite_saved_response_safety` applies the
invariant to EVERY saved handle and EVERY independently typed matching response,
yielding publication provenance and typed/progressing resumed state.

## Construction and proof premises

Saved contains exactly the full OperationInstance, actual payload and actual
root continuation. Publication has one raw constructor, applicable only when
the running current computation is `Saved.request`. There is no EvalContext,
interior extraction rule, masking bypass or capture under a handler. Inversion
of the typed current root request gives both payload typing and continuation
typing; neither is a premise of raw publication. `handler_cannot_publish` makes
the direct handler-bypass exclusion explicit. Interior bind/scope/expose/handler/
trial/wait propagation uses the imported actual Handler.Step and its accepted
preservation theorem. No assumed evaluator transition is substituted for it.

Raw internal steps, publication and response are defined without typing facts.
The separate Protocol requires exact FULL operation-instance equality and a
closed response of that entry's own response type. Identity, ordered type
arguments, payload type and response type are all in the compared instance.
Wrong instances and missing handles are rejected by independent lemmas. Capture
preservation uses root inversion; response preservation uses the saved entry's
actual continuation substitution. Finite trace induction then establishes the
invariant. Progress distinguishes actual outer return, actual outer failure,
coherent published waiting state, or a concrete admissible next transition.
Bottom responses are not postulated: a typed bottom request can be captured and
wait, while `bottom_response_unavailable` excludes any admissible response.

Scheduling deliberately follows frozen HigherOrder.Interaction: ANY existing
handle may replace the current branch in either running or waiting phase,
including after termination of another branch. Reuse never consumes an entry.
An earlier saved handle can therefore be selected after a newer publication.
This is the prior research arena interface, not a theorem about native scheduler
permissions. The theorem assumes independently typed supplied responses rather
than claiming a native parser/host produces them. Metadata is retained syntax;
retention is not activation freshening, permission validity or effect hygiene.

## Actual constructions applying the universal result

- `pending_capture` starts from the typed `interactionProgram` with empty arena.
  A handler first selects an operation arm whose actual attempt issues a nested
  request. Three real internal steps (`handleRequest`, `operationCons`,
  `operationRequest`) expose the root; only then does publication occur.
  `pending_resume_remaining` responds, restores the wait, observes No, executes
  the remaining matching arm and observes Yes. `pending_complete_safe` applies
  the universal theorem to this composed trace.
- `pending_two_distinct_responses` first completes the true response branch,
  then resumes the same saved entry with false. The entry remains exactly equal.
  `repeat_handle` handles any finite list of independently typed responses;
  `handles_in_any_order` and `capture_then_old_response` quantify independently
  over handles. `old_after_new_capture` starts empty and actually publishes both
  requests before selecting handle zero while handle one is waiting.
- `forwarded_capture` uses actual handler exhaustion before publication. Its
  saved continuation is restored HK of result bool. The accepted
  `distinct_continuation_types` keeps original K's result unit separate.
  `selected_original_execution_safe` embeds accepted `selected_execution`,
  whose arm actually invokes original K, into an empty-arena trace and applies
  the new invariant. No selected-arm handler restoration is inserted.
- `callback_capture_response` publishes a callable-response request, accepts the
  actual typed `nestedLambda`, and reaches an actual dynamicCall. Its lambda
  body and result consumer both contain handler syntax. `callback_actual_entry`
  exposes the genuine LambdaEntryPlan with both full bodies; the consumer's
  binder remains in its proper outer context. Every subsequent actual internal
  prefix satisfies `callback_every_internal_prefix_safe`.
- `value_wait_capture` uses the distinct actual valueRequest propagation step.
  `value_wait_saved_response_safe` applies the captured-handle theorem to every
  independently typed response to that value wait's request.

These constructions are proof terms awaiting primary elaboration, not executed
tests or independent certification.

## Source/native audit and exact remaining premises

NO_SAFE_CODE_SLICE under this theory-only lease. Actual inspected owners in
`tools/inference-playground/src/runtime/machine.rs`:

| Owner | Actual evidence and missing correspondence | Exact falsifier / requested evidence |
| --- | --- | --- |
| `Machine::propagate_request`, lines 2081 onward | Inspects installed CatchReturn before committing selection; validates grant/declaration/payload; captures continuation before popping the shallow delimiter. Native generic callable responses are restricted by the primitive or exact operation-v1 branch. Paper raw boolean eligibility and arbitrary typed OperationInstance are not established by these checks. | Map accepted declaration/instance and eligibility producers to each admitted paper arm; a same-typed but distinct instance selected by the mapping, or a rejected permitted callable response, falsifies full correspondence. |
| `TemplateNode::ForwardHandler` in template entry, lines 1989 onward | Resolves control owner, checks active/current owner, allocates a fresh handler occurrence and restores CatchReturn. Paper forwarded HK stores a renamed handler; no theorem relates retained metadata to these live fresh identities or excludes native owner errors. | Supply owner/control-map and fresh-per-resume invariants for every actual saved suffix. A replay reusing an occurrence or resolving to the wrong owner falsifies it. |
| `Frame::CatchReturn`, lines 1097–1135 | Pops the shallow delimiter and evaluates a selected value arm. With no value arm native execution returns the received value. The accepted paper candidate's empty value trials fail. | HO-HANDLER-VALUE-EMPTY-1 remains OPEN: a direct mapping of no-value-arm catch predicts incompatible successors. No semantics change or unproved implicit identity arm is authorized. |

This packet does not touch source constraint generation, accumulation,
propagation, levels, extrusion, qualifying intrusion or generalization. Their
source-to-proof and inference A/B obligations stay with Luna's source/inference
intake. No source constructor or native consumer was changed, and tests of this
arena would not prove those owners emit these transitions.

Mutual TODO HI-NATIVE-1: Luna/source intake owns the native correspondence just
listed. Inputs are the pinned machine/continuation/declaration paths and actual
source constructor evidence; proposed output is a scoped correspondence or
source-qualified counterexample, never production change inferred from this
candidate. The minimal provisional implementation slice is NONE until that
mapping and the value-empty discrepancy are adjudicated.

Mutual TODO HI-GRAPH-1: Luna/later integration owns
HO-HANDLER-GRAPH-COMPOSITION-1. Inputs are separately reviewed graph and handler
languages; output needs an explicit combined grammar, substitution, observations
and raw interaction proof. Falsifier: a graph reference in handler attempt or
callback body whose actual elimination/typing case is absent. Old-core embedding
alone is insufficient. This packet requests no new dependency or lease.

Mutual TODO HI-METADATA-1: Luna/semantic proof intake owns the live permissions,
freshening, owner/scoping, full raw Resume and mu/recursive/full-paper omitted
forms. Retained IDs are not a supplier for independent F1/FK1 quantifiers.
The current finite syntax proof leaves these premises unchanged and visible.

## Reuse, hashes and checks

The accepted old arena pattern was authored by
`/root/higher_order_interaction_astra_r1` (with any later primary coauthorship
recorded by its accepted receipt). This candidate reuses its append lookup,
trace induction, protocol association and scheduler pattern. It rejects transfer
of the old EvalContext/suspended-request extraction to Handler: that syntax
cannot account for handler interception. Accepted Handler syntax/safety were
authored by `/root/higher_order_handler_astra_r1` (accepted integration authors
remain recorded in the prior outcome). Their actual preservation, progress,
substitution, selected execution and forwarded-continuation suppliers are used
only in their finite Handler premises. No historical failure or excluded module
is imported as a proof, and no missing full-paper premise is renamed as closure.

Direct imported source: HigherOrderHandlerSafety SHA-256
`f74c35666d8f4f5ab1af52009c005d5cb0be9958f7f8d64185c31750b2dd38ef`;
its HandlerSyntax dependency
`4578e2d3c8b06a57937dd652e06eabb8c9271113a7eb3388dc718856d64b249d`.
Structural guide HigherOrderInteraction:
`45f2b8c74e2837e503db84aed3c9f55767a32d19e4008546e25a01cef1202875`.
Source machine:
`b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`.
Original paper:
`a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
All 109 frozen contract dependency hashes matched by read-only hashing.

Frozen Lean SHA-256:
`2d565176f1ab20bd6c3e685df6d505cb34d42b971450c373a5e563cf1fbd518a`.
Lean/build/tests/checkers/axiom queries: NOT_RUN by author. Primary owns bounded
serialized elaboration, every public declaration's signature/transitive axiom
query, repairs and fresh independent nonauthor review. All present proofs are
candidates until that process completes; this author cannot certify them.

Only this note, the one Lean module and the exact assignment inbox are written.
No scratch files, generated objects, background processes, descendants, Git,
external contacts, compiler changes or configuration changes. The inbox records
final STOP/time/hash. Next in-scope action is primary verification and review of
these frozen bytes; the author has no continuing background assignment.

## Primary coauthorship and verification freeze

Primary acknowledged the author's final STOP and source/note takeover at
07:31:45.053702 UTC. Primary coauthorship: the reserved local identifier prefix
in trace_publication_split became priorActions; concrete response examples now
supply explicit Saved witnesses and protocol tuples, and the value-wait response
application specifies handle zero. Raw rules, scheduler, protocol and quantified
theorem statements are unchanged. No typing or preservation premise was added.

The original author inbox and its original candidate hashes remain byte-frozen.
The three modules have passed serialized Lean elaboration; the combined query
covers223 explicit named module declarations plus8 named query constructions,
and8 additional anonymous applications. All231 emitted transitive axiom closures
are contained in {propext,Quot.sound}. Earlier failed attempts remain recorded.
The additional graph examples execute both projections through the same actual
view/reference chain, retain distinct union results, execute a guarded delayed
self-loop, and type an actual wrapper step with distinct inner/outer callable
types. Handler examples complete both response values, reject direct publication
under a handler and reject an uninhabited bottom response.

Final source/note-bound rebuild and fresh nonauthor review remain required before
acceptance; exact receipts/adjudication are owned by the sprint outcome. Primary
is a coauthor and is not an independent certifier. Current module SHA-256:

- `HigherOrderHandlerInteraction.lean`: `a0920fc7214055fd213bc66729e865b571698f95bd42ae289c432b6cf5730d3f`
