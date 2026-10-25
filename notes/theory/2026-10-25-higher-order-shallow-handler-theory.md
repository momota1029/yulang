# Higher-order shallow handlers: actual code and value safety candidate

Status: candidate mathematics, UNCHECKED and UNREVIEWED at author freeze.
Contract: HANDLER-RECURSIVE-RHS-THEORY-20261025/r1, outcome A.
Author: `/root/higher_order_handler_astra_r1`; requested Astra/medium;
observed model and effort UNKNOWN. No coauthors or descendants at this freeze.
No production, source correspondence, permission, inference or full-paper closure.

The parent is HO-SHALLOW-HANDLER-1, paper lines 399–456 and the local
handler/resume preservation lemma at 1069–1088. The execution theorem at
1139–1159 retains its original full syntax, graph, external-response, metadata
and arbitrary finite-prefix quantifiers. This packet supplies a candidate for
the entire accepted HigherOrder value/computation/adapter grammar, recursively
extended with handlers, ordered trials and waits. Omitted paper forms remain
outside this representation and OPEN at the parent, without changing its scope.

## Construction and application

`HigherOrderHandlerSyntax.lean` defines mutually recursive Value, Comp, Adapter,
Handler, ValueArms and OperationArms, then separate extrinsic typing judgments.
Every accepted HigherOrder constructor is copied structurally, with the same
literal payloads, modes, type annotations, operation instances, receipt data,
views and adapter path correspondence metadata. The full embedding recurses
under lambda bodies, result consumers, adapter inputs, request continuations,
binds and case branches. `embedValue_typed`, `embedComp_typed` and
`embedAdapter_typed` preserve every old typing derivation in its original context.
This is a typing embedding, not a claimed operational equivalence with the old
core's suspended-context terminal classification.

Handlers, trials and waits can occur anywhere Comp can occur, including inside
lambda/delay/adapter code. Value-arm bodies bind the returned value at index 0.
Operation-arm bodies bind payload at index 0 and K at index 1. K is concretely
encoded as a value-entry lambda, with its response binder, original code body,
and an identity result adapter. Its type is Callable(Q,A); invocation uses the
accepted delayed argument carrier convention. No assumed callable function,
opaque code label, BodyLaws or safe-attempt oracle occurs in the construction.

The six-sort renaming and substitution functions traverse all these forms.
Operation arm bodies lift twice; request continuations lift once; lambda result
consumers remain outside the lambda parameter binder. Mutual typing-preservation
proofs for renaming/substitution are supplied. `substitute_pair` closes the
payload and K simultaneously, and `attemptOperation_typed` applies it to actual
arm code. This directly supplies the local attempt premise in the parent lemma.

`HigherOrderHandlerSafety.lean` gives independent raw Step rules. A rule never
contains typing, preservation or safety as a premise. Matching compares equality
of the full OperationInstance: operation identity, ordered type arguments,
payload type and response type. Structural DecidableEq instances are derived
locally for Ty and OperationInstance; no classical equality oracle is invoked.
All arms must type-check regardless of their raw Boolean eligibility flags.
The permission meaning of these flags is not asserted.

Selection substitutes the original K into actual attempt code and puts only a
wait frame around that code. The selected handler is absent during the attempt.
No advances to the remaining arms, and Yes returns the result. Value exhaustion
produces MatchFailure; operation exhaustion forwards the same instance and
payload with `forwardedContinuation h k = handle (renameHandler succ h) k`.
This separate construction has response-to-output typing; it is not the K sent
to an arm. Request propagation under bind shifts only the ambient variables of
the bind body, preserving its own result binder.

A request inside a wait is propagated with the wait in its response binder.
The original handler, payload and remaining arms are shifted once, while the
original K is shifted under its own response binder. The pending original
instance is unchanged. Thus responding to the nested request re-enters the
pending attempt, retaining the original request and plan. Effects are not
intercepted by the removed selected handler, and no transition rewinds prior
execution. `no_after_event` retains the prior event in the prefix before No.
This is a syntactic/event-order fact, not a world-state or effect-hygiene proof.

`preservation` covers every raw step, including all base and handler transitions.
`closed_progress` covers every closed typed extended computation and gives only
Ret, Request, Fail or an actual next step. A request/failure below an evaluation
frame must propagate; it is not classified as an arbitrary suspended term.
`prefix_preservation` and `finite_prefix_safety` apply these results to every
finite raw internal prefix. `resume_typed` and `many_responses_typed` retain each
independently typed response and do not consume or modify saved K. They do not
claim the accepted old interaction arena already represents the new grammar.

Concrete applications include:

- `selected_execution`: a complete raw trace from a unit-input/bool-output
  handler through an arm that actually calls the original unit-to-unit K.
- `forwarded_execution_safe` and `distinct_continuation_types`: forwarding
  produces a unit-to-bool continuation, distinguished from selected K.
- `ordered_value_trials_safe`: a No arm followed by a Yes arm in source order.
- `wrong_identity_skipped`, `wrong_arguments_skipped`, `ineligible_skipped`:
  exact-instance/Boolean selection cases with no weakened matching relation.
- `nested_request_restoration_typed` and
  `nested_response_restoration_typed`: actual request-through-wait followed by
  any independently typed nested response.
- `nestedLambda_typed` and `nested_lambda_call_safe`: extended forms inside
  both lambda and result-adapter binders, applied back to finite-prefix safety.

## Source/native boundary and precise remaining obligations

Read-only inspection of frozen `runtime/machine.rs` and `continuation.rs`
provides owner locators, not a source/native simulation theorem.

`Machine::propagate_request` (machine.rs:2081 onward) compares native declaration
identities, requires local grants outside its closed primitive case, checks a
restricted operation signature/payload domain, captures K before popping the
selected `Frame::CatchReturn`, and then evaluates selected arm code outside that
handler. This agrees with the selected-versus-forwarded distinction at a control
shape level, but does not construct this candidate's fully typed attempt plans.
The current routine does not supply general effectful No/Yes trial code and
pending-wait restoration. Its native payload/response restrictions are not used
to restrict the theorem's accepted HigherOrder domain.

`Frame::CatchReturn` (machine.rs:1098–1136) selects the first value pattern and
returns the received value when no value arm exists. The paper's empty value
trial instead yields MatchFailure. This observed difference blocks identifying
this candidate with that native path without an explicit semantic/source bridge;
it is not authority to change the runtime or revise the paper.

`SavedFrame::HandlerBoundary` (machine.rs:2306 onward),
`TemplateNode::ForwardHandler` (continuation.rs:34), and its replay case
(machine.rs:1989–2008) retain handler/environment/owner and allocate a fresh
handler occurrence on replay. The candidate retains handler identity and code
but does not model this activation/owner freshening or prove the native replay
correspondence. Preserving a numeric identity is not proof of freshening.

Luna/source intake owns the following remaining premises:

1. HO-HANDLER-SOURCE-1: source Catch arm elaboration must produce typed ordered
   attempt bodies, simultaneous payload/K binders and the same full operation
   instance. Falsifier: a reachable body using the wrong index/instance, an
   untyped disabled arm, or loss of an accepted higher-order constructor.
2. HO-HANDLER-NATIVE-WAIT-1: a future authorized native correspondence packet
   must map actual pending waits and request propagation to `Step.operationRequest`
   and `Step.valueRequest`. Falsifier: a nested response drops the remaining arms,
   original payload/K, or reinstalls the selected handler around attempt effects.
3. HO-HANDLER-VALUE-EMPTY-1: adjudicate the paper/native no-value-arm discrepancy
   at `Frame::CatchReturn`; no code change is authorized by this packet.
4. HO-METADATA-ADEQUACY-1: actual eligibility/permissions, owner/activation
   freshening, receipt/view behavior and rigid polymorphic elaboration remain
   separate semantic/source obligations. Every total Boolean choice is covered
   only as raw selection data in this value-typing projection.
5. Full-paper safety: graph extension, omitted tuple/record/variant/nominal/mu/
   evidence/type-abstraction/primitive/mapop/rec/template forms, and the combined
   new handler grammar with arbitrary saved external interactions remain OPEN.
   Existing F1/FK1 and Simple-sub A/B obligations are unaffected.

No production implementation TODO is authorized. The minimal next source packet
would be a read-only source-to-raw binder/instance/wait mapping using these owners
and falsifiers; any prototype must first receive a new explicit Luna lease.

## Reuse, checking and resources

Accepted HigherOrderSyntax supplies Ty and all metadata. The accepted
HigherOrderSubstitution, Entry and Safety proofs supply the structural method
and base cases, which are reproved over the extended syntax rather than applied
outside their old domain. HigherOrderInteraction is read for its independent
response/immutable-saved-code boundary; its theorem is not claimed for handlers.
No historical failure, literal-only theorem or assumed transition is promoted
into a source theorem. No Simple-sub mechanism, compiler behavior or expectation
was changed.

Author checks: NOT_RUN (Lean, build, tests and checkers prohibited by the packet).
Textual reads and SHA-256 hashing only; primary owns serialized elaboration,
public-signature and strict transitive-axiom inspection, followed by fresh
nonauthor review. Required axiom closure is a subset of {propext, Quot.sound}.
This note is not certification of compilation or proof acceptance.

Only the two leased Lean files, this note and the one leased inbox are written.
No scratch files, background processes, child workers, Git operations, external
contacts or edits to accepted modules. The frozen inbox records the final hashes,
time and STOP receipt; there is no implied continuation while waiting for intake.

## Primary coauthorship and candidate freeze

Primary acknowledged the author's actual STOP and took over the two source files
and this note at 07:14:40.175763 UTC. Primary coauthorship repairs: six mutual
proof application layouts and an ordinary comment before mutual; reserved local
binder prefix renamed trace; explicit Nat.succ weakening in the two response
propagation cases; concrete eight-event witness for the selected-continuation
execution. These preserve raw grammar, transitions, types and theorem domains.
The author inbox remains byte-frozen at its original handoff hashes.

Primary has elaborated both modules and queried every named public declaration.
The combined query covers 273 module declarations plus eight primary query
constructions, with eight additional anonymous boundary examples. All successful
query results have transitive axiom closure contained in {propext, Quot.sound}.
The query exercises empty value-arm failure, concrete instance inequality, nested
response restoration, ordered trials, double binder lifting, transparent wrapper
cycle rejection, guarded constructors and alias-cycle rejection. Earlier failed
elaboration/query receipts remain preserved. Final source/note-bound rebuild and
fresh nonauthor review are required before acceptance; their exact receipts and
adjudication belong to the sprint outcome.

Current module SHA-256:

- `HigherOrderHandlerSyntax.lean`: `4578e2d3c8b06a57937dd652e06eabb8c9271113a7eb3388dc718856d64b249d`
- `HigherOrderHandlerSafety.lean`: `f74c35666d8f4f5ab1af52009c005d5cb0be9958f7f8d64185c31750b2dd38ef`

The two new grammar extensions separately embed the accepted higher-order core.
Their combined handler/graph language is not proved by either independent lane
(HO-HANDLER-GRAPH-COMPOSITION-1 remains OPEN). Original full-paper and native
correspondence parents remain OPEN.
