# Higher-order proof core: fresh independent review

Assignment-ID: HIGHER-ORDER-PROOF-CORE-REVIEW-20261025
Handoff revision: 1
Sprint: LEAN-HIGHER-ORDER-PROOF-CORE-20261025/r1
Contract SHA256: 56a820500ce7bc3f3d0996e106a9981e539f2e2e05554f15526903e146fcaeb6
Baseline: 77df594169ad07ff9cb523699485cd0e7146e86f
Reviewer: /root/higher_order_proof_core_review_astra_r1, fresh NONAUTHOR.
Authors reviewed: /root/higher_order_proof_core_astra_r1 and /root (repairs/source map).
Requested model/effort: gpt-6-astra / medium. Observed model/effort: UNKNOWN / UNKNOWN.
Parent launch receipt: acknowledged by 2026-10-25T06:22:39.123139+00:00;
conservative budget start 2026-10-25T06:22:35+00:00, deadline 06:27:35+00:00.
Sole write lease: this review inbox. No descendants, Git, config, central or reviewed-file writes.

## Verdict

CLEAN for the fixed research milestone. No blocking, major or minor findings.
The result is a structural, all-constructor, one-way typing-preserving embedding
of Original.Val/Comp and TypedCall.Value/Comp/Adapter/Function, with a genuine
callable-as-Value endpoint. It is not reflection, injectivity of evidence,
conservativity, operational adequacy, or source/native/full Call closure.
The design remains research authority only. Independent review does not make it
Authoritative production architecture.

## Stage 1: design, dependency and constructor audit

Read root operating instructions, governing sprint/authority rules, selected
contract, current state/README, original typing definitions and complete-Call
permission. The operational paper explicitly labels its construction/proposal;
it supplies no independent production authority.

Compared every Original type/value/computation constructor and every TypedCall
Value/Comp/Adapter/Function constructor against the recursive target maps.
All eight literal payload domains, variable indices, ordered children, thunk,
union/intersection/top/bottom, bind/union branch/request binders are retained.
Original wrappers expand structurally; no opaque old-code constructor remains.
Closed original terms embed into arbitrary target contexts using the proved
empty relation. General preservation retains every old lookup fact through
ContextEmbedding; extend_embedding preserves zero and successor indices.

Operation identity, ordered type arguments, payload/response types, scope owner,
expose views, failure reasons, path components/kinds/types, occurrence identity,
receipt profiles/designated slots, adapter paths/views and interface ports all
have matching structural fields/maps. PathRule is translated Prop-to-Prop:
its mappingIdentity is not recovered as computational data. This qualified claim
is explicit and correct. Adapter.typed occurs only in the old input proof and
is consumed to construct extrinsic target typing, with no typing-definition
cycle in the target syntax.

Value lambda binds A; computation lambda binds Thunk A. Both preserve receipt,
argument/body-result/result annotations and consumer. Wrap uses c->a on input
and b->d on output around a->b. DynamicCall takes a thunk carrier. No operational
rule is inferred from that newly defined research typing interface.

## Stage 2: proofs, endpoints and recorded verification

Read every new proof. Mutual preservation constructs each target derivation;
embedAdapter_typed uses the actual old typed body under an extended empty
embedding. embedFunction_typed consumes every old FunctionTyped derivation and
returns ValueTyped in every target context, with the mode and adapter equalities
applied in the correct directions.

function_as_argument and call_with_function_argument use actual delay/ret and
dynamicCall constructors. The query constructs a typed higher-order receiver;
its existence is not merely assumed by the example. request_callable_response
constructs a request continuation that binds and returns a callable. function_cell
uses the actual generic Store.push/current-cell theorem and embeds the function's
existing derivation. This is formal generic storage, not native closure readback.

read_embedding keeps the actual selected address and pointwise maps the current
store. read_embedding_typed uses successful_read_typed. captured_value_typed
uses realized_substitution_typed; captured_body_typed applies the actual close_body
construction before embedding. Inspected the supplier's realize/captured_index/
CellsTyped/substitution/close_body definitions: success and CellsTyped remain
explicit, and filler cannot replace a represented typed index. New callable
storage and transport of old represented captures are separate constructions;
no theorem quietly asserts that old captures already contain native callables.

Inspected runner, query and all eight recorded calls, without rerunning Lean.
Rows 3/4/8 are the final successful syntax/embedding/query checks. All their
input hashes equal before/after and current bytes; module output hashes also
match current objects. All 64 contract pins match; all 37 accepted prior module
chains have successful non-timeout rows, stable inputs and matching present
input/output hashes. The five prior receipt hashes match the contract.
Recorded aggregate Lean time is 3.733904196997173 seconds. Failures remain visible:
row 2 reserved prefix/layout parse failures, row 6 Arena.root argument name,
row 7 underdetermined example application; final row 8 resolves them.

The query contains 59 signature/axiom pairs (55 public declarations plus four
example proofs) and 33 examples. Printed axioms are empty or subsets of
{propext, Quot.sound}; no Classical.choice, sorryAx or extra axiom appears.
Examples exercise computation forcing, nonconflation of A/Thunk A, distinct
wrap adapters, metadata, callable response/cell, current lexical/global reads,
and an actually realized closed body. These checks supplement the universal
proof inspection; examples alone are not the constructor-coverage argument.

## Stage 3: actual source correspondence and residual owners

Inspected program.rs Lambda/Apply/Name and generated member receiver branches;
machine.rs Closure, Lambda, Apply/Callee, ValueEntry, RecordDefault,
bind_record_parameter, consume, execute_with_substitution, lookup/extend,
substitute_environment and dispatch_name; receiving schema constructors.
The source map correctly distinguishes caller-environment delayed argument from
the closure's saved environment, actual Value forcing from Computation binding,
unit patterns without an ordinary binder, sequential record/default binding,
callback validation and dispatch/name transport. Native primitive/continuation/
operation providers are not silently claimed covered by lambda/wrap syntax.

A source Apply callee is a computation; its future elaboration needs bind and
capture-avoiding index handling. Formal one-binder lambda does not encode all
native unit/record/default/root/callback fields. The source map identifies these
omissions instead of treating a structural embedding as a source elaboration
proof. No demonstrated runtime defect licenses a compiler change here.

Parent application: remove the missing callable Value representation obstacle
inside RESPONSE-ENCODING-1 / ENV-CALLABLE-1. Keep their native/full parent gates
OPEN. HO-SUBSTITUTION-1 remains with the higher-order proof lane; source body/
layout construction, native current ReceivedValue encoding, recursive graph
readback and callable body/consumer realization remain with source/native owners
under ENV-LAYOUT-1, ENV-CELL-VALUE-1, ENV-GRAPH-1 and ENV-CALLABLE-1. Dispatch,
receiving/template interpretation remain ENV-DISPATCH-1 / RESPONSE-TEMPLATE-1.
New-core progress/preservation, Force, whole traces, operation authenticity and
original inference A/B remain OPEN at their original owners.

## Frozen artifact hashes

- Design: 50eb7ebd2ed2d155dfeca2e3ce99f3f5b990cc4f1bf101663949a04d8d4b748f
- Source map: ecf40f37ccecede102c02e6ac4d40b0b937c05b46b33f0a93c5f0684ff3faabc
- HigherOrderSyntax.lean: ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972
- HigherOrderEmbedding.lean: 2b773edf831d04cd4319e1fb980865dff0fb9a38f7d64b21f3d228ea2a0e1457
- Initial author handoff: c1c1b5de2d0b906540a1ba50f7bf70673543b30379cd77b54861bf52f1cecfbb
- Verification JSONL: 7934c1b69d4fb469a73db499bef9f7696464ea7216eb12a8a99036688496eaef
- Query: f9286bae30e92edb70d1293ea29cf117ffa60a2ba3993a4eec4e02db0e28e8c1
- Runner: f218d36c9173537e2e44b60d96b46fafe8a78f31b4adabc4271fa55d18db6872

Initial author handoff remains historical candidate bytes, not a claim to the
repaired final hashes. All hashes above were independently read and matched.
Next step: primary adjudication and bounded integration. No reviewer TODO or
repair is required. No further reviewer stage is authorized by this receipt.

STOP receipt: 2026-10-25T06:23:59.109299+00:00; conservative elapsed 84.109 / 300 wall seconds.
Reviewer Lean/build/tests/native checks: NOT_RUN. Read/hash inspection only.
Writer STOPPED after this single inbox write. No live/background processes or
descendants, no unresolved descendant leases, no further writes.
