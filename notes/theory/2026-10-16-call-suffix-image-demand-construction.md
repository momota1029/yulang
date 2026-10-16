# Original Call phases, raw suffixes and Catch image demands

Date: 2026-10-16
Status: Draft constructive native algorithm definition; unapproved architecture;
independent mathematical and source review CLEAN for bounded claims
Claim class: bounded constructive source-to-proposed-record derivation; no
claim that current code emits these records or that generic feasibility is closed
Baseline: `7d5f5a7545bb84f3fb2679a6fa25aef6a66ca1a4`
Native source baseline: unchanged from `2140859b13b4450303dc4873a8cdb299e59169eb`
Exclusive lease: this file only; static prover leaf, no further delegation
Production, negative preflight and H3/P: unchanged and disabled where applicable

## 1. Frozen statement, independent inputs and exclusions

Construct the missing **joint** source/native record map for the selected
late-provider spine, rather than assume a supplied complete invocation graph
or a map from a Function4 effect summary to its pending continuation:

```text
act E: ping : Unit -> Int
p_once(u:Unit)  = E::ping(Unit)
p_twice(u:Unit) = Bind(_, E::ping(Unit), E::ping(Unit))
relay(cb : Unit -> [E] Int) =
  Catch cb(Unit) { E::ping(), k -> k(0); Return(v) -> v }
answer = relay(Name p)
```

These are source constructor abbreviations, not an executed/parsed fixture.
The Bind in `p_twice` is the original sequential computation Bind; no claim
that every arbitrary local declaration has that source role is introduced.
An additional variant uses `Bind(_, k(0), E::ping(Unit))` as the operation
arm. Keep its operation occurrence separate from both provider occurrences.

Fix the original declarations, source nodes, lexical scopes, registered
formals, original shared roots and all original response/current-state/future
binders. Quantify over one joint assignment `xi=(nu,K,D)`, the actual source
call/use instantiation, original lawful correlated substitutions, and every
actual selected request phase in that same invocation. Do not allocate a new
source binder to make a native projection fit. Native graph copies may allocate
their ordinary mapped row/record identities, with explicit original references.

Independent inputs are the independently valid primitive **whole** interfaces
and their local typing laws; the original actual environment and published p
value; original source roles/typed paths/receipts/profiles; actual world and
current configuration; operation instance/payload/response constraints; and
the original visibility/matching/selected-arm `OpCompat` premises. A valid
published value does not certify unrelated initialization timing. These inputs
are not a complete typed certificate for the desired Call, its source-to-native
joint map, or the requested raw remaining family; those are constructed below.
Guard origins are constructed, while their truth remains the original typing
or execution predicate, never inferred from an origin label.

The bounded conclusion is: the proposed emitters construct before provider
arrival a source-indexed invocation hole and an arm's dependent raw family;
the authentic later provider lower constructs a map to **that same** restored
Call/Catch instance; and each original Request clause constructs its exact
remaining source family. For the structural source request of once, the raw
remaining computation returns the response with no second E; for twice it
contains the second original E outside the selected shallow handler. The
outside-arm E retains its separate original route. Every other original
interface alternative, open carrier and dependent phase/future family remains
in the complete record, without a claim that the structural case exhausts it.

The general all-source operation/discharge, arbitrary alias/copy/equality,
later-lower closure, termination, required principality, full profiles/worlds,
native MODEL, soundness and production parents remain OPEN. No source domain
is narrowed and no old proof edge is retired.

## 2. Authority and the exact current obstruction

Governing semantics:

- [Annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
  §§1,1.1,1.2,3: negative concrete permission, open inflow, actual handling and
  independent survivors; permission is not a cap or a contribution.
- [Source Call formation](../design/2026-10-08-call-source-interface-definition.md)
  §§2–3: IF-Insert/IF-Use and complete declaration/phase/alternative retention.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3–4: source Return/Bind/Call, Strict entry, explicit declared operation
  result consumer and original future/raw-resumption transport.
- [Ordinary computation](../design/2026-10-02-ordinary-computation-semantics-package.md)
  §§2–5 and [source owner](../design/2026-10-02-typed-source-owner-realization.md)
  §§2,6: original state-threaded Request Bind, owner spans, outside matching,
  shallow selection and raw continuation without the selected handler.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md)
  §2: original binder partition, whole residual and lawful joint instances.
- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–5 and selected [attachment](../design/2026-10-10-contextual-attachment-admission-design.md)
  §3.1 / [residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md)
  govern native operation, instance identity and residual retention.

The preceding [architecture Draft](2026-10-16-open-negative-formal-catch-image-design.md)
is unapproved. Its clean reviews cover Draft/bounded claims only. This note
continues its first missing source consumer and does not treat it as selected
native semantics. The frozen [later-lower audit](2026-10-16-catch-image-later-lower-feasibility.md),
SHA-256 `d21d4e96a875a49e9b9c93ef0a7a4b59e633ac7ed4347335f7b85098ac8c8534`,
authenticates the outer Argument -> cb demand -> ResultEffect dependency and
the need for general effect-lower wakeups.
That is its frozen producer/review-provenance hash. The primary later changed
review metadata only: current Draft hash is
`639b0282ef08d8e3657dde8ee5654333480f5ce194981dbdfa55c546e25334ff`
and current audit hash is
`63ace8b183386737f4b328a2840a4e1585dc6ede22d9df7ec88a37ea92070e67`.
These current frozen files are the dependency pins below; no live review
output or other unfinished research artifact is consumed.

At the baseline `candidate_catch_operation` (`candidate_effect.rs:826–890`)
allocates a raw continuation return row and emits:

```text
slot64: raw_entry_effect <: raw_return_effect
slot65: WHOLE_scrutinee_effect <: raw_return_effect.
```

Catch's arm effect is then forwarded to its result at
`candidate_source.rs:870–889`. Thus even after replacing Catch's whole
scrutinee forwarding at slot51, slot65 -> k's invocation effect -> arm effect
reintroduces E from a request already handled. The existing comment explicitly
calls slot65 a provisional conservative full-S bound. It is not an exact raw
suffix constructor. No modification to code or either edge is authorized here.

## 3. Emit source clause graphs at their actual constructors

### 3.1 Record vocabulary and original scopes

Use the one proposed relation authority from the Draft. A `QRef` below is a
retained original source clause graph, **not** a new whole-Call correctness
predicate or a reconstruction from a solved scalar type. Its source clause
roots are emitted from the original source constructor and its declared
primitive interfaces using IF-Insert/IF-Use:

```text
QRoot {
  original_owner, source_occurrence, original_rule_phase,
  original_scope_telescope,
  clauses: original_declared_clause_addresses_and_contextual_refs
}
Clause = Ret(original_value_packet)
       | Bind(first_Q, original_value_and_state_binders, suffix_Q)
       | Read(original_binding_or_registration, original_use)
       | Invoke(CallUseId, provider_family_ref, whole_argument_ref)
       | Strict(original_formal, whole_argument_ref, body_Q)
       | NativeReturn(original_operation, request_thunk_ref)
       | ExecuteDeclaredResult(original_declaration, returned_carrier_ref)
       | Req(RequestPhaseId)
       | Handle(CatchUseId)
       | OriginalAlternative(original_IF_clause_ref)
       | ProviderHole(original_provider_binder, whole_original_interface_ref)
```

Each constructor preserves its full typed tuple, original `K,D`, providers,
worlds, licenses, scope/guard dependencies and future interfaces. The shortened
tags do not replace those operands. `OriginalAlternative` references **each**
original alternative at its actual IF slot, including non-source-executing or
hole-dependent alternatives. It does not map them to the source branch's
result/future interface. A missing original interface is Pending at that
original owner, not an empty clause set. The same original witness governs the
whole clause; no marginal selection of callee/effect/result witnesses occurs.

Proposed identity records are:

```text
ProducerIntro {
  original_Lambda_or_Operation, original_scope_telescope,
  original_formal_registration_or_declaration,
  source_value_descriptor, complete_Q_root,
  entry_role, body_or_native_return_Q, designated_consumer_ref,
  native_positive_Function?, original_introduction_relation?, admission?
}
CallUse {
  original_ApplySourceInput, original_source_Call_frame_and_IF_refs,
  callee_Read_or_value_Q, whole_argument_Delay_Q,
  provider_binder, invocation_Q, lexical_Catch_or_continuation_parents,
  native_demand?, original_checking_relation?, instance_map
}
CatchUse {
  original_Catch, original_scrutinee_Q, ordered_original_arms,
  actual_handler_and_receiver_binders, original_scope_telescope,
  image_lineage, residual_row, arm_RawFamily_refs
}
```

Native fields ending `?` are filled when the corresponding term/admission is
**generated**, without solving the constraint. Q roots and their source
references already exist. Recursive roots are registered before their edges;
an unresolved provider has a nonempty symbolic hole reference rather than an
assumed body. Source binders remain at their original scopes in both states.

### 3.2 Actual emitter assignments

| Actual owner | Proposed source-directed emission |
| --- | --- |
| `candidate_source.rs:600–655` | Register the same Lambda/formal/Name binding and a provider binder beta_cb; retain the annotation's original open negative port/permission occurrence separately. |
| Lambda visitor `:715–758`, `admit_lambda_fact` at `lib.rs:11317–11505` | Allocate ProducerIntro and its Strict/body Q references from the original Lambda recipe. At actual positive Function construction and slot2, attach that exact intro to the original relation/admission. |
| Operation visitor `candidate_source.rs:925–941`; `candidate_operation` at `candidate_effect.rs:805–824` | Retain the resolved declaration's entry, NativeReturn(MakeRequestThunk) and explicitly designated result consumer. Attach the intro to its actual slot42 positive value admission. Merely reading the operation emits no Request. |
| Value Name `candidate_source.rs:942–977` | Emit Read/Ret of the original binding view, retaining its registration or DefinitionUse/LocalUse. Native evaluation effect stays pure; no initializer or latent code is substituted. |
| Apply `candidate_source.rs:1008–1052`; `shadow_apply.rs:1518–1630` | Emit CallUse with callee Q and Delay of the **whole original argument**. Later attach the actual demand, invocation row, checking/cause and original native tuple before admission. |
| Block/Bind visitor `candidate_source.rs:758–768` and original local binding recipes | Emit the original source Bind edge and suffix binder/reference, preserving sequential source role. Native initializer installation is not by itself proof of that source role. |
| Catch visitor `candidate_source.rs:697–700,769–810,870–889` | Emit CatchUse and each arm's original dependent RawFamily reference, before its provider is known; source arms retain their payload/continuation binders and ordered subgraphs. |
| `candidate_catch_operation` | Retain Int response pairs and original scrutinee result Value pairs. Emit RawProducer and SuffixEffectDemand below instead of treating full scrutinee Effect as the raw suffix. |

The Lambda's complete source root includes Strict(entry) and its body, not
just the body effect row. If the actual argument is an arbitrary effectful
carrier, Strict's Request cases retain the unfinished rebind/body suffix.
For the actual source section `Delay(Return Unit)`, pure Unit formation and
entry Bind yield Unit before body execution. This computation does not
constrain every other admitted carrier to be pure or returning.

The formal's positive annotated Function is a checking/exposed **contract**,
not a real source producer introduction. Label it
`ContractExposure(registration,beta_cb,annotation)`; its ordinary native lower
does not allocate a fake provider or supply p's body. Before p arrives,
`Invoke(c_b,beta_cb,Delay(Unit))` remains a family of original provider
interfaces under beta_cb. This avoids deriving a complete invocation from the
annotation's E or from the successful paired Function constructor.
The provider hole's interface reference is the original Parameter/source
description family with its generated constraints, possibly still an unsolved
description variable. It is introduced by that source constructor here;
formation does not assume a complete already-valid interface for cb's future
actual provider. An independently supplied opaque primitive interface and an
unknown source provider description remain distinct cases.

## 4. Construct the actual late-provider joint map

The map is emitted in the original source flow, then carried by native bound
origins. It is not supplied as an attachment-map premise or inferred from
nominal equality.

### 4.1 Introduction and forward association rules

Add a proposed per-admission `SourceValueRef`, whose only constructors are:

```text
IntroValue(original_ProducerIntro, its_original_positive_Function_admission)
ReadValue(original_binding_use, donor_SourceValueRef, coherent_use_map)
RebindValue(original_Strict_entry, actual_argument_result, formal_binder)
AliasValue(original_local_binding_or_result_edge, donor_ref, typed_forward_map)
TransportValue(actual_FreshUse_or_extrusion, donor_ref, coherent_map)
```

Each rule validates the actual source action and endpoints at its emitter.
Type-only constraints carry their original unresolved provider/interface
variable; they do not gain IntroValue by endpoint equality. Distinct incoming
origins remain separate under the ordinary source guard/telescope even when
their native positive Functions share a representative. The existing
`candidate_context::Origin`, BoundAdmission/BoundEmission and dependency edges
are the attachment points, not a claim that these fields already exist.

For `answer = relay(Name p)`, generate these records in source order:

1. Original Lambda p supplies `IntroValue(i_p,rho_p)` at its slot2 Function
   introduction. Its original published value retains that source descriptor.
2. Name p supplies `ReadValue(use_p,i_p,mu_p)` at the actual definition/local
   use, using the existing graph's coherent FreshUse or shared-anchor map.
   Its argument computation is `Delay(Ret(that same p value/view))`.
3. Name relay supplies its original complete Lambda descriptor, instantiated
   by `mu_r`. The already emitted cb CallUse and CatchUse are part of that
   same retained source graph. They map to `c_b^mu_r` and `H^mu_r` together.
4. The original outer Call's Strict entry forces that exact Delay. Pure Read
   returns the same p value; `RebindValue(entry_out,ReadValue(use_p),cb)`
   relates beta_cb in **this** relay invocation to that same provider packet.
   This is the source entry/rebind rule; it does not require predicting p's
   eventual requests or satisfying the whole Call at generation.

The constructor retains both the original open carrier frame and this actual
source section. All other original carrier and Call alternatives remain in
their own complete IF slots. The following joint record is generated from
this actual outer Call, not from any independently chosen lower witness:

```text
ArgumentBinding {
  outer_CallUse, original_actual_argument_Q_and_ReadValue,
  original_entry_receipt_and_rebind_ref,
  receiving_formal_registration_in_mu_r,
  donor_ProducerIntro_in_mu_p,
  original_outer_comparison, Argument_FunctionPort_relation,
  common_source_input_world_and_telescope, coherent_map_composition
}
```

### 4.2 Native admission/replay consumer

The actual outer Function comparison produces its contravariant Argument
child (`lib.rs:12644–12650`): actual p value below relay's cb domain. Attach
the ArgumentBinding above to **that** child while the original comparison and
source CallUse are available. No generic subtyping rule asserts every native
Argument child is such a binding.

`candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:442–489`)
retains the actual lower admission and this source association. The restored
cb upper demand was emitted by `c_b^mu_r`; its admission retains that CallUse.
When ordinary opposite-bound Replay meets these original two parents, append

```text
InvocationCase {
  call = c_b^mu_r, catch_parent = H^mu_r,
  actual_intro = i_p^mu_p,
  actual_ArgumentBinding,
  original_lower_BoundKey_and_admission,
  original_upper_BoundKey_and_admission,
  ordered_Replay_parent, actual_FunctionPort_parent_and_fields,
  same_xi_source_telescope, mu_p_and_mu_r_with_outer_entry_identifications,
  result = substitute(i_p.complete_Q_root, that_call's_whole_argument)
}
```

The existing ResultEffect child (`lib.rs:12659–12664`) keeps this same
InvocationCase and its Result/provider fields. The consumer does not build
it anew from an E operand. Its Q substitution replaces p's whole argument
binder with this CallUse's Delay(Unit), identifies the original entry/result
views by the original typed maps, and retains all other parameters at their
original scopes. The same map is applied to every packet/interface/future
operand and original IF clause. It is not two successful scalar comparisons
composed into a fictitious provider witness.

**Constructive joint-map derivation for this spine.** ProducerIntro is formed
from p's original Lambda/declaration fields. ReadValue is formed from the
original Name resolution and its actual use map. RebindValue is formed by the
source Strict constructor of the outer Call using that exact argument Read.
The receiving cb registration and `c_b,H` refs come from the same mu_r graph.
The Argument child is emitted by the original outer source comparison; its
stored donor/receiver fields are precisely those of RebindValue. Replay then
retains both original parents, so the InvocationCase fields above are all
given by one constructor chain. Induction over these four source edges proves
that its provider, Call and Catch IDs and substitutions are the same ones;
no desired joint map or completed native MODEL is assumed. This is a proof
of the **proposed source-directed rules**, not a claim that current native
origins retain this chain.

For a direct alias `let alias=cb; alias(Unit)`, AliasValue records that original
binding and the LocalUse/FreshUse map. It preserves the cb registration donor
and forwards into the alias CallUse; it does not use the currently absent
`formal_name` shortcut as proof. For a direct module/local p use, actual
capture/FreshUse/shared-anchor evidence is retained as above. Arbitrary
nonidentity adapters, inferred aliases and row quotients remain beyond this
bounded derivation; they keep their original pending source-map obligation.

## 5. Request construction supplies the exact remaining family

### 5.1 Before any provider lower arrives

At the Catch arm's source formation, introduce a **dependent family binder**
q for that arm's original selected Request, with its original phase-domain
and payload/response/current-world/future telescope. This is not a request
event, a fresh runtime boundary or a successful eligibility witness.

```text
RawFamily(H,arm) = family over original RequestPhase(q) of H.scrutinee_Q:
  [original_same_q_exposure_and_match_guard,
   original_response_and_current_state_and_future_binders]
  -> Remaining(q, response, Cnow, original_future_arguments).
```

This record points to `H.scrutinee_Q`, its unresolved Invoke hole, original
arm request binder and original continuation-binding source rule. It exists
before p arrives. It is not implemented by scanning a row's effects or
assuming an empty set of current Request phases. Original opaque provider
phase/continuation families remain referenced under their own guards.

### 5.2 Emitting Request and attaching pending source frames

The operation producer's declared entry forces the Unit argument, obtains its
original payload, returns `MakeRequestThunk(op,payload)` across the native
return delimiter, and its **declared source result consumer** creates the
Request clause. Thus that Request has the original source operation and
actual instance operands, a fresh event binder at the original introduction,
original `K,D`, and the original result consumer's response continuation.
The operation's native invocation has already returned; it is not restarted
or captured as an unfinished native call at this phase.

Use the ordinary Request/Bind equation as a construction rule:

```text
Emit(Return(v) >>= F) = F(v)
Emit(Request(q,k) >>= F) = Request(q, lambda r,Cnow. k(r,Cnow) >>= F)
```

The second rule appends a **reference to the original pending F**, with all
original prefix-bound variables; it does not evaluate F or solve a constraint.
This makes each source Bind/entry/body/return frame retainable before its
first child has an actual lower or request. At an unresolved Invoke, keep a
parametric frame family over that original provider's request phases.
Substituting a later InvocationCase exposes its Request clauses and appends
the already retained frames, under the same xi and source guard.

Proposed concrete record:

```text
RequestPhase {
  source_Q_root_and_clause_address, InvocationCase_or_original_hole_family,
  original_operation_instance_payload_and_event_binders, K, D,
  original_yielding_configuration_and_Observe_refs,
  native_return_and_designated_consumer_phase,
  original_response_family, original_raw_result_value_and_future_interface,
  remaining_frames: shared ordered SourceFrame refs,
  original_scope_telescope, original_route_parents
}
SourceFrame = BindSuffix(original_bind, original_binder, suffix_Q)
            | RebindAndBody(original_Strict_entry, body_Q)
            | ReturnFromInvocation(original_owner_span)
            | DesignatedResultConsumption(original_source_consumer)
            | OriginalPhaseSuffix(original_complete_IF_clause_ref)
```

`Remaining(q,r,Cnow,future)` is constructed by composing q's original response
continuation with those ordered frames by ordinary Bind. It retains current
state, exact owner-span borrow/fresh re-entry, and original future family.
It never contains the **selected Catch handler**. The Catch boundary cuts the
raw suffix at its original scrutinee result; it neither recaptures the whole
scrutinee prefix nor applies the value arm during raw resumption. Forwarding
has its separate original fresh-handler wrapper; selecting has none.

For an arbitrary carrier request during Strict entry, Remaining contains the
unfinished RebindAndBody frame and later code. For an original nonstructural
or hole-dependent phase, keep its original complete phase suffix reference
and every dependent interface/guard operand. Do not substitute a structural
`Return` for an opaque suffix. The construction is uniform in those references
and proves neither their independent primitive laws nor their native discharge.
More explicitly, the reference binds the **original clause witness** z and
its full Request observation `(q,C,k)` from that clause's declared observation
telescope, then denotes that very `k(response,Cnow)` with its original future
family. It is dependent Request elimination on the original interface, not
reconstruction of k from its result/effect marginals. If an imported contract
has no such complete Request/phase observation, leave the missing interface
field Pending at that original declaration owner. A bare Function4/nominal-row
signature cannot supply it. This does not remove the imported clause or turn
it into the structural source branch.

### 5.3 The selected once/twice source phases

Write R(r) for source Return of the **same** typed response packet, retaining
its original future/interface constraints. Write `Omega_p` for the original
provider invocation return frame and the remaining cb Call-to-scrutinee
continuation. These frames are emitted before the body Request; they contain
no second E introduction or selected Catch wrapper. Owner re-entry keeps
their original evidence and actual resumed state. No cb wrapper invocation is
added: the cb Call invokes p's actual producer invocation.

For the actual source argument Delay(Unit), pure Unit/Read and Strict entry
reduce by source Return-Bind. The complete **structural source clauses** are

```text
Q_once  = Request(q1, lambda r,C. R(r,C) >>= Omega_p)
Q_twice = Request(q2, lambda r,C.
              Bind(_, R(r,C), CompleteCall(original_second_E_Apply))
                >>= Omega_p).
```

These equations are derived from emitter rules: the first operation's
declared consumer produces its Request; once appends only Omega_p; twice's
original body Bind appends the second original Apply before Omega_p.
The RequestPhase constructor therefore gives

```text
Remaining(q1,r,C,future) = R(r,C) >>= Omega_p
Remaining(q2,r,C,future) = CompleteCall(original_second_E_Apply,C)
                           >>= Omega_p.
```

This establishes the different suffixes from original source constructors,
without assuming an already supplied complete interface. The second E's
distinct original Apply/declaration-result-consumer introduction supplies q3;
it is not q2 found again in an E set. Its complete carrier/entry/result/future
interfaces and other original clauses remain at that source Apply.

The record also retains every original independent alternative of Q_once,
Q_twice, their Calls and primitives by its own IF address. The displayed
structural equalities do not delete those alternatives or establish that
their entire declared effect types are empty. In particular “the source
remaining branch has no second Request” is distinct from “all possible
complete-interface phase families have an empty effect interpretation.”

## 6. Bind raw k and replace the full-S demand at its owner

At the original continuation-binding source rule of H's operation arm, emit

```text
RawProducer {
  original_CatchUse_and_arm, original_k_binder,
  original_selected_Request_binder_and_RawFamily(H,arm),
  response_interface = original_operation_Int_interface,
  result_interface = original_scrutinee_result_interface,
  original_scope_telescope_and_current_state_family,
  entry = StrictResponse,
  body = Remaining(original_same_q, response, Cnow, original_future)
}
```

This is the source semantics of the same raw continuation already supplied
by selection. It is not an invented Lambda with guessed effects. Its raw
result remains the scrutinee result rather than the handler arm's result;
its response remains the actual operation's Int rather than an unrelated
new value variable. All rigid/type-family evidence stays at that q's scope.

The proposed native continuation construction retains existing response/value
pairs and allocates ordinary open `entry`, `tail` and `returned` effect rows:

```text
slot64: entry+ <: returned-
new SuffixEffectDemand(RawFamily(H,arm), tail)
replacement slot65: tail+ <: returned-
K+ = PositiveFunction(Int-, entry-, returned+, original_scrutinee_Value+)
K- = NegativeFunction(Int+, entry+, returned-, original_scrutinee_Value-).
```

Allocate these rows at the original Catch-arm constructor's level. Ordinary
extrusion and coherent use maps subsequently determine their actual copies;
the raw-family projection does not install a non-generic exception or level-0
anchor. The new tail has an actual residual computation owner, rather than
being an invented extra tail of the negative formal's annotation.

No whole-scrutinee Effect operand occurs in replacement slot65. The new tail
is owned by this raw-family projection/lineage; it is not an annotation tail,
an empty result, or a second independent q witness. One static row can retain
the whole dependent raw-family constraint at this source arm. It is not one
new row per dynamic event. The source relation retains the dependence on q
and checks its required uniform finite-interface projection; no claim of that
general projection's principality is made here.

For raw k's actual Apply, retain its original CallUse and RawProducer at the
CatchBinder Name. Its invocation graph is

```text
RawInvoke(q, kappa_response, C) =
  Force(kappa_response,C) >>= lambda r,Cnow.
     Remaining(q,r,Cnow,original_future).
```

Thus slot64 preserves actual response-entry effects. With the original
literal response 0, the source argument is Delay(Return Int0), so entry
contributes no request and does not restart cb's entry or p's prefix. With
an effectful response computation the unfinished response entry remains a
genuine part of RawInvoke, with its own source request phases.

An upper demand on returned (or tail) registers its original exact target,
not an invented remainder:

```text
SuffixImageDemand(lineage, original_q_family, original_upper_admission)
  requires the original Remaining/RawInvoke family at that same q
  to satisfy the original upper Value/effect/interface target.
```

Propagate it by the Ret/Request/Bind/Call source clauses above, with original
guards and all original alternative suffix refs. At once's source phase it
checks R(response) and the original return frames. At twice's source phase
it reaches the second original operation's request/response/future clauses.
It never checks the consumed first E as an outgoing raw request. It also
never emits `whole_scrutinee_effect <: upper` as “feedback.” Existing
CatchImage output demands compose the original arm Call with this family
before projecting to Catch's residual row.

## 7. Source-to-image derivation for the actual arm

Let g_q denote the original full selection predicate at q's yielding boundary:
actual source profile/receipt/Observe paths, current Active/Covers/visibility,
ordered match and the original response/arm compatibility. Emission retains
g_q and its source origins; it does not prove g_q from those origins. Fix a
valid original selected source branch satisfying it for the displayed arm.
The original outside-image rule binds **that same** q's Remaining as k and
runs `k(0)` outside H.

For once, the exact original source clause gives

```text
H[Q_once] --g_q1--> RawInvoke(q1, Delay(R(0)), C_outside_H)
                    = R(0) through the original Omega_p frames.
```

For twice, it gives

```text
H[Q_twice] --g_q2--> RawInvoke(q2, Delay(R(0)), C_outside_H)
                     = Request(q3, original_remaining_q3_family).
```

H is absent in the second equation. Any later search for q3 uses its own
actual current context, event and original observed views. An outer handler
may handle it through its own source derivation; the old h cannot remove it.
At the current image's outward boundary it is the second original request,
with no assertion about completed whole-program support under outer contexts.

For the outside-arm variant, source Bind appends the arm's **own** operation
Apply a to the RawInvoke result:

```text
once image  = Request(q_arm, original_remaining_arm_family)
twice image = Request(q3, lambda r,C.
                original_remaining_q3(r,C) >>= CompleteCall(a)).
```

The second equality records q_arm in a future suffix if that suffix is
resumed; it does not unconditionally execute it when q3's continuation is
discarded. q_arm's introduction and route are distinct even when its family
and operation declaration equal q1/q2/q3. It is outside the selected handler
and is not fed back into H's scrutinee subtraction.

If g_q is not established, keep the original guarded selection and forwarding
clauses. Source forwarding preserves q and its prescribed fresh-handler
resumption wrapper. Epistemic pending is not a source event changing state;
no scalar E is guessed forwarded, removed or empty. The structural selected
branch equations above leave all other original guard/alternative families
in the complete image, with their own original outputs and current state.

This constructs the selected source -> Q -> RequestPhase -> Remaining ->
SuffixImageDemand chain and its joint provider/Call/Catch map. It does not
assert a generic native evaluator for all those clauses or that the current
code implements any proposed record.

## 8. Later inputs, copies and the bounded proof boundary

Before restoring a source instance, allocate its mapped Q/Call/Catch/raw-family
shells and watchers; then connect their original dependencies through the
same FreshUse map; then restore its actual bound admissions. This avoids
missing the late p lower while a restored cb demand/image is already present.
General Value/effect admission hooks queue source association and image work;
FunctionPort insertion alone is insufficient, as the frozen audit shows.
A provider Value lower supplies the authentic InvocationCase and its retained
source phases. A later E effect lower wakes the dependent image/demand checks;
it does **not** reconstruct a Request or a missing provider phase from the E
atom. Without the corresponding original source interface/association, keep
that bridge pending at its owner. Actual operation Support stays its declared
type operand, distinct from a generated source Request event.

Use immutable BoundAdmission/BoundEmission references and the actual lower/
upper Replay parents. Work keys include the source Call instance, invocation
case, original admission and generation; endpoint equality cannot suppress
unprocessed source-origin/image obligations. A new provider alternative adds
its own guarded InvocationCase, not a replacement for the previous one.
Its original phase families and every current output upper are visited.

Capture may retain an unresolved Q/RawFamily/SuffixImageDemand with all free
source operands and pending dependencies; it need not solve every guard.
FreshUse maps source-owned Q/Call/Catch and permission/lineage records jointly
with the ordinary row/view maps. It preserves one map within a use and keeps
distinct local generic instances separate. A captured inherited receiver
boundary or currently bound q remains that same original reference; aliasing
raw k does not universally generalize q or allocate a fresh selected request.
The fixed support of q/current response/current world and original future
families is retained at the actual source binder/Generalize owner. No raw
family is inferred merely because some native term has Function4 shape.

All unconditional output facts require a stable original guard/constructor
derivation. Guarded pending clauses stay retained. A new dependency invalidates
generation-dependent solved conclusions before reuse; it does not retract a
wrong scalar E bound already inserted into an ordinary append-only row.
Publication must retain the whole constrained relation with a proved lawful
scheme interpretation, or suspend queries that require its solved image.
Empty current lower sets cannot justify a closed empty raw suffix. Existing
source/drain terminal receipts certify only their existing operations, so new
image work requires its own owned continuation/acknowledgement coverage.

For this finite nonrecursive selected source graph the template construction
uses O(n + original interface-reference payload) records. Request suffixes
are shared frame references, not duplicated prefixes. Each admitted authentic
provider/source-demand pair adds one InvocationCase and its actual clause
edges; finite once/twice normalization visits the two operation sites and
their Bind/return frames. Original unbounded future families remain references;
this is not a finite enumeration or a bound on evaluating their predicates.
Generic recursive maps may create unbounded distinct demands/contexts. Their
exact closure, termination, lawful quotient/equality and required-principality
proof remains OPEN, without a new source cap or implementation-ready claim.

**Precisely discharged in the proposed bounded construction:** original
producer roots are emitted rather than assumed; the late lower's source
ownership is joined to the original cb Call/Catch instance at original source
entry/Argument/Replay owners; Request/Bind emits the exact structural remaining
suffix; raw k uses that suffix rather than full S; and once/twice/outside-arm
structural source clauses follow from the original shallow rules.

**Not discharged:** truth of original typed guards or independent primitives;
full arbitrary source-role/coherence/profile/world formation; all alternative
native interpretations; implementation correspondence; generic image-demand
normalization; arbitrary aliases, FreshUse/extrusion/qualifying intrusion;
general later-lower lifecycle/termination; global soundness and required
principality. The original central native parent remains owned and OPEN.
This note is a reviewable bounded construction, not adoption or proof of
generic feasibility. Removing slots51/65 or enabling negative preflight must
await proof-supported reviewed/adopted implementation authority.

## 9. Verification, pins and commit packet

Static leaf packet with a 25-minute cap. Only this note is written. No compiler
code, tests, expectations, shared records, manifests, questions or configuration
changed; no Git mutations, executable probes, tests, builds, network, benchmarks
or children. CPU/RSS unmeasured. Requested configured Sol/high; observed runtime
model/effort unknown. This author supplies no independent certification.

Pins, baseline equality, local links, fences, whitespace and the frozen artifact
hash are recorded on handoff. Both predecessor artifacts are frozen producer
inputs; their clean bounded review does not adopt their architecture or close
the central theorem. Changed predecessor metadata hashes are recorded above;
the following tracked dependencies match the packet baseline. Native files
also retain the original 2140859b1 byte hashes.

```text
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917  notes/design/2026-10-02-ordinary-computation-semantics-package.md
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa  notes/design/2026-10-02-typed-source-owner-realization.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9  crates/yu-solver/src/candidate_effect.rs
cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1  crates/yu-solver/src/candidate_call.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e  crates/yu-solver/src/candidate_scheme.rs
357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba  crates/yu-solver/src/shadow_apply.rs
2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f  crates/yu-solver/src/lib.rs
```

Commit packet:

- Exact lease: `notes/theory/2026-10-16-call-suffix-image-demand-construction.md`.
- Baseline: `7d5f5a7545bb84f3fb2679a6fa25aef6a66ca1a4`; native dependencies
  unchanged from `2140859b13b4450303dc4873a8cdb299e59169eb` when checked.
- Status: Draft/unapproved constructive algorithm and selected-spine derivation;
  independent mathematical/source reviews CLEAN; generic parent remains OPEN.
- Checks: static source owner/constructor tracing and handoff integrity/pins;
  zero builds/tests/probes/measurements. Artifact frozen before review.
- Suggested checkpoint: `research: construct original Call suffix and raw image demand`.
- Shared deltas for primary/curator: retain this bounded construction's precise
  status, identify slot65's required remaining-family replacement, and keep
  generic image/native/soundness/principality/adoption/cutover gates OPEN. No
  old proof edge is automatically retired or marked proved.
- Reviews: mathematical `checked_result_semantics` and source/authority
  `capture_source_review` independently returned CLEAN at frozen producer
  SHA-256 `fd72e7c2e6024da19d03e73d8c3a9e65f894a3f769f5d6e9856b020e3fbe4239`.
  The primary accepts the bounded source-directed construction and selected
  structural suffix equations. Neither review certifies a generic native
  discharge procedure, implementation correspondence or adoption readiness.
- Next owner: the original generic image-demand consumer and its guarded
  normalization/copy/lifecycle obligations. The source association and suffix
  construction above must be consumed, rather than assumed again in another
  equivalent diagonal proof. Generic feasibility and architecture adoption
  remain OPEN.
