# Open negative formal ports and source-owned Catch images

Date: 2026-10-16
Status: independently reviewed Draft; unapproved native architecture
Claim class: proposed construction/consumer invariant, local constructive
derivations, and a source-rule discriminator; no central feasibility closure
Baseline: `2140859b13b4450303dc4873a8cdb299e59169eb`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; static prover leaf, no further delegation
Implementation authority: none; negative-formal admission and H3/P remain disabled
Independent mathematical checked_result_semantics and source/authority
capture_source_review are CLEAN for the Draft/bounded claims at producer
SHA-256 `cadffc962dca3c51023cb7a72235285a89095d9716c71c1227c8db0ed98f3bde`.
The complementary producer was reviewed at `d21d4e96...c8534`; its current
metadata digest is pinned below. Neither review establishes central native
feasibility or supports implementation/adoption yet.

## 1. Frozen obligation and authority boundary

This packet changes method from auditing the unchanged rejection guard to
designing its replacement at the actual formal, Apply, Catch and scheme
owners. The primary accepts the architecture finding that the existing native
algebra has no executable negative-permission/Catch-image operation. This
document proposes one. It does not adopt it, implement it, certify it, or
replace the original A/B obligation with a conditional feasibility claim.

Fix an originally formed source graph, its original annotation occurrences,
Function paths, formal registrations, lexical scopes and binders. Quantify over
one joint source assignment `xi=(nu,K,D)`, coherent substitutions of that whole
graph, compatible actual providers, actual received views, and every current
and later source lower/upper admission. Keep original complete Call, value,
effect, response, continuation, world and activity operands correlated. The
anchor is the original source abbreviation

```text
receive(f : Unit -> alpha+) = let g=f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int.
```

The formal starts negative; Function arguments reverse that sign and results
preserve it. Its outer AE is positive and omitted, outer RE negative and
omitted; the nested argument row is positive Ctrl allowance and the nested
result row negative Ctrl permission. Every path remains distinct. The selected
first-call component belongs to the outer complete invocation, has no written
permission, and is distinct from both scalar AE and RE. Its existing theorem
does not supply the nested second-use profile/applicability premise.

The required replacement must construct an open native negative port with
occurrence-local concrete permission; connect it through authentic source
uses; and constrain an actual Catch result by the original shallow handler
image. It must preserve unrelated and independent same-family contributions,
shared named references, rigid operands, raw suffix requests, and current and
future constraints. No handling follows from annotation alone.

The fixed semantics are [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,1.1,1.2,3; [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md)
§§3–5; [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6; and [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§3,9. Attachment set grouping and residual lineage remain selected by
[attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–4 and [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md).
[Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 govern normal accumulation and necessary abnormal safety.

The [selected known-Function source constructor](../design/2026-10-16-known-function-first-call-profile.md)
§§2–3 and its [construction](2026-10-16-known-function-first-call-profile-construction.md)
§§3–7 are inputs with their actual limits. Full Initial/world formation,
general profile supply, full native MODEL, soundness, required principality and
production remain original OPEN parents. This draft creates no new source
envelope. Old Oracle PUSH/POP or a concrete upper `Row` is not a universal
prerequisite of the proposed operation. Replacing an old proof edge requires
an explicit, reviewed replacement record; it does not prove the old theorem.

## 2. Actual baseline and the proposed cut

| Owner at the pinned baseline | Existing operation | Proposed change, requiring adoption |
| --- | --- | --- |
| `candidate_source.rs:600–655,720–748` | Registers the original formal/Name/scope; retains FormalAnnotation; emits OmittedFormal only when annotation is absent. | Retain a formal-port construction certificate for each negative concrete row; no OmittedFormal substitution. |
| `candidate_effect.rs:1119–1235` | Recurses over paired annotation terms; rejects negative concrete rows; installs slots 43/44 and `formal_domains` only after success. | Add the open permission-port construction below in the same paired recursion. |
| `candidate_call.rs:19–53`; `shadow_apply.rs:1518–1630` | Retains formal registration, source Apply operands, checking/cause and native four-port demand before admission. | Emit a complete invocation source-interface reference and a forward use relation retaining those exact operands. |
| `lib.rs:11317` (`admit_lambda_fact`); `candidate_effect.rs:805–824` (`candidate_operation`) | Constructs the actual positive producer Function and entry/body or operation-declaration ports. | Retain its complete source producer interface on that original admission, before copying/replay. |
| `candidate_source.rs:769–810,870–889` | Knows original Catch, ordered arms, payload/continuation binders; forwards the whole scrutinee effect at slot 51. | Emit one CatchImage relation; replace the unconditional scrutinee-to-result edge only when the new operation is proved/adopted. |
| `candidate_effect.rs:826–890` | Builds provisional packet/response/raw-continuation constraints; raw return effects conservatively include full scrutinee effects. | Keep original packet fields and attach their source subinterfaces to the Catch image. Replacing the conservative raw effect bound requires its own proved suffix correspondence. |
| `candidate_context.rs:3001–3067,3201–3290` | Retains Function field/parent relations and executes closed Allowance checks. | Add the new relation kind and guarded work rules to this one relation authority; do not reinterpret closed filters. |
| `candidate_scheme.rs:800–900,1089–1250` | Captures relation/context/view dependencies; prepares one coherent row/view/context map per use. | Capture and jointly map permission, complete-interface, image, lineage and pending obligations. |

The proposed cut preserves ordinary Value/effect inequalities. The new
operation is a retained constraint with source operands, rather than an eager
execution analysis, candidate typing search, global family deletion or second
reconstruction pass. The full source interface is necessary: an effect set
alone loses the raw-continuation distinction in §7.

## 3. Exact open-port construction

Use a separate arena for these ports. Do not put negative permission into the
existing `View.allowed`, `Support`, `Allowance`, `source_weight` or
`closed_weight` contracts. Existing covariant views remain governed by their
selected [checking/publication contract](../design/2026-10-10-concrete-effect-annotation-implementation.md).
In particular, suppressing `closed_weight` on an old closed view is not this
proposal.

Proposed records (IDs are private, checked and session-branded):

```text
NegativePort {
  owner, annotation, row_position, function_path, port_kind,
  registration, parameter, lexical_scope, composed_sign = Negative,
  level, inflow_row,
  binding: FreshOpen { original_row }
         | Named { original_scope, original_name, original_scoped_row },
  coherent_copy_map?,
  permission_set, construction_relation, positive_parent, negative_parent
}
PermissionSet {
  original_annotation, exact_row_occurrence, original_scope,
  members: [(original_ordinal, resolved_effect_operand)],
  instance: Original | Fresh { source_instance, use_origin }
}
PortConstruction {
  original_formal_registration, original_Function_path,
  exact_P_and_N_children, exact_parent_P_and_N,
  original_occurrence, cause, original_level
}
```

There is **one set identity per exact row occurrence**, with separate member
ordinals. Distinct occurrences remain distinct even when their resolved lists
or inflow row representatives coincide. The current source carrier supplies
nullary `SourceEffectId { module, declaration }`; these operands are copied
exactly, with an empty type-argument tuple. It has no parameterized-argument
carrier. Extension to nonempty invariant argument tuples is an existing OPEN
formation/comparison obligation, not a new language restriction or a claim
that erasing arguments is safe.

For a negative row with concrete set `C` and at most one written variable,
the proposed exact equations are:

```text
no written variable: eta := fresh_effect_at_level(original_level)
written 'e:         eta := annotation_effects[(original_scope, 'e)]
                    using candidate_formal_effect_variable
returned pair:      (live_effect_term(Positive,eta),
                     live_effect_term(Negative,eta))
permission:         PermissionSet(original_row,C), separately referenced.
```

There is no `Support(C) <: eta`, `eta <: Allowance(C)`, empty/closed bound,
new unrelated tail, or equation `eta = C | residual`. For the named case,
`'e` denotes the same whole flowing coordinate as the accepted singleton
negative symbolic case. It is not silently converted into a freshly allocated
remainder. Other occurrences of `(scope,'e)` use the same table entry; their
permission-set identities still differ. The original task contains no
multiple-name row; this draft does not select its interpretation or authorize
the existing multiple-name restriction as a language boundary.

An omitted row keeps the existing fresh paired open coordinate and gets no
concrete permission. A singleton symbolic-only row keeps the existing shared
coordinate and gets no concrete member. Positive concrete ports keep their
existing covariant Support/Allowance pair and ordered original operands.

At each Function frame the exact returned values remain

```text
P = PositiveFunction(argument.N, AE.N, RE.P, result.P)
N = NegativeFunction(argument.P, AE.P, RE.N, result.N).
```

The constructor emits the new certificate in that frame before returning P/N;
it records the existing slots 43/44 after those edges are admitted. It does
not discover the path by scanning a solved graph. Its validator checks source
registration and annotation ownership, composed sign, exact child ordering,
shared pair row, original scope/name lookup and original resolved ordinals.
An arbitrary row-equality witness cannot construct a certificate.
For a copied port, validate the original name against the original table and
validate `inflow_row = copy_map(original_scoped_row)` jointly with its parent
children. Do not overwrite `annotation_effects[(scope,name)]` with one use's
fresh row; that would collapse later independent uses. The unnamed branch
similarly maps its original allocation. An extrusion copy uses the actual
polar extrusion map; it does not allocate an unrelated open coordinate.

**Local derivation, not implementation certification.** The negative clause's
delta allocates/reuses eta and retains permission/certificates; it emits no
concrete effect lower or closed upper for eta. Therefore the permission list
alone neither entails Ctrl inflow nor excludes Write inflow. With one named
variable its equality is to the already selected scoped coordinate; with no
named variable the new coordinate has exactly the ordinary unconstrained
initial state. This follows by enumerating the operations above. Other real
constraints, including independently approved positive annotation interfaces,
may subsequently constrain eta. The statement does not erase those effects.

## 4. Source interfaces, routes and one identity authority

Permission is not stored as an attribute of canonical rows. Its applicable
position/view is carried through a proposed `SourceInterfaceRef` and typed
forward edges in `candidate_context`, using the already retained source nodes.
The reference denotes a graph of source constructor clauses, not a list of
currently observed effects or a guessed complete execution.

```text
SourceInterfaceRef { owner, original_source_index, original_rule_phase,
                     entry_role, original_scope_telescope, clause_root }
InterfaceClause = Return(source_value_ref)
                | Request(original_request_introduction, raw_suffix_ref)
                | Bind(first_ref, original_binder, next_ref)
                | Invoke(original_ApplySourceInput, complete_call_ref)
                | Execute(original_Comp_position, carrier_ref)
                | Handle(original_CatchImageId)
                | Reference(original_name_or_local_use, coherent_map)
                | Alternative(original_branch, guarded_child_refs)
                | OutsideMatch(original_handler, original_q_and_k,
                               arm_cursor, original_typed_bindings)
                | Pending(original_typed_obligation)
```

These tags are proposed native records of existing source constructors. They
are not additional source semantics. `candidate_source` would emit literal
Return and source Bind/branch/Catch clauses while it already visits those
nodes. A Value formal Name emits Return with its original registration/read
reference; a Computation Name emits its designated one-layer Execute.
Operation and Lambda expressions return their original producer descriptors;
their declaration/body and entry clauses remain latent until source Invoke or
Execute. Apply uses the actual `ApplySourceInput` and native demand fields;
its clause includes callee evaluation, actual argument Delay, entry/rebind,
body/native return and designated result consumption. **It is not an AE/RE
alias.** The full producer/complete-Call correspondence at that last step is
not supplied by current `NativeInterface` and remains OPEN.
The operation descriptor contains the original `MakeRequestThunk` result,
whose request-introduction clause activates only at its source-designated
consumption. A latent advertised Support member is never translated directly
to Request. Generated entry/selection/finish clauses use the original source
node plus its rule phase, so they do not pretend to have a new parsed source
node. Existing source descriptors and their subcode are shared by reference;
the proposal retains their outputs rather than reconstructing a second source
semantics from solved rows.

Retain the producer link where the native positive Function is actually
introduced, rather than infer its source from a later negative Function:

```text
ProviderIntroduction {
  original_Lambda_or_Operation_source, positive_Function,
  entry_role_and_original_formal_registration_or_operation_declaration,
  body_or_native_return_interface, designated_result_consumer,
  original_entry_and_result_rows, introduction_relation_and_bound_admission
}
```

`admit_lambda_fact` would attach this to its actual Function introduction and
entry/body constraints. `candidate_operation` would attach the declaration's
producer interface to its slot-42 introduction. Bound insertion, Replay and
FunctionPort then carry this same producer parent to the actual Apply demand.
The proposed Invoke consumer relates the **joint** producer and demand tuple;
it does not pair an effect lower from one provider with a Result lower from
another. A fresh or unknown formal's provider stays a variable/interface
constraint until ordinary lower propagation supplies an introduction.
`ProviderIntroduction` retains construction evidence; it does not prove its
complete interface valid or turn a successful scalar comparison into complete
Call membership. Imported opaque providers require their original independent
complete interface, not local source reconstruction.

Use the existing original relation/bound admissions as route parents:

```text
ForwardUse {
  source_interface, target_interface, source_position, target_position,
  registration_or_original_binding, Name_or_Apply_source,
  original_relation, actual_lower_and_upper_admission_refs,
  FunctionPort_parent_and_field?, FreshUse_or_extrusion_map?,
  same_assignment_substitution, inherited_packet_refs
}
```

Direct formal Calls join registration -> registered Name -> original Apply
checking occurrence -> actual FunctionPort parent. An alias adds its original
local binding and LocalUse/capture/FreshUse/Bound origin edges. A returned
callable uses the original Function Result path and result/rebind edges. The
new consumer follows these edges forward; it never finds permission by family
or endpoint equality. An unresolved source mapping is a pending obligation.
The existing formal-Name shortcut does not authenticate arbitrary alias or
second-use correspondence. No reverse edge writes receiver authority into a
provider lower or sibling alias.

One contribution/route authority lives with these source constructor records:

```text
RequestOrigin { original_operation_declaration_and_instance_operands,
                original_request_introduction, source_binder_telescope }
RequestOccurrence { origin, actual_invocation_or_resumption_binders }
Exposure { request_occurrence, original_executing_view,
           exact_observation_position, forward_route_parents }
```

Only the source request-introduction clause allocates a request binder.
Invocation/resumption substitutes that binder coherently; forwarding preserves
the original event and origin. A later raw-suffix request has a different
request binder/occurrence even if the nominal effect and declaration match.
Do not mint these from `AnnotationMember` or current row Support. In fact the
inspected production operation constructor advertises a latent declared
interface; `candidate_effect_contribution` has no ordinary operation-generation
caller. Existing `Contribution.instance` therefore cannot simply be asserted
to be this complete source-event authority. Bridging its future inputs must
use the same request-introduction owner, with a reference to that record.

## 5. CatchImage records and exact consumer contract

Retain a relation in the **same** `candidate_context` constraint authority,
with a proposed operation key alongside ordinary inequalities:

```text
ConstraintKey = Ordinary(existing RelationKey)
              | CatchImage { catch_instance }
              | ImageDemand { lineage, exact_output_upper_admission }

CatchImage {
  original_owner, original_Catch_occurrence, original_source_index,
  original_scrutinee_source_index, scrutinee_interface, scrutinee_effect,
  ordered_arms: [(original_pattern, guard_interface?, arm_interface,
                 payload_binders, raw_continuation_binder?)],
  actual_handler_activation_binder, owner_receiver_binder,
  incoming_permission_and_inherited_profile_refs,
  complete_original_scope_telescope, original_occurrence_and_cause,
  residual_lineage, gamma, exact_output_value_and_effect,
  source_input_admissions, output_upper_admissions, obligations,
  generation, completion_receipt
}
```

These are static symbolic activation/receiver binders, instantiated by the
original operation's semantics. A lexical scope number or `context_use` is not
a dynamic activation. Guards retain the original source telescope and can
refer to current configuration `C_h`, exact original event, profile, receipts,
typed paths, family/type arguments and current world. They are ordinary typing
constraints, not an opportunistic runtime filter.

Emit one CatchImage from the original Catch visitor. At adoption, its ordinary
residual projection replaces **only that Catch's** unconditional slot-51
scrutinee forwarding. Keep all original arm/value checking, packet, response
and source Bind constraints. Source-origin contributions outside this Catch
have no incoming image edge. Do not preserve the old conservative slot 51 and
then claim exact subtraction: that edge independently reintroduces everything.

The proposed meaning is precisely

```text
J_out = ShallowImage(original_H, J_scrutinee)
gamma = outward_effect_projection(J_out)
J_out <: original_Catch_result_interface
gamma+ <: original_Catch_output_effect-
```

It is a constraint on complete correlated source computations. Immediate row
subtraction is not its definition. Its work-rule cases are the original
source equations:

1. **Return:** leave the handler activation; apply the original value arm, or
   ordinary return forwarding when no value arm exists. Include that arm's
   computation, bindings, effects and result checking.
2. **Request:** retain the original request, current context and raw suffix.
   Construct ordered pattern/guard evaluation clauses outside each tested
   handler according to source unwind. The visibility formula uses exact
   `Active`, `Covers`, `Path`, `Protected` and local `Grant` from typed boundary
   §6. Selecting requires visible/matching/accepting conditions. `OpCompat`
   remains a separate required constraint on the selected arm; failure is a
   type conflict, not an alternative forwarding route.
3. **Selection:** omit this event from this image's outward request boundary;
   Bind into the actual arm outside the selected handler, passing the raw
   continuation. Include all native/arm effects and result obligations.
4. **Forwarding:** preserve this same request and its original origin, with
   exactly the source continuation wrapper required for still-enclosing
   handler computation. Retain guard/pattern effects before that request.
5. **Resume:** invoke the retained raw suffix in the actual current context.
   It has no automatic copy of the selected handler. Explicit source Catch
   around a resumption creates its own CatchImage and activation binder.

Concretely the consumer would append the existing selected
[outside-image equations](../design/2026-10-02-typed-source-owner-realization.md)
§6 as guarded graph clauses, with the original whole operand telescope:

```text
Image_H(Return(v)) = MatchValue_H(v)                         outside H
Image_H(Request(q,k)) = MatchRequest_H(q,k) >>= Finish_H(q,k) if Eligible_H(q)
Image_H(Request(q,k)) = Forward(q, lambda a,C. Image_H[k(a,C)]) otherwise
Finish_H(q,k)(Accepted(arm,bindings),C) = Run(arm,bindings,C)
Finish_H(q,k)(NoArm,C) = Forward(q, lambda a,C. Image_H[k(a,C)])
```

`OutsideMatch` retains the source ordered matcher cursor, original typed
bindings and original q/k pair; it does not store a live reference to the
expired candidate. If matching yields a new request qg with suffix kg,
ordinary Bind constructs
`Request(qg, lambda a,C. kg(a,C) >>= Finish_H(q,k))` outside H. Forwarding
later enters a fresh source-prescribed activation, never the old h. These
rules say exactly what graph edges must be emitted and which event they
retain. They do not supply a finite native evaluator for every guard or prove
that the proposed Invoke/Execute emitters already realize the whole graph.

Each case is stored with its source guard formula. Unknown eligibility remains
symbolic/pending; absence of a known Path or Grant is never a proof of its
negation. In particular complete profile coverage is needed to discharge a
negative visibility judgment. Storing all guarded clauses is not choosing
independent marginal witnesses: the same source witness, assignment, current
configuration and ordered guard outcomes govern the whole selected clause.
The collection is not speculative inference over possible typings.

### Feedback and exact outgoing tails

Each actual residual constructor retains a distinct lineage, even when source
rows or current keys coincide:

```text
ImageRecipe {
  lineage, CatchImageId, original_source_and_interface,
  retained_heads_with_original_request_route_refs,
  exact_residual_context, gamma,
  feedback: [ImageDemand(original_source, original_H, upper_admission)],
  projections: [(gamma, exact_original_output_or_tail, origin_relation)],
  lower_cursor, upper_cursor, pending_pairs, generation
}
```

For every actual upper `gamma <: t`, retain that **exact** projection and
`ImageDemand(J_scrutinee,H,t)` as source feedback. The latter requires every
applicable image clause to satisfy t and emits the corresponding source,
arm, response and continuation constraints. It never emits the generally
false `scrutinee_effect <: t`: handled requests may be absent and arm requests
may be new. Nor does it equate gamma with the annotation's named variable.
No artificial tail is created for a closed output: the exact closed target
remains its upper demand. Several outputs/tails of one recipe are retained;
separately created recipes are never merged by equal gamma/source rows.

This specifies the feedback obligation and its owning consumer. An effective
native rule that normalizes/discharges it for the required finite interface
language, preserving required principality, is the first central OPEN
algorithmic premise. An uninterpreted retained `ImageDemand` is insufficient
for accepted inference or publication.

## 6. Work ownership, extension, copying and publication

Proposed work variants are `RegisterNegativePort`, `ForwardUse`,
`RegisterCatchImage`, `CatchInput(image,original_lower_admission)`,
`CatchUpper(image,original_upper_admission)`,
`ImagePair(lineage,lower_admission,upper_admission)`,
`GuardDependencyChanged(image,generation)` and `TransportImage(map,source)`.
Every task retains its parent relation(s), occurrence/cause and source witness
telescope. Admission runs before scalar pair/equality memo shortcuts. The
constraint operation kind and exact image/lineage identity participate in the
same native memo authority; the old pair-only completion result cannot
discharge one of these tasks.

**Current and future lowers.** First install a watcher on the original source
interface and source-bound admission buckets; then snapshot their current
admission frontier and queue every original admission. New admissions use the
same watcher. A task keyed by `(image,lineage,original_admission,generation)`
deduplicates the overlap, with a separate retained origin for every physical
admission. Upper registration is symmetric. Processing a new lower visits
every retained upper; processing a new upper visits every admitted lower.
This is normal incremental propagation, not solving at generation. Semantic
row equality transfers both watcher sets, retained admissions and all original
image/lineage refs; it creates no permission.
The cursor ranges over immutable original admission IDs in append-only logs,
not saved positions in mutable live bound vectors. An original physical
admission and its later transported admission retain their explicit edge;
neither the current representative nor a shifted live index substitutes for
the recorded parent. This is a proposed watcher-specific protocol, not a
silent change to the selected ordinary bound-restoration order.

The [frozen complementary source audit](2026-10-16-catch-image-later-lower-feasibility.md)
§§2,5 supplies a concrete existing seam: `candidate_apply_effect` at
`candidate_extrusion.rs:876–899` appends an ordinary lower and
`:799–840` replays its opposite bounds without necessarily inserting any new
FunctionPort dependency. The new watcher therefore hooks **general effect
bound admission and its image-source interface association**, not merely
FunctionPort insertion. The existing source-support registration factory is
`cfg(test)`; its invalidation footprint only watches FunctionPort insertion.
It cannot certify this proposed Catch image's dependency closure. This audit
is complementary producer evidence, not independent review of this draft.

**Late dependencies.** A new profile/route/arm/upper dependency dirties the
image generation before any dependent result can be used. All early effects
are retained as guarded relations. An unconditional derived fact is admissible
only with a proof valid for every completion of its remaining source guards;
partial inventory cannot justify `not Protected`. Generation-dependent
approximations live in a private owned overlay until discharge, rather than
being silently inserted into irreversible ordinary lower stores. Invalidation
withdraws that overlay and dependent completion/publication receipts, retains
all newly accepted constraints, and requeues the relevant pairs. This overlay
and its publication protocol are a new architectural obligation, not something
the current journal or relation memo already proves.
At fixed original `xi,q,C_h`, pending eligibility is lack of established
knowledge of that predicate, not a semantic event changing from ineligible to
eligible. Generation changes belong to evidence processing. They never modify
the original source event, world, activity configuration or language law.
In particular, forwarding E unconditionally while a guard is pending cannot
be repaired by later discovering handling: ordinary append-only lower bounds
have no inverse deletion operation. No such fallback is permitted here.

**Suspension and completion.** The source action owns its image continuation,
lower/upper cursors, pending children and generation. Queued is not Complete.
Unknown guards or an unsupported exact image normalization suspend the affected
private interpretation/query with its accepted constraints. An open source
constraint need not be solved before capture or FreshUse: those operations may
retain/map the **whole live image relation**, its pending clauses, source free
operands and future watchers. Their completion receipt covers emitted work and
the validity of that retained graph transfer, not a claim that all semantic
guards are true/false or no later lower exists. Generalization requires its
ordinary binder/level/free-support proof extended to those operands; bare-root
capture is insufficient. A public target that carries these constraints needs
the corresponding valid constrained-scheme theorem. A target/query claiming a
solved residual or unable to retain the relation must wait for its sufficient
discharge; an empty current frontier cannot supply it. A late edge invalidates
generation-dependent solved receipts first. Suspension is safety, not normal
inference closure or a new source rejection. The existing source/drain
continuation machinery supplies candidate attachment points, not proof of this
new lifecycle. Necessary abnormal safety follows top-level principles:
discard/stop an invalid private attempt if its guarded overlay cannot be reused
safely; no unconditional capacity restoration requirement is introduced.

**Capture/FreshUse.** Capture the reachable operation/permission/interface/
recipe graph and all guards, witnesses, projections and pending dependencies
together with the existing row/context graph. Extend the one FreshUse map by
`permission_instance_map`, `interface_map`, `image_map` and `lineage_map`;
these are construction maps, not independent solving caches. Allocate mapped
rows and recursive graph shells before connecting children. One source-owned
annotation instance maps to one fresh set identity per genuine local generic
instance; repeated references within that use share it. An inherited receiver
boundary/profile remains the same historical boundary; copying its view does
not allocate a new boundary or local grant. Distinct generic instances do not
share local attachment authority merely because a row remains shared.
Source ownership of the annotation instance, not row genericity alone, decides
which identity is freshened. Record that ownership at formal construction and
use the existing source frontier/owned-region evidence at capture.

Extrusion applies its actual level/polarity row map jointly to every operand
and retains original permission identity and source provenance. It does not
create a new local annotation instance. Qualifying intrusion equates only its
recorded parent/copy rows and transports both bound sides and pending image
dependencies; it never equates permission sets or residual lineages. All copy
validators check one source-to-target tuple under the same map, original
resolved operands and binders; separate witnesses for endpoints are invalid.

**Cost and cycles.** Port construction takes O(annotation nodes + written
members), with one open row for each unnamed port. No provider inspection is
needed. With finite retained sets of I image instances, L input admissions,
U output upper admissions and A arm clauses, a completed nonrecursive wave
has O(sum_image L_image * U_image * A_image) pair/arm work plus typed-guard
work and actual output size; storage retains actual origins and shared graph
nodes. This is a structural bound, not a claim that the guard work is constant
or that all recursive sets are finite.

Source/interface recursion uses explicit backreferences and a worklist, not
unfolded route strings or fresh lineages on every replay. A lineage is allocated
at an actual source residual construction or genuine coherent FreshUse of it.
Repeated replay of that construction keeps it. A new genuine construction
retains a distinct lineage. Cyclic constraints may still generate unbounded
contexts, substitutions or image demands. Existing two-circuit acceleration
does not certify these new mixed Catch/Call cycles. A general exact finite
closure/termination and required-principality argument is OPEN. Keep H3/P off;
do not turn this uncertainty into a source cap or a claimed completed compiler.

## 7. Finite source-origin discriminator and local equations

The following is a finite source-rule discriminator, not an executed or parsed
fixture and not evidence that the current negative preflight accepts it.
The declaration, ordinary Lambda, block-local Bind, Apply and Catch forms have
the actual owners in §2; the same Catch/resumption syntax appears in
`crates/yu-solver/tests/candidate_operation_catch.rs`. Keep each printed
occurrence distinct and resolve both names by their source binders.

```yulang
act ctrl:
    our ping: () -> int
act write:
    our next: () -> int

my once u = ctrl::ping()
my twice u = { my first = ctrl::ping(); ctrl::ping() }
my relay(cb: () -> [ctrl] int) =
    catch cb() { ctrl::ping(), k -> k 0, v -> v }
```

For the discriminator fix an independently valid original source environment
and complete typed input/view/receipt premises for the actual `relay` entry;
the local Ctrl annotation permission applies to that direct callback view.
Do not assume a full profile theorem for the nested `alpha+` anchor. Current
full source admission is not proved by the printed program. The derivation
below comes directly from the proposed emitters and original source equations,
rather than a checker supplied with event transitions.

Original constructor origins are:

| Symbol | Actual source constructor owner and retained origin |
| --- | --- |
| a | `relay` formal annotation's exact result row; FormalAnnotation/paired RE frame. |
| c | Apply of the registered Name `cb` to the original Unit; `ApplySourceInput` and its native demand. |
| h | The original Catch enclosing c, with ordered operation/value arms and raw continuation binder k. |
| o1 | Apply of the resolved operation in `once`; its declared producer's designated result consumption introduces request q1. |
| o2, o3 | The two distinct operation Applies in `twice`; block Bind retains o3 as the actual suffix after o2. |
| r | Apply of the raw continuation Name k in the operation arm, outside h. |

Let `Req_i(k)` abbreviate the original Request constructor with its original
event/origin and continuation, keeping current store/configuration arguments
implicit here only. Let `R(v)` denote Return. Source Bind yields

```text
J_once  = Req_1(lambda x. R(x))
J_twice = Req_2(lambda x. Req_3(lambda y. R(y))).
```

For this fixed valid entry, its exact active local grant, coverage and matching
premises select the displayed operation arm, whose `OpCompat` remains an
independent typing premise. Ordinary shallow selection and raw Resume then
derive

```text
ShallowImage(H,J_once)  = R(0)
ShallowImage(H,J_twice) = Req_3(lambda y. R(y)).
```

The selected handler h is absent at r. Request q3 is fresh at its original
suffix introduction; no old observation or earlier selection removes it.
Both inputs have the same immediate nominal support `{Ctrl}`, while their
outward image supports differ. Thus **no function of that nominal support
alone** can be the exact shallow-image operation on this source-rule fragment.
This refutes the proposed shortcut of implementing the new relation solely as
`eta minus declared_Ctrl`. It is not a counterexample to the preferred complete
interface design, a claim about every finite abstraction, or a proof of current
native source reachability.

There is also an authentic source-origin later-lower order to preserve.
Consider the ordinary source caller `answer = relay(Name once)`, with relay's
body inferred before the actual provider has reached its formal. Its outer
Apply Argument child emits `actual_once+ <: formal_cb-`; replay with the
already retained cb upper demand reaches the same call's ResultEffect child.
The audit above traces the actual owners to `lib.rs:12644–12664`. In the new
constructor, restoration first registers the captured image and its live
source watchers, before restoring/emitting the source bound admissions that
can reach it. The resulting original admission L_once must queue
`CatchInput(image,L_once)` even if no new FunctionPort is added at that final
effect insertion. Replacing once by twice preserves those source owners but
gives the distinct raw-suffix interface above. No arbitrary hand-inserted
Contribution or test-only support factory is a premise.

For the empty-initial-frontier case, the retained equations are

```text
register image I and output upper U with no discovered provider lower:
    keep I, U and pending ImageDemand(I,U); do not conclude gamma = empty.
admit authentic L_once later:
    queue (I,L_once,U); its complete guarded image checks R(0) against U.
admit authentic L_twice later into a source alternative of that same I:
    queue (I,L_twice,U); retain/check Req_3, with its own original guard.
```

The last line describes a later lower only when an original source branch/use
really supplies it to that image; it does not merge two independent generic
relay uses. A source `if b { once } else { twice }` retains both original
provider alternatives and their common b under the same source assignment.
Its invocation constraint therefore supplies their guarded source interfaces,
not independently selected marginal event lists. There is no claim that the
baseline's rejected negative formal executes this new schedule.

Further same-origin equations, under their original typing/eligibility
premises, discriminate the named failures:

```text
Permission_a(Ctrl), no Catch: J remains J.
J = R(v):                   image adds no declaration-only Ctrl.
J = Req_Ctrl(lambda x. Req_Write(k)), H arm resumes raw k:
                            image = Req_Write(k).
J = Req_Ctrl(k), H arm calls a distinct ctrl::ping() outside H:
                            image includes that arm's fresh Ctrl event.
```

The last event may share a family and even operation declaration with the
handled request; its distinct source introduction/route survives. Likewise an
independent same-family contribution in an unrelated output or latent result
has no incoming image edge and is preserved. Independence alone does not
immunize a genuinely exposed, otherwise visible request from ordinary handler
selection: eligibility follows its own complete source route and current
configuration. This draft introduces no origin veto.

To instantiate the original nested anchor, `f(Unit)` returns an actual `g`
through the original Result/rebind route; g's nested negative RE uses the
eta/permission pair from §3. The second `g(Unit)` and any surrounding Catch
need their own complete source use/profile/receipt/Observe derivation. The
selected outer first-call component cannot be reused as that evidence. This
is an explicit remaining source premise, not permission to drop that case.

## 8. Central invariant: exact proof status and first missing premise

The proposed decisive invariant is:

> For every original source witness under the unchanged joint assignment and
> source telescope, the negative-port emitter changes only the retained
> permission/ordinary symbolic connections; each reached Catch image consumes
> exactly the original shallow source event/route under its own guards, keeps
> every other image contribution, and commutes with lawful joint substitution
> and later-lower extension. Native completion/discharge preserves this same
> relation for all original source constructors, copies and later admissions.

This invariant is **OPEN**. The following are useful local derivations with
different scopes:

1. The proposed negative-port clause is open and adds no permission-only
   concrete lower or cap, by its explicit operation list (§3).
2. The proposed watcher protocol covers every admitted lower/upper pair if
   admissions and watcher installation are atomic in the one work owner: a
   pair is either in the registration snapshot or queued by later admission;
   overlap is deduplicated by the same admission/generation key. This is a
   protocol lemma, not evidence that existing source constructors emit it.
3. For supplied complete source interfaces with fixed original handler/view
   operands, relational image distributes over union of *whole correlated
   source computations*. Thus `Image_H(J union Delta) = Image_H(J) union
   Image_H(Delta)`. This is not a per-row-member linearity law and does not
   permit independently assembling marginal continuation/guard witnesses.
4. Lawful joint substitution commutes with the original source Request,
   Return and Bind equations when it preserves resolved rigid operands,
   typed paths/receipts, activity configuration and all guard truth. Applying
   the same substitution to h, its raw suffix, its source/arm interfaces and
   every occurrence identity gives the same shallow-image clauses. General
   row quotienting is not this injective/coherent transport lemma and needs
   its own semantic equality proof.

These derivations do not close the invariant. In particular later lower
extension must be interpreted at a fixed complete source environment. A new
dependency that changes an earlier unknown profile/visibility fact requires
generation invalidation (§6); the union equation cannot justify retaining an
obsolete unguarded result. An executable native discharge proof must show
that guarded clause propagation has exactly this meaning, not merely store
the formula and call it interpreted.

The first central missing owner is the joint
`SourceInterfaceRef/Invoke -> CatchImage/ImageDemand` native consumer:
construct complete original invocation/continuation clauses from actual
producer/use source constraints, then normalize their guarded image into the
selected finite interface language with current/future lower coverage and
required principality. Native four scalar fields, current zero-word filters
and retained SourceAnnotation do not implement that operation. No existing
result establishes that normalization or the new dependency overlay's
soundness. The original complete Call/native correspondence and A/B inference
parents retain ownership and OPEN status. Full profile/world inputs can be
supplied as independent semantic premises for a bounded lemma, but cannot be
reported as constructed by this draft.

Before dependent implementation/adoption, the decisive next proof must derive
or refute that actual source-to-consumer operation, beginning with §7's two
raw-suffix cases and an added lower after a registered image/upper demand.
A separate producer/reviewer must attack source coverage, shared named eta,
two fresh uses, independent same-family arm output and a resumed new request.
The primary assigns fresh semantic and source/conformance review. The author
does not certify this draft. Explicit user adoption is still required for this
new architecture after the required invariant is resolved.

The primary accepts both bounded reviews and retains the joint consumer gate
OPEN. In particular, existing `candidate_catch_operation` slot 65 sends the
full scrutinee effect into raw-continuation return effects. Together with arm
effect forwarding, that would reintroduce Ctrl even in the once/resume case
after deleting Catch's slot 51. The exact source-suffix correspondence replacing
that bound remains part of this central gate, alongside later-lower wakeups,
copy/publication and guarded normalization. No approval is requested on the
basis of the conditional worklist result.

## 9. Checks, dependencies and commit packet

Static-only packet, 25-minute cap. No production code, tests, snapshots,
configuration, questions or shared records are edited. No Git mutation, build,
test, executable probe, benchmark, network or child agent. CPU/RSS are not
instrumented. Requested normal configured Sol/high; actual runtime model and
effort metadata unavailable. No Astra or hot-reload claim.

Baseline dependency checks compare every inspected source/design listed below
to `2140859b13b4450303dc4873a8cdb299e59169eb`; no dependency delta was observed.
Local Markdown link/fence/whitespace checks and the final frozen file hash are
reported to the primary at handoff. None is mathematical or source review.

| Direct dependency | SHA-256 |
| --- | --- |
| selected known-Function design | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| selected source construction | `7051eafe3221b97229a760e52639f6a5c329860175ded210e7953a77a395e42a` |
| annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| existing covariant implementation contract | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| ordinary computation semantics | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed boundary | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| source owner/outside-image equations | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| attachment admission | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| residual lineage | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| complementary source audit, review metadata integrated | `63ace8b183386737f4b328a2840a4e1585dc6ede22d9df7ec88a37ea92070e67` |
| HIR/source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| solver/candidate_effect.rs | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| solver/candidate_context.rs | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| solver/candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| solver/candidate_call.rs | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| solver/candidate_scheme.rs | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| solver/candidate_extrusion.rs | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| solver/shadow_apply.rs | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| solver/lib.rs | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| existing operation/Catch source controls | `8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484` |

Commit packet:

- Exact lease/change: `notes/theory/2026-10-16-open-negative-formal-catch-image-design.md`.
- Baseline: `2140859b13b4450303dc4873a8cdb299e59169eb`; changed dependencies:
  none observed; primary revalidates the frozen dependency cone.
- Status: independently reviewed Draft/unapproved research architecture;
  central source/native construction, normalization and lifecycle invariant OPEN.
- Checks: static owner trace and baseline/hash comparison; artifact integrity
  and frozen SHA-256 supplied on handoff; zero executable verification.
- Suggested research checkpoint: `research: draft open negative ports and source Catch images`.
- Shared deltas left to primary/curator: record this unapproved proposal and
  its exact central OPEN consumer premise; retain preflight, H3/P, original
  complete Call, profile/world/MODEL, A/B, hygiene, principality and production
  gates. Any old proof-edge replacement needs its explicit reviewed record;
  no old theorem is marked proved or retired by this note.
