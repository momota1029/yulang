# Catch matcher target declarations at the outside occurrence

Status: Draft source-definition proposal; candidate mathematics, independent
review NOT RUN. No adoption, reviewed theorem, accepted-source, implementation
or production authority. Supersedes: none.

Author: `/root/catch_matcher_target_declaration`, sole author; no descendants.
Assignment: `CATCH-MATCHER-TARGET-DECLARATION-20261017`, revision 1.
Contract: `catch-matcher-target-declaration-20261017`, revision 1, SHA-256
`ccb332b41ae50c5361a977bbe6ba9791c5854123c3a20958e70a732ab5262170`.
Supplied baseline: `d329427fc`; inherited semantic checkpoint:
`e855987e642a02c6060fd2bdd93864a19b0dba3f`. No Git inspection.
Requested role/model/effort: astra_prover / gpt-6-astra / medium.
Observed effective model/effort and opaque runtime session ID: UNKNOWN.

## 1. Parent, proposed decision and result

Original FORWARD-FIRST-CALL A/B, F1 and FK1 remain OPEN with their original
quantifiers and accepted source domain. F1 retains the finite monomorphic
decorated graph Ω, valuation ν, capture root/cut, complete typed ports/maps,
lexical environment and child/parent contexts, every original saved occurrence,
current C and ρ, joint history J, ξ=(ν,K,D), admitted joint response
τ=(r,C_resume,η), actual provider, output-dependent future, finite interaction
and licensed prefix. Universals remain external and original existential
witnesses remain at their introductions. FK1 independently includes genuinely
opaque continuations and their complete application/transport interfaces.

The change proposed here is an explicit internal source declaration for the
original outside `MatchRequest_H` occurrence μ_H. It supplies a metadata
eliminator with an operational body and a typing introduction, a payload input
port and variable-binding rule, and a raw operand/continuation-binding schema.
These are proposals for adoption, not deductions that the old implicit matcher
already had these declarations. The former failed Var/retention argument is
not used to confer authority on them.

The metadata rule is fully specified below and has a direct local preservation
argument. The payload variable case also has a construction-directed path
map. The raw schema explicitly has different response-entry B and saved-suffix
answer A owners; its complete typing preservation remains blocked at the
original suffix/descriptor and current-owner actions identified in §6. Thus
this proposal supplies concrete definitions for review but does not fill all
of adopted MI-Intro premise 6 or construct a complete M_exit.

Governing meaning: typed-source-owner §6 selects outside matching; the October
17 adoption selects matcher-input §§2–4, including conditional MI-Intro.
Typed-boundary §6 distinguishes stored views, transport, receipt, observation
and current incidence. Source contracts §2.2 requires independent descriptor
validity; IF-Use registers a typed use only after its primitive is typed.

## 2. Common parameters and the proposed administrative source forms

Use the original typed Request derivation δ and actual exit ε. Invert δ at
its original constructors, retaining all original parameters in order:

```text
Γ0; Ω; ξ=(ν,K,D); J_y;
H, its lexical descriptor and ordered arm interfaces;
op[θ], actual provider/instance, C_y, ρ_y;
v_P with its original complete admitted operation-argument view;
q : Event(op[θ],provider,v_P,C_y,J_y; origin and original evidence);
Δ_q : original response/admission/future declaration;
raw : RawHandle(q,Δ_q; e_saved,t,k, original suffix declaration S);
δ, Elig_y; ε; its actual output C_out,J_out,ρ_out.
```

Here θ is the original scoped substitution, including symbolic family/type
arguments, not a newly chosen instance. S names the original declaration of
the entire saved suffix up to its answer boundary. It is not the parent
continuation a after that boundary. Inversion exposes a declared S where δ
actually contains it; absence of such a declaration is a failed formation
case, not permission to infer it from Δ_q or an arrow skeleton. No additional
premise says the matcher use, M_exit or TypedMatchInput is already valid.

Propose the following internal source forms, inserted only at the existing
eligible Request clause's μ_H after ε. They are not user syntax, new runtime
effect operations, ordinary first-class Event values or a replacement matcher:

```text
InspectRequest_μ(q; z. c)          -- bind a metadata tuple, then c
PayloadAt_μ(q)                    -- the original admitted payload view
RawAt_μ(q,raw)                    -- the same whole raw operand
BindPayload_μ,i(x,v; c)           -- variable-pattern binding
BindRaw_μ,i(k,raw; c)             -- original continuation binding
```

The existing ordered matcher is elaborated as
`InspectRequest_μ(q; z. MatchArms_H(z,PayloadAt_μ(q),RawAt_μ(q,raw)))`.
`MatchArms_H` is a spelling of its existing ordered pattern/binder/guard code,
not an independently postulated relation. This proposal specifies its entry
operand declarations and the indicated binding cases; it does not supply
unknown general pattern/guard/forward bodies by this abbreviation. The
surrounding `>>= Finish_H(q,raw)` stays at its original output-dependent seam.
Inspection is before an arm outcome and has no success/Selected premise.

This elaboration is a proposed source-definition extension requiring review
and adoption. In particular its administrative inspection step and the raw
public-view schema must not be silently counted as existing accepted rules.

## 3. A complete metadata declaration and authentic introduction

Declare a distinct internal sort `HistoricalMeta(q)`. It contains the exact
dependent Event parameters, in their original order: resolved declaration and
θ; provider and operation instance; reference to the admitted payload carrier;
origin/event identity; emission indices C_y,J_y,ρ_y where present in δ; and
references to the original observation/evidence fields at those indices. Its
component types are the corresponding parameter declarations of Event,
instantiated with δ's actual fields. There is no χ profile of q as a value,
no Function signature for q, and no current eligibility field. All additional
fields in the original Event telescope are included at their declared order;
this is dependent elimination of that complete telescope, not a new selected
subset of it. The result tuple is internal metadata; its carrier reference
is not a conversion of the event to a payload value.

The target declaration at μ_H is

```text
q_arg : Event(op[θ],provider,v_P,C_y,J_y; original evidence)
z_μ   : HistoricalMeta(q_arg)
```

Define `fields(q)` by dependent pattern elimination of the actual Request's
Event constructor under δ. It returns its original parameter references;
where Event is abstract, this rule specifies the constructor's metadata
eliminator as part of the proposal, rather than assuming a generic value
projection is available. Its declaration is usable only for an Event operand
at a Request inspection site, not for an arbitrary ordinary source value.

The operational clause is explicit. At the actual post-exit control position,

```text
⟨InspectRequest_μ(q; z. c), C_out,J_out,ρ_out,G⟩
  →admin ⟨c[fields(q)/z], C_out,J_out,ρ_out,G⟩.
```

G is the existing evidence graph. The transition reads the same q operand
already carried to μ_H by the original Request clause. It does not search a
global event registry, require replay of an emission, or access a saved store.
No runtime event, Observe, Receive, boundary, grant, response or predicate is
allocated. Thus `G'=G`; only the administrative program expression changes.
`C_out`, not C_y, is the control state throughout.

The authentic source introduction `Meta-At-Exit` is proposed as:

```text
δ derives the original Event constructor and yielded Request(q,raw)
ε is its actual eligible H exit to the original μ_H at C_out,J_out,ρ_out
μ_H is elaborated by the InspectRequest declaration above
-------------------------------------------------------------------
the actual q operand at μ_H admits InspectRequest with result
fields(q) : HistoricalMeta(q), retaining its original dependent indices.
```

The third premise is a source declaration occurrence, not a proof of target
typing. Its grammar, domain, body and result type were independently specified
above. Source typing of a following c uses the ordinary dependent substitution
rule from `z:HistoricalMeta(q)`; typing arbitrary c is not a premise needed
to type this read itself. This differs from assuming `TypedMatchInput` or
postulating that some unknown use is typed.

Local preservation attempt succeeds in the proposed calculus: inversion of
δ gives each actual constructor argument at the matching declared parameter
type. In dependency order, substitute each earlier argument into the next
declaration. The resulting tuple therefore has HistoricalMeta(q). Substituting
it into c preserves each reference and its original binder scope. The step
leaves current state and G unchanged, so neither historical eligibility nor
an emission-world fact is coerced into a current-world assertion. This is a
finite dependent-constructor elimination/substitution argument, independent of
matching success. It proves no implementation correspondence and remains an
unreviewed argument for an unadopted rule.

An arm's declaration comparison reads `z.op`, using the original ordered
matching rule; OpCompat remains the existing static constraint on accepted
arms, never a new dynamic filter. Reading `z.observation` cannot serve as a
fresh observation under the payload or k view. If matching suspends later,
the metadata tuple contains only the same historical references and can be
retained with the original pending matcher frame.

## 4. Payload declaration, binding and path construction

Let `P_op[θ]` be the complete argument-interface graph declared by op, including
its polar positions, provider/carrier and membership/admission clauses,
effects, residual paths, evidence ports and dependent binders. δ supplies the
actual admitted payload at the operation's argument port s_P, including its
original correspondence from the actual provider view to that port. A carrier
identity alone does not supply this admitted view.

Declare the matcher input position `t_P=(μ_H,payload)` by instantiating
`P_op[θ]` at that actual occurrence. Its evidence root is a fresh *view root*
whose incoming edge is from the admitted view at s_P. It is not a boundary,
provider, predicate, event or source witness. Define the operand body:

```text
PayloadAt_μ(q) = the complete v_P view carried by q's Request derivation.
```

The `Payload-At-Exit` introduction inverts δ's original admitted argument
binding, projects the same payload field, and instantiates the declared
`P_op[θ]` at μ. The target type is selected by this proposed declaration;
it is not inferred by guessing an equality of path sets. Substitution into
the source and destination occurrences of the same declared schema then
derives their structural correspondence as follows.

For each node n of the finite decorated P_op graph, retain the original schema
node n and create its target occurrence `(μ,payload,n)`. For every schema edge
`n --l--> n'`, create `(μ,payload,n) --l--> (μ,payload,n')`, retaining its
polarity, effect/value distinction and annotation occurrence. Map a source
path consisting of the s_P root and edge sequence w to the target root and
the same w. The inverse removes the target occurrence tag. Recursive graph
backedges are mapped once by node identity; no infinite unfolding or merging
of two annotation occurrences occurs. Thus there is a proved structural
bijection j_P between these two declared occurrences. It does not equate
unrelated provider or arm types. The original provider-to-s_P map remains a
separate preceding edge, with all its original witnesses.

Use the existing typed transport operation:

```text
χ_tP = (j_P)_*χ_sP       D_tP = (j_P)_*D_sP
K_tP = K_sP             L_tP = L_sP
```

Every output path incidence has its source tagged preimage. Its b, predicate,
provider and witness identities remain unchanged. The graph copying above
concerns occurrence positions only; it does not copy/freshen K or source
existentials. Other source views of the same underlying v remain separate.

For an ordinary variable pattern x, propose the declared binder
`x_i:P_op[θ]` at the actual pattern occurrence with the same occurrence-schema
construction j_x, and the explicit reduction

```text
⟨BindPayload_μ,i(x,v_P; c), C,J,ρ,G⟩
 → ⟨c, C,J,ρ[x_i↦the transported whole v_P view],
       G + Flow(t_P,x_i,j_x) + Receive(u,slot_i,x_i,j_x)⟩.
```

Here u and slot_i are the actual current invocation/typed binding slot supplied
by the existing outside owner-resolution rule at that binding step. They are
not H or owner(H) by default. This notation displays evidence updates; it does
not assert that the physical runtime allocates these exact records. An
ordinary typed binding creates its existing Receive edge; it creates no
boundary or concrete contract. If current owner/slot formation is unavailable,
this binding's full introduction is unavailable. That is an owner obligation,
not solved by historical δ. A wildcard performs no binding or receipt.

For this variable case, whole-packet typing and path/profile preservation
follow by schema substitution and j_x after the current owner is supplied.
Other patterns, structural projections and independently annotated binder
interfaces require their actual original typed rules and maps. In particular
an arm expecting a distinct interface does not acquire j_x by naming it
P_op. This proposal does not reject such arms or equate their interfaces;
their original constraints/compatibility and pattern derivations remain due.

## 5. Raw operand and continuation-binder declaration

The independent declarations controlling the raw view are:

| Coordinate | Original supplier | Target role |
| --- | --- | --- |
| B and Δ_q | op result declaration and the actual request response/admission/future family | Response entry, including the same admitted τ and actual provider/Future(r) |
| A_S and output evidence | Whole saved suffix S at its answer boundary | Answer after executing the entire suffix, with its actual returned provider and output-dependent future |
| e_saved and saved code t,k | Original capture/Bind derivation | Dependent lexical environment and ordered pending computation |
| Current C,ρ and control owner actions | Actual call/resume and existing owner resolution | Execution state; never a captured store/active-handler snapshot |
| Caller continuation a | Original surrounding Call/Bind | Continuation after the answer; not part of A_S or substituted for k |

A_S is a dependent family owned by S. It may depend on the admitted τ and the
actual output state/history/evidence ζ. It is not a fresh result type chosen
at matching and need not equal B. The public continuation schema must retain
these dependencies, even if both have the same printed skeleton in another
program.

Propose the target raw-use telescope, in dependency order:

```text
Γ_hist; q; Δ_q; S and its declared entry/answer/effect interfaces;
e_saved : Env_S at its original capture indices;
raw_μ : RawOperand(q,Δ_q,S,e_saved,t,k);
u,slot_k,C,J,ρ : actual current binding context;
k_i : ContinuationView(raw_μ; R_S).

R_S = dependent callable interface with:
  entry: the original Value-response entry protocol;
  response tuple: τ=(r,C_resume,η) in the ORIGINAL AdmResponse(Δ_q);
  response view: r at B[θ;q,η], its actual provider and Future(r);
  body: the SAME t with e_saved extended by that whole τ,
        then the SAME saved k, outside the consumed H;
  observations: the body's original Return / Request / licensed Pending
        alternatives, with all original joint evidence;
  answer: v at A_S[τ;ζ] at S's actual answer boundary, with ζ's current
        state/history, returned provider, residuals and output future;
  continuation seam: the original typed insertion of that whole answer
        into the surrounding caller suffix a.
```

Entry-effect positions, body computation/effect positions and A_S's latent
positions are distinct. No operation-emission effect is pasted onto B's
latent interface. Entry forcing follows the original Call rule; a body effect
is not moved to an argument or returned latent position. The interface is
declared over the original full response admission domain, not the responses
for which a later descriptor test happens to succeed.

The operational body of RawAt is projection of the same handle from the
original Request operands. BindRaw binds that same semantic handle, with a
new use view at the declared R_S port and the existing typed binding/Receive
rule under actual u,slot_k. It neither calls raw nor chooses a response. The
underlying handle is not replaced by a semantically new opaque continuation.
Any native executable wrapper must separately represent this same handle.

For structural raw handles, the proposed callable body is specified by the
pinned P2 equations, without an Image or membership oracle:

```text
CallRawBody(Raw(t,e_saved,k,Δ_q), τ, a; o)
  iff Append(k,a,b)
      and O_t(e_saved extended by THAT τ, C_resume,b,J; o).
```

`Append` and `O_t` keep their actual conditional P2 premises and original
frame bodies. Here b is Append's existing result witness at its original
scope, not a fresh independent source existential. The response/answer cut
used to declare R_S has `a=End` at S's
answer boundary; later ordinary Call composes the actual caller a. It is
invalid to take the final answer of `Append(k,a)` as A_S when a changes it.
No H is reinstalled in this structural raw body. Explicit forwarding wrappers
remain separate source constructors and may install their own fresh H.

The source declaration `Raw-Bind-Decl` constructs R_S from the independently
declared B, Δ_q, S, e_saved and code graph, then declares raw_μ and k_i with
the body above. It is a genuine definition with an operational body, not a
rule whose premise is “k_i already has the desired typed use.” Its proposed
typing introduction must establish descriptor membership for that body on
every admitted τ from δ's original capture/suffix typing and the original
constructor preservation rules. A function-shaped declaration alone does
not establish that introduction. This is the precise preservation gap below.

Candidate incidence maps are construction-directed component maps: Δ_q's
declared B ports to R_S.response ports; S's computation ports to R_S.body;
S's answer ports to R_S.answer; each captured reference to its own declared
environment slot. Each is the occurrence-schema map of §4 on its actual
complete declaration, with original tags. There is no blanket map from q's
observation, the operation's outer effect, or all private environment paths
to the public function. Private references stay private in the evidence graph.
An original raw root or cross-component dependency needs its explicit source
declaration edge; the table is not a total map for unspecified edges.

For the pinned specimen, the proposed value skeletons instantiate as
`P=Unit`, `B=Int→Int`, `A_S=Int`, with saved body `ApplyOne(r)=Call(r,1)`.
Thus k has a B-response/A-answer skeleton `(Int→Int)→Int`. This does not
type its full interface, claim the specimen is accepted, or supply the later
Luna lane's complete binder equations. k id still needs its actual Call entry,
admission and future; raw is not specialized to id when it is bound.

## 6. Preservation attempt and exact missing cases

The local metadata step is independent of any current live-H proof. The
payload occurrence map preserves the complete declared packet after the
original payload admission and current binding-owner premises are supplied.
Both arguments preserve the source witness scopes and work with empty or
nonempty profiles; no empty profile is selected to simplify the proof.

For raw preservation, inversion of an original structural Request identifies
t, e_saved and k. Unfolding the specified body gives exactly P2 Resume;
Append preserves the order of saved frames and uses the same τ. At the
Return/End subcase the suffix's independently declared answer port supplies
A_S, and the occurrence maps preserve its actual evidence. At Bind, the next
frame's original output-dependent input must receive the actual preceding
answer tuple. This is a concrete attempted induction on the supplied
constructor derivation (or finite licensed-prefix derivation), not induction
on a possibly cyclic graph's node count.

The induction cannot finish on the full original domain from these pins.
P2's OriginalFrame_f cases still require their real local bodies and complete
world/admission/provider/future actions. In particular an arbitrary current
world cannot be replaced by C_y, and a retained suffix typing at an old index
is not automatically valid for every Δ_q-admitted τ. The current owner/slot
at a resumed binding also needs the actual source owner-resolution action.
These failures are at concrete consumers: original matcher BindPat and
continuation binding, saved-frame Resume/Append input, and S's answer seam.
They are not repaired by adding a premise named `WellTypedRawUse`.

General patterns/annotations, declaration mismatch, false or effectful guards,
NoArm forwarding/re-entry, normal value matching, suspension and all foreign
frame/continuation alternatives keep their original obligations. Inspection
does not exclude any of them. The structural raw body is not an interpretation
for opaque FK1 handles; those retain their separate interface and quantifier.

Historical/current separation is pointwise: all Event and Elig_y references
remain at C_y,J_y. All actual owner/receiver activity and guard evaluation
use the state at the current step (initially C_out). Since ε consumes H,
`Active(H,C_out)=false` and hence `Inc_C_out(q,H,b,p)=false` for every b,p,
regardless of stored χ or Path. New receipts cannot reactivate an old boundary
receiver. The lookup of old metadata does not discharge any current grant.

Manual falsifiers, not executable probes:

- Replace B with A in the specimen: k id loses its Function-response entry;
  replace A with B: ApplyOne's actual Int answer is lost.
- Drop one δ payload D incidence: §4's inverse path map finds an unmatched
  original witness, so packet preservation fails even with equal scalar types.
- Carry `Active(H,C_y)` as current: ε makes the current incidence conjunct
  false. Metadata preservation deliberately offers no such cast.
- Let caller a change the answer: the answer of Append(k,a) differs from S's
  answer; declaring A from the final caller result violates §5's cut.
- Use a native opaque view as an empty source profile: unknown coverage gives
  no such derivation, and the raw descriptor proof is still absent.

These discriminate bad constructions. None is a source-qualified
counterexample to original A/B/F1/FK1.

## 7. Application to adopted MI-Intro and F1 P2

Fields 1–13 of the adopted telescope retain their original inputs and actual
exit outputs, as in the frozen exit candidate. Within this proposed extension,
§3 adds an actual metadata-read occurrence for field 7 and its dependent
fields. Section 4 constructs the payload occurrence part of prospective
field 14 from its independently declared operation argument schema. This is
an explicit candidate edge toward M_exit; it is neither a completed M_exit
nor evidence that the accepted source already generates that edge.

The raw component, all cross-component dependencies and the actual current
owner/guard environment of field 15 still require §6's proof. A_H's existing
order and binder interfaces are retained; a remains the original separate
field 17 and needs its actual dependent seam. Only after the complete field
14 and these owners are supplied can adopted MI-Intro conclude MatchEntry.

For P2 `I_Request → Select_0-H`, this gives a concrete proposed first source
instruction for the formerly unspecified metadata use. Its erasure reads
the same q/raw and begins the existing matcher outside H. For the variable
payload case, j_P can compose with the original provider-to-argument edge.
The existing θ_k may compose with a complete raw edge only after the latter
is proved. Consequently `(θ_k ∘ M_exit)_*` remains unavailable as a complete
construction. F1 gains a reviewable declaration and local candidate proof,
not a discharged branch. FK1, FIRST-RESULT-ADEQUACY, H1/H2, JOINT_DEC,
complete Call/effects, source-Generalize, soundness, principality, F5 and
production remain OPEN. No supported source behavior is removed.

## 8. Source/native evidence and implementation boundary

Static inspection used only the contract-pinned files. It confirms:

| Owner | Existing concrete evidence | Unfilled correspondence |
| --- | --- | --- |
| `Builder::catch`; `Work::CatchArms`; `Action::CatchOperation` | Original operation/arm/binder/source identities, original scrutinee endpoint/effect and level | No δ/ε or actual outside metadata-read typing certificate |
| `candidate_catch_operation` | Slots 60/61 pair payload argument ports; 62/63 connect k's Function using op result for response and original scrutinee endpoint for answer; 64/65 accumulate entry/full-scrutinee effects | Complete Δ_q, S answer evidence, owner actions and source occurrence maps are not supplied by these constraints |
| `machine::propagate_request` | Reads request declaration/payload while CatchReturn remains installed, later pops and binds | Its pre-pop read is not §3's outside inspection; a phase correspondence proof is still needed |
| `machine::bind` | Stores the same ReceivedValue and extends the lexical environment | Complete typed-view/Receive relation at the source binder is absent |
| `capture_template`; `ResumeTemplate` | Saved nodes, declaration and original_event retained | No full source R_S or all-response descriptor proof |
| `ResumeArgument`; `ResumeReturn` | Checks operation result on entry; returns actual suffix result | Distinct B and A consumers, not complete admission/output-future typing |
| `receiving::opaque` | Runtime continuation view has unknown coverage | Not an empty χ, source identity map or typed raw-view certificate |
| `candidate_function_port_admit`; `candidate_context_execute_relation` | Transport/consume previously formed relations and observations | They cannot introduce the missing matcher source declaration |

The inherited Function-response pre-pop refusal remains a limitation; it was
not executed again. The exact 138-byte specimen's prior partial-HIR errors
remain `UnsupportedItem 0..44` and `UnsupportedExpression 75..138`. No post-pop
Function-response binding, full acceptance or source execution is claimed.

**NO_SAFE_CODE_SLICE:** candidate_catch_operation and the runtime
capture/binding/response consumers both depend on unadopted declarations and
unproved complete correspondence. The permitted next native work is Luna's
static, unapplied instantiation after freeze/review, not guard removal or
production edits. Ordinary Simple-sub generation, accumulation, propagation,
levels, extrusion, qualifying intrusion and generalization remain intact.
No residual/provider/witness lineages are collapsed or withdrawn bypasses
restored.

## 9. Reuse, mutual TODOs and freeze

Reused within their premises: the historical/current split and retention
equations of `/root/catch_request_exit_introduction`; the exact missing
declaration and B/A discriminator of `/root/catch_matcher_operand_use_introduction`;
Luna's adopted matcher telescope and source/runtime instance; the conditional
saved ApplyOne/θ_k construction of `/root/source_matched_catch_actions`;
P2 Resume/Append of `/root/runtime_source_supplier_proof`; typed-boundary and
typed-source-owner rules by the primary with the scoped inputs recorded in
their headers. No historical author or conditional result becomes an
independent reviewer of this proposal.

Rejected reuse: historical Var as actual outside inspection; IF-Use as primitive
typing; target paths equal by naming; erasure as complete source adequacy;
scalar Function constraints as R_S; pre-pop runtime reads as μ_H; opaque
coverage as empty protection; B as A; structural raw as every FK1 handle.

| Stable request | Owner / first missing evidence / required input and output | Exact falsifier |
| --- | --- | --- |
| CATCH-TARGET-ADOPT-1 | Luna routes fresh independent review and adoption of §§2–5, with the frozen contract and adopted telescope. Output: explicit acceptance/rejection of each declaration, separate from proof closure. | Treating this Draft as adopted semantics or claiming complete M_exit from metadata typing. |
| CATCH-RAW-ANSWER-1 | Original Request/capture/suffix source owner: from δ's declared S and Δ_q, supply the actual answer-cut declaration and preservation for every originally admitted τ, including OriginalFrame bodies and lawful current actions. Output: the missing raw typing derivation, not a narrower response set. | A derived from B, caller a substituted for S, descriptor validity assumed, historical world cast to current, or foreign case silently excluded. |
| CATCH-TARGET-OWNER-1 | Original MatchRequest_H/BindPat/continuation-binding owner: instantiate actual outside u/slots, arm projections and dependent source maps; input ε and original A_H. Output: real use/Receive actions and missing cases for field 14/15. | Taking u=owner(H) or j=Id without the actual source binding/descriptor; carrying consumed-H activity. |
| CATCH-TARGET-NATIVE-1 | Luna's already leased conditional static lane: instantiate §§3–5 on P=Unit, B=Int→Int, A=Int with actual source binder/operand equations and missing native fields. | Claimed post-pop Function branch, pointer equality as full typing, ignored partial-HIR errors, or new implementation writes. |

A later minimal provisional implementation TODO, only if newly authorized,
is to retain an already justified source declaration identity plus separate
B-entry/S-answer incidence at `Action::CatchOperation → candidate_catch_operation`
and identify its exact binding/resume consumer. First falsifier: the producer
has only scalar endpoints or a synthesized identifier and no original typed
S/Δ_q certificate. In that case report absence rather than inventing the
certificate. This is a request for a future lease and proof-supported slice,
not implementation authority in this assignment.

Eight substantive stages: frozen authority/pins; metadata declaration and
operational introduction; payload port/binding maps; raw B/A telescope and
body; preservation attempt; discriminators and parent application; native
owner correspondence; freeze/handoff. Cap 720 seconds. First recorded clock
2026-10-17 05:28:21 UTC; final clock and conservative charge are in the handoff.
Only source reads, manual derivation and SHA-256 verification were performed.
No tests, builds, probes, runtime, Git, network, descendants or scratch paths.
Effective runtime model/effort and CPU/peak memory remain UNKNOWN.

All 22 pinned inputs matched at entry and are checked again at freeze. The
contract SHA binds their exact paths/hashes; the manifest follows. The only
new paths are this artifact and
`tasks/agent-loop/inbox/20261017-catch-matcher-target-declaration-proposal.md`.
Both freeze at revision 1; no further writes after the handoff's STOP receipt.
Fresh review, semantic adoption and Luna intake remain pending. No worker
continues in the background.

## 10. Frozen dependency manifest

```text
51e6990ad8499fc93fd8d3b5ff718d4b10d990068aa9ec9994a7b8266fa557ba notes/design/2026-10-17-catch-matcher-operand-use-introduction.md
a874e1288003fa83fe9321c1d92a1e865267aedf3db79cd5e7410644c61ea5e2 tasks/agent-loop/inbox/20261017-catch-matcher-operand-use-introduction.md
b0881f12db88442cc0cdbc0f13c08671ec1f083e78f21898bca09575f0be700f notes/design/2026-10-17-catch-request-exit-introduction-proposal.md
edce02b4c4736d5f59f59ba31071a5aa9cb7e31b526fc6834f9e4043982164e4 tasks/agent-loop/inbox/20261017-catch-request-exit-introduction-proposal.md
5b7177e3f185c6c777dd2b0794c1f30fe17815c7ac99ee03dbb1d5f82a91376f notes/theory/2026-10-17-catch-exit-source-runtime-instance.md
cd99aa19cfd301d0ad9f2396c6ef810fc0244f3f08e877ac3f8ce92dd307ba24 notes/design/2026-10-17-catch-matcher-input-formation-proposal.md
ea0b96693114f9cbe9c8e6306b4dcff6fd522baef2c9076277de1a33801a2936 notes/theory/2026-10-17-catch-matcher-input-constructor.md
414cafbe5bbe1b940ffa96fb6f6a9c0b3a3bef5fd3a1aec0dfec3aa5be41329e notes/theory/2026-10-17-catch-exit-typed-incidence.md
d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa notes/design/2026-10-17-source-formation-proposals-adoption.md
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa notes/design/2026-10-02-typed-source-owner-realization.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb notes/design/2026-10-02-typed-boundary-realization-draft.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
064e813a0bcf82019d9379dfa25fd1c825eabd2072c5933f32b28d6d1ea284ae notes/theory/2026-10-17-source-matched-catch-actions.md
3a0bf3df4657dd0a6ccbb8690d990177ff19f30e10e91c93839b4601c634f61b notes/theory/2026-10-16-parameterized-shallow-image-finite-presentation.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5 crates/yu-hir/src/module/local_source.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38 crates/yu-solver/src/candidate_source.rs
11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb crates/yu-solver/src/candidate_effect.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6 crates/yu-solver/src/candidate_context.rs
b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82 tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
```
