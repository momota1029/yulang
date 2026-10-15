# Root computation-formal permission: construction and paired consumer

Date: 2026-10-15
Status: independently reviewed research-only static source rule and conditional
residual preservation argument; native suppression remains on HOLD pending the
actual owner/path/instance correspondence.
Compiler baseline N: `af3ed318b4c022e6baa211134ef89d0f3810eecb`.
Authority/research snapshot A: `6baadfc315c9a96cf7e3236954c603f86335bb59`.
Lease: this new note only. Original source/runtime hygiene parent remains OPEN.

## 1. Fixed claim and source instance

The user confirms that effect-taking arguments may be treated as delayed.
[Annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,1.1 already selects the substantive rule: a contravariant concrete root
annotation grants function-local handling permission; it neither caps incoming
effects nor handles without an actual Catch. Existing typed transport/lifetime,
complete Call, original binders/providers and one `xi=(nu,K,D)` remain binding.
[Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–3 require construction before solving and proof-supported implementation.

Use the reviewed concrete source instance in
[receiver-relative exit](2026-10-15-receiver-relative-protection-exit.md) §7:

```yu
act io:
    our tick: int -> ()
act other:
    our tick: int -> ()
my bridge (thunk:[io] int) = thunk
my answer:[io, other] int = bridge {
    my first = io::tick 1;
    my second = other::tick 1;
    1
}
```

This checked-in successful constructor control was not rerun here. Fix original
Lambda L, formal t, annotation a, outer row position s, and resolved family I=io.
Let k=(original definition/local callable, L, t) denote the source receiving
binder, not an invocation address or an effect-row number. In this instance
L is the single original formal Lambda; no multiargument-frame selection is
inferred. Native e_t is the authentic registration's entry-effect row, v_t its
original parameter Value row. The input's additional other family remains J.

**Required static conclusion:** construct the local permission and its root
typed path from these actual source operands, then preserve their association
through the authentic formal Name and receiving Function ports. No profile,
receipt, event or successful pending comparison is an introduction premise.
The full parent still quantifies over omitted/inferred callbacks, every supported
source path, latent values and resumptions, soundness and natural inference.
This exact annotated rule does not close those obligations.

## 2. Syntax-directed introduction, with no supplied permission premise

N `yu-hir/src/module/source_annotation.rs:68–95,524–576` supplies a.owner,
a.position, s=row.position, the resolved SourceEffectId vector and symbolic
variables. SourceEffectId is module/declaration identity, not spelling.
The formal registration supplies original t/L, Computation role and e_t
(`candidate_source.rs:566–578,699–715,1192–1198`). All operands already exist
at `candidate_formal_entry_annotation:1170–1182`.

Write the constructed **judgment**, without selecting a Rust representation:

```text
OwnsParameter(k,L,t,a)       a.ty = [I] Int at its original outer row s
Role(t)=Computation         EntryEffect(t)=e_t
---------------------------------------------------------------- RootPermit
SourcePermit(k,t,a.position,s,RootComp,e_t,I; xi)
```

RootComp is the root computation position of the original parameter carrier.
It is not a nested callback result or every descendant position. The annotation
is contravariant because it is on the received parameter computation; its
Value part remains Int. This is a direct specialization of the selected
annotation policy, not a rule inferred from row equality or inferred support.
It creates no effect contribution, inclusion into a closed {I} cap, scope release,
Force, concrete request, handler selection or dynamic Receive.

The source role rule simultaneously gives `Gamma(t)=Computation(E_t,Int)`.
Entry binds the whole delayed carrier. The body Name/result consumer can
execute it; there is no Value-entry Force. E_t stays an open ordinary effect
endpoint, so J can reach it. A source row variable, if present in an extension,
would retain its original constraint connection and supply no concrete permit;
this note proves only the displayed root [I] Int case.

**Construction proof.** OwnsParameter is established by the original retained
Lambda/parameter/annotation association, not a later matching name. HIR's
parse_row resolves I from the effect namespace and retains s. The source role
rule selects Computation from that outer annotation. Its negative parameter
position and concrete I instantiate annotation integration §1, giving the
receiver-local licence for exactly I at RootComp. Thus the conclusion follows
from source syntax/ownership already known before body use and solving. No
Γ profile is assumed. In particular, replacing I by J changes this conclusion
even when scalar Value/AE/RE constraints are isomorphic.

The tuple-like judgment is a proposed source-construction output. An immutable
record, an existing qualified context, or another representation may implement
it only after independent approval of its constructor/consumer seam. This note
does not silently adopt a new interpreter or claim the current compiler emits
it. It closes the finite *licence introduction* premise at the source level;
it does not manufacture source execution from static rows.

## 3. Actual Name and Function-port preservation

For original Name occurrence n resolved to Parameter(t), construct its typed
carrier-use correspondence from that resolution:

```text
Resolve(n)=Parameter(t)       SourcePermit(k,t,a,s,RootComp,e_t,I;xi)
---------------------------------------------------------------- NamePermit
UsePermit(n,k,a,s,RootComp -> n.computation,I;xi)
```

This is the identity computation-carrier correspondence of the source binding,
not permission for every endpoint equal to e_t. N emits the matching static
carrier linkage at `candidate_source.rs:914–921,1304–1307` through
FormalNameEffect and the two original Name slot-1/2 inequalities e_n=e_t.
Those edges must carry the same n/t/registration association as NamePermit.
Their opposite inequality directions do not create a second independent
licence or permit transfer to an unrelated formal with an equal row.

N's positive Lambda/demand pair retains the original endpoints:

```text
F_L = Function4(Int-, e_t-, e_ret+, v_t+)
U_C = Function4(v_arg+, e_arg+, e_call-, v_result-)

v_arg+ <= Int-          e_arg+ <= e_t-
e_ret+ <= e_call-       v_t+ <= v_result-
Int+ <= v_t            v_t <= Int-
e_n = e_t              e_n <= e_ret   (body thunk, no Catch)
```

Owners: `lib.rs:11271–11335`, `shadow_apply.rs:1541–1620`, and actual Function
port dependencies in `candidate_context.rs:3000–3065`. Source receiving AE
connects the whole argument's contribution to RootComp. The Name/body/RE
route transports its effects to the Call result under the same assignment.
It does **not** export an unconditional local licence to the caller merely
because an effect reaches e_ret. Licence scope remains k. Without Catch the
rule introduces no residual transform, so both I and J still reach the output.

**Local preservation proof.** Resolve(n)=t supplies exactly one original
binding path; composing it with the authentic receiving ArgumentEffect child
and the body-to-result correspondence keeps k,t,a,s and the same contribution
antecedent. SourcePermit adds no constraints to E_t, so these scalar inclusions
are unchanged. Permission is a property of that qualified source use, not an
operation on e_t: a sibling ordinary use remains unfiltered. A canonical
row equality cannot replace k/t/a or join another source's permit. Hence
I's local licence survives Name/AE transport, J receives no licence from it,
and ordinary forwarding preserves all contribution coordinates.

For annotated t the current `FormalConstruction` path is insufficient:
`lib.rs` creates that record only from omitted_formals. The actual
recipe.formal_registration and registration.entry_effect are present; the
coupled constructor must retain F_L's authentic AE-to-registration connection
for annotated formals directly. This is an actual implementation owner gap,
not a need for a complete new receiver interpreter.

## 4. Paired Catch consumer and conservative residual theorem

Extend the example's body to the selected `catch thunk` control only through
its genuine source typing/arm constructors. NamePermit supplies the static
source permission for the scrutinee use. A consuming Catch must additionally
establish that its actual handler owner is this same receiving binder instance
k and that q is exposed through this exact carrier-use computation position.
The existing [typed-boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6 theorem then supplies local eligibility from explicit I and the genuine
current receipt/observation; these are execution obligations, not rows.
An inherited protection is retained as evidence and cannot veto a valid
receiver-local explicit grant. A nested helper's different owner cannot use
k's licence merely because its code is lexically beneath L.

For a static residual operator on the **scrutinee-to-Catch-output route only**,
the following is a sufficient preservation condition. For each represented
contribution x suppressed there, establish:

1. Its complete possible operation-instance set Ops(x) is covered by I and
   by guaranteed selected-handler matching arms at this qualified local use.
2. Payload coverage is total for those instances: irrefutable payload patterns
   with no guard suffice. Partial literals, unknown guards or unknown operation
   coverage do not justify suppression. Original arm typing/OpCompat is retained.
3. Earlier arms cannot leave a covered event unmatched. If they may select,
   their ordinary effects are included; any match/guard effects are included
   outside the handler. No optimistic run-time pattern result is assumed.
4. Raw continuation/resumption effects retain the **unfiltered original**
   scrutinee interface E_S. Every operation/value-arm effect reaches output by
   its ordinary route, without this residual filter being applied again.
5. Unknown owner/path/instance correspondence means forward conservatively;
   it is not a new source rejection or a licence to omit a required path.

The initial bounded consumer can use the stricter case: the scrutinee is the
direct original Computation-formal Name; the Catch belongs to that same
original Lambda and qualified receiving instance; matched payloads are
binder/wildcard or Unit justified by the operation's declared payload type;
and the continuation is discarded. Discard means wildcard or an actual binder
with no resolved references, not a spelling test. HIR's empty-call payload
syntax alone is not Unit coverage (`local_source.rs:243–246`). All arm/value
effects and original raw-continuation E_S edges remain ordinary, including
unselected source arms. This sufficient precision gate does not reject source.
Use the **first source-ordered arm for that exact operation**, with guaranteed
payload coverage and discarded continuation. A later discard arm cannot
authorize omission when an earlier matching arm resumes. Unknown/partial
earlier matching cases conservatively forward. This strict gate satisfies
conditions 1–4 without an arm-selection search or inferred runtime match.

**Proof of the residual bound.** Take any emitted event at the Catch's outer
boundary in a typed source execution. If it is a scrutinee event not selected
by this handler, condition 1/2/3 prevents its operand from being suppressed;
the residual scrutinee route retains it. If an event is selected, the selected
event itself is consumed, while all new arm/selector events use the ordinary
arm/outside routes. If an arm resumes raw k, shallow selection does not reinstall
this handler: the continuation's original E_S covers escaping suffix events,
and condition 4 carries them through the unfiltered arm route. A value arm's
events use its ordinary route. These cases exhaust the source handler image.
Thus no outer event is lost; retained operand witnesses/providers and K,D
remain attached. Unknown operands are retained, so the claim is conservative
preservation, not exact support subtraction or a principal-effect theorem.

Multiple operations in one family matter: an arm for I::tick cannot erase a
family-level operand also representing I::tock. Either retain that operand,
or prove coverage for every operation it represents. Payload-partial tick
also remains. Current Contribution stores family/origin/instance without an
operation field (`candidate_effect.rs:140–144`); it cannot simply be read as
one operation. An Annotation-origin member is likewise family-level.

ViewOrigin::Operation alone is not exact-operation evidence: nested annotation
effects also inherit that provenance. An exact injected-operation member must
be authenticated at the **outer** signature RE insertion
(`candidate_effect.rs:1538–1552,1573–1580`, where family is supplied only for
the top operation signature). Otherwise use conservative family coverage.
This is a concrete additional constructor/consumer correspondence requirement.

**Bounded exact-operation classifier, derived from current constructors.**
For member x=(view,m), require all of:

```text
view.provenance = Operation(origin with declaration d)
m=0; view.position=d.signature_position
view.allowed=[d.id.family]
d.signature.value = Function{result,...}; result.effects=None
```

Then x denotes the outer injected request family of the exact operation d.id.
Proof: at `candidate_signature_value:1538–1552`, family is Some only for the
actual top declaration-signature pointer. The row=None/family=Some branch at
1573–1580 creates exactly this singleton view at context.position, which for
an operation is signature_position. The row=None/no-family branches create
no such member. An explicit row branch uses that row's original position;
it cannot pass this test as the root signature node. SourceNodeKey is exact
parse/green/start identity (`yu-syntax/full_parse.rs:68–92`), and the admitted
nonrecovered signature and nested row are distinct source nodes. There is no
second family member in this constructor branch. Copying the view preserves
its declaration, position and allowed vector (`candidate_effect.rs:890–909`).

Explicit result rows, generic Contribution operands and unknown provenance
therefore forward under this bounded classifier. In particular an own-family
item explicitly written in an RE row must not be confused with the injected
request: the current vector may contain both, and any future dedup/composite
representation must retain distinct roles or forward the ambiguous member.
The classifier proves exact operation identity, not payload match or local
permission; the paired Name/owner/coverage checks remain mandatory.

N's current Catch slot-51 scrutinee inclusion is unconditional
(`candidate_source.rs:840–857`); arm slot-51 inclusions are separate. Only the
first route is a residual candidate. `candidate_catch_operation:820–875`
already includes original E_S in the continuation's returned effects at slot
65; filtering that continuation input too would invalidate the proof above.
Existing Allowance/LocalWeight checks are admission mechanisms, not this
residual operator. Its representation and integrated implementation remain
proposals requiring review; no such consumer is claimed implemented here.

## 5. Fresh uses, owner scope and the minimal enforcement invariant

For each qualified RootPermit/NamePermit edge the implementation must retain
one correlated record of original k/t/a/s, RootComp, resolved I, entry endpoint,
actual Name/source route, and the corresponding positive Lambda AE/native
comparison. It must not choose a separate matching formal or provider by row.
At a consuming Catch add its own source occurrence, exact scrutinee route,
local-owner qualification and operation/pattern coverage evidence. This is the
minimal **paired** obligation: a valid producer with a row-wide consumer, or
a local consumer fed an unrelated annotation, is insufficient.

Source substitution preserves these judgments by substitution of their same
endpoint/typed-path variables; resolved I and original annotation provenance
remain unchanged. For a fresh inferred use, map entry/value/effect endpoints
and all local scope references through the one actual FreshUse map, and retain
the same original declaration/annotation and that use's joint antecedent.
Different fresh uses cannot exchange local-owner witnesses. Genuine old
external protections retain their original identity and are never included
in a new permit's destructive update, because introduction performs none.
Apply the [ownership/capture theorem](2026-10-15-effect-scope-ownership-capture.md)
only after its complete latent inventory/shared-map premises are established.

N `candidate_scheme.rs:140–149,1057+,1268,1331` retains actual context_use and
shared scope/context maps. This does not yet prove that the new permission
output is captured, restored and replayed through them. A producer/consumer
slice must cover each such reference and invalidated/resumed route or retain
the existing conservative inclusion. Row canonicalization must preserve the
qualified annotation identity independently of canonical endpoint equality.

Static k is a receiver binder, not proof that a saved receiver is currently
live. Re-entered raw code can have a different execution owner while retaining
old typed bindings. The reviewed [source-owner theorem](../design/2026-10-02-typed-source-owner-realization.md)
§§3–4 forbids rebinding old boundary evidence to that owner. Runtime/native
eligibility still needs the actual same-instance owner/receipt/Observe bridge;
no `context_use` or Lambda ID alone proves it. Escaped values, recursive
activations and full source/runtime closure therefore remain OPEN.

## 6. Handoff, checks and freeze

Constructive result: RootPermit now derives this finite annotation licence
from its original source operands, rather than assuming an arbitrary profile.
NamePermit and the authentic AE/RE trace identify its qualified use and prevent
row-global authority. The residual argument gives explicit sufficient consumer
conditions, including multioperation families, payload coverage and shallow
resumption. It does not establish those conditions for every current native
path, introduce a concrete new runtime model or certify source soundness.

Next actual owner: establish the actual owner/path/instance correspondence
needed by §4, then couple FormalEntry's source-owned output to the annotated
Lambda AE and actual FormalNameEffect route. A same-Lambda/direct-Name check
alone does not discharge that premise. A bounded reversible constructor probe
may collect evidence; semantic residual suppression and production adoption
remain on HOLD until the correspondence is established and independently
reviewed. Current unconditional Catch forwarding is unchanged.

Checks: source reads and constructor substitution, no builds/tests/execution,
network, child delegation or Git mutations. One <=20-minute prover leaf;
requested Sol/high, effective runtime model/effort unknown. Dependencies are
pinned by SHA-256 below. Only this leased note changed. Shared task/index/theory
records remain primary-owned.

```text
N yu-hir/module/source_annotation.rs f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38
N yu-hir/module/local_source.rs 96a77474b9e63eecaf3b5be926e82af9a88d531b40fd758f6009b33ba87c4f44
N yu-syntax/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
N yu-solver/candidate_effect.rs deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225
N yu-solver/candidate_source.rs 90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab
N yu-solver/candidate_call.rs 359566bccaa150cbe001c060475cce3d0a3e35a37a9e45d118c0f485df2e88cf
N yu-solver/candidate_context.rs 9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083
N yu-solver/candidate_scheme.rs 436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6
N yu-solver/shadow_apply.rs 28112e3a8b04bff3abbed0bf7496a4e49300384e7e943ee8a71f4eff3a100294
N yu-solver/lib.rs b0f7778934a37ec9c642f7e6232cb61e37a1b0768f6af92556cf873f6b2a69f7
A annotation-effect-hygiene-integration.md 4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4
A typed-boundary-realization-draft.md 1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb
A typed-source-owner-realization.md 5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa
A receiver-relative-protection-exit.md fc23ca3ddee2f8bd49f8fb402fa93865406a17f3c3aa8f99cb5d77a7c31e5691
A effect-scope-ownership-capture.md 44d69d6506f14c1658d7670ef68c46348d1315ce98ff1d2677f68993c5e00ea6
```

Independent compiler-referee review of producer SHA-256
`c4e9028e14e332cf4f61bdeef48962287f136a2f1da120da1538b1aa6ad69dfa`
found no blocking or major defect in the conditional argument. It confirmed
the exact-operation classifier and separate arm/raw-continuation routes, while
explicitly withholding the dynamic correspondence from static Lambda/Name
identity. Primary verification matched all 15 dependency hashes. These status
updates do not strengthen the theorem. Original parent OPEN; source-licence
construction remains separate from pending native transport, operation coverage,
owner/receipt and residual-consumer enforcement.
