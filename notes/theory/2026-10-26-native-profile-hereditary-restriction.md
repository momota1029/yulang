# Native profile construction commutes with hereditary restriction

Date: 2026-10-26. Status: independently accepted; see the [review receipt](../../tasks/agent-loop/inbox/20261026-inference-profile-restriction-review.md).
Assignment: INFERENCE-PROFILE-RESTRICTION-20261026/r1.
Baseline supplied by the primary: `eb3eef2f6a29d9c2a6132d648866c60900db276c`.
Author: `/root/profile_transport`, generic bounded constructive-proof leaf.
No compiler, semantic-rule, source-domain, production or parent-status change.

## 1. Result and exact governing constructors

**NPR** proves that the existing PF1/PF2 native profile construction commutes
with an independently lawful hereditary restriction, on every actual finite
native license derivation. It constructs the composite action from the
original field injections and the original independent leaf actions. A
generated profile-commutation law is not an input. **VB-NP** applies the result
to the actual fresh `ValueBind` of VB1 and the immutable `Name h` / `Name x`
Call of HC1/GC3. It removes the separate generated-native-profile transport
premise at that binding, lookup, and later compatible use.

The parent remains the full original
`YulangClosure.SourceProblem.InferenceSoundness`. This result is a source
construction component, not an instance of that proposition and not a proof
that native compiler success supplies a complete original solution.

The following are the actual source inputs, with their selection/status
boundaries checked before construction:

| Source | Use and status |
| --- | --- |
| [Native signature definition](../design/2026-10-08-native-signature-formation-definition.md), §§1–4 | Authoritative selection of the native grammar, origin/receiver separation, complete licensed projections and local no-annotation policy. |
| [Signature incidence construction](2026-10-08-source-signature-incidence-construction.md), §§2–8 | Adopted `PortProv`, `DeclContribution`, `L`, actual record injections, whole certificates, licensed-field selectors and their source maps. The opening adoption notice governs the historical candidate wording. |
| [Source-interface definition](../design/2026-10-08-call-source-interface-definition.md), §§2–4, and [IF construction](2026-10-08-call-source-interface-construction.md), §§3–6 | Authoritative insertion/use/source constructors and reviewed IF supplier, retaining full dependent interfaces. |
| [Native local profile construction](2026-10-24-native-local-profile-construction.md), §§2–5 | Independently accepted PF1/PF2 on selected native licensed projections and their stated independent inputs. Defines the existing `NP` used here. |
| [Contextual Function definition](../design/2026-10-08-contextual-function-membership-definition.md), §§2–3, and [semantic input realization](2026-10-08-call-semantic-input-realization.md), §§2–4 | Selected hereditary immutable membership, lawful compatible extension, original binding/capture/rebind constructors and W/D. |
| [Fresh ValueBind](2026-10-24-fresh-valuebind-complete-call.md), §§2–4 | Reviewed VB1/HC1/HC2; actual typed Return, fresh dynamic binding and same-provider Call. |
| [Generated Call descriptor typing](2026-10-24-generated-call-descriptor-typing.md), §§2–5 | Reviewed GC1–GC4; concrete whole field maps, origin partition, source local law and independent arm composition. |
| [Complete Call definition](../design/2026-10-07-complete-call-contribution-definition.md), §§2–5 | Authoritative complete-operation, exact upper objects, independent C0/SpecCall and all actual alternatives. |
| [Pure-read result definition](../design/2026-10-08-pure-read-call-result-constructor.md), §§3–5 | Authoritative selected `ReadInvoke` result, with the source relation kept independent. |
| [Original generated Call relation](../progress/2026-10-06-source-call-generation-construction.md), §5 | Original `G_call` conjunction and its one shared existential witness. An original full solution already supplies `TypedCallCert_Dec`. |

The current Lean repository has no datatype declaration of these native
`L`/`DeclContribution`/`NP` judgments. The companion
[NativeProfileRestriction.lean](lean/YulangClosure/NativeProfileRestriction.lean)
therefore checks the concrete dependent-record equations used below; it does
not invent a replacement native grammar. The original-constructor induction
is the paper theorem in §§3–6. The source/type/axiom verification receipt and
exact input hashes are in the assigned handoff.

## 2. Statement, indices, and genuine independent inputs

Fix the original finite registered source/complete-contract graph, original
binder tree and resolved source occurrences. Retain the original joint index
`I=(B,G,Delta,X,xi)`, `xi=(nu,K,D)`, complete origin partition `Omega`, receiver
`beta_r`, original typed slot/position, and all constituent dependencies.
An event and its current configuration are those of the independently admitted
history; the current configuration is not a snapshot frozen into the original
assignment. Let `sigma:e -> e'` be one **actual independently compatible**
extension of the original history. This does not assert that every store
change, world substitution, or static renaming is compatible.

An actual field key remains precisely PF1's

```text
k = (ell, constituent, field, w),
ell : L(I;Omega,beta_r,s,p,c),
w : the original governed-license/field witness for this projection.
```

The key is not merely a supported slot or an endpoint. The static derivation
and source identities are retained. Write `sigma_*ell` and `sigma_*k` for
their original whole hereditary action: static coordinates are retained and
the actual dependent semantic/evidence coordinates use the original action.
This notation does not add an event-indexed constructor to `L`. If a static
license field is independent of events, its action is identity. A current
event-dependent field uses its own original action, not identity by fiat.

Let `p` name the actual independent packets in the chosen finite derivation:
primitive/external/inherited packets, annotation evidence when present,
genuine primitive and independent-arm licenses, and independent complete
operator evidence where the original rule requires it. Each is the whole
original packet, with its provider, scope, guard, field correspondence and
lawful hereditary action. These are exactly the semantic leaves already
required by the native rules, PF1/PF2 and W. No source default supplies one.
For each genuinely local unannotated field, its source declaration already
selects `FullProtection` and `NoConcreteRemovalGrant`. Their original
introducing field and real license `w` remain in the packet.

**Theorem NPR (pointwise native profile naturality).** For each such actual
finite `L` derivation, each actual governed field key `k`, every independently
compatible `sigma`, and the original leaf packets `p`,

```text
NP with sigma-restricted original leaves
   (sigma_*ell)[sigma_*k]
 =
restrict_sigma (NP with original leaves (ell)[k]).             (NPR)
```

Both sides use the same transported dependent tuple, actual branch tags,
original introducing fields, source routes and witnesses. Equality is the
native constructed-record equality after the original dependent reindexing.
It is not an equality between independently chosen proof records, an
extensional equivalence of foreign profile predicates, or a quotient by
equal effect endpoints. If a leaf's action has its own lawful dependent
record equality, use that exact equality on both sides. The construction
adds no proof irrelevance or injectivity assumption for that leaf action.

The statement is forward, at transported actual keys. It neither says every
target key has a predecessor nor supplies a new license in an empty fiber.
It also does not require finite enumeration of an opaque primitive's witnesses
or future histories: induction is on a given finite derivation, and the field
and history quantifiers remain universal.

## 3. The record calculations that generate the composite action

Take `t` to be the **entire** original dependent tuple, with all its parameter,
carrier, provider, role/entry, current-world, response/raw-handle, result/future,
guard, license and scope evidence. For an actual contextual occurrence `a`,
GC1 and native §3.2 define its insertion as `tag_a(t)=(a,t)`. Hence

```text
restriction(tag_a(t)) = tag_a(restriction(t)),
projection_a(tag_a(t)) = t.
```

The source occurrence is unchanged by a hereditary event extension. When a
separate lawful source freshening acts, its original image of `a` occurs on
both sides. This is the actual tuple injection, not an axiom about arbitrary
maps. The companion's `tagged_restriction`, `tagged_projection`,
`restrictPacket_mk` and `restrictPacket_comp` check these equations for
arbitrary whole dependent packets and actual chosen field actions.

For the original shared Pair and dependent Bind records the calculations are

```text
restriction(t,p1,p2)
  = (restriction(t), restriction_t(p1), restriction_t(p2));

restriction(t,b,p_b)
  = (restriction(t), restriction_t(b),
                    restriction_(t,b)(p_b)).
```

The first equation restricts one `t`, not two witnesses selected for the two
components. In the second, the final field is indexed by that same restricted
middle witness. The Lean `sharedPair_restriction`, `sharedFields_restriction`
and `dependentBind_restriction` check these full dependent equations. Choosing
`t=(v,r,C')` in the latter is the actual result-to-rebind map; choosing the
hidden whole row for `b` is the actual single-package hiding map. The formal
calculation does not construct the returned tuple or the hiding admission.

For a local policy, the existing construction is

```text
(original licensed field packet, FullProtection, NoConcreteRemovalGrant).
```

Restriction applies to the original packet and preserves these source policy
values at their original field. Thus local construction after restriction
and restriction after local construction are the identical record.
`appendLocal_restriction` checks this, with the actual static policy pair as
its `defaultPolicy` parameter; `appendLocal_original` shows the original packet
is recovered unchanged. This parameter represents the selected source policy,
not arbitrary event authority. The original `w` is an input on both sides.

Finally the actual original origin/field correspondence partitions inherited
and genuinely local fields. Assembly is case analysis on that retained
partition. Its inherited case returns the child's same packet; its local
case appends only the selected local policy. Fieldwise restriction distributes
over that case analysis (`assembleFields_restriction`). Equal owner/receiver
identifiers do not change which case the actual constructor supplied. The
selector comes from `DeclContribution`/`PortProv`, not an assumed global
classification or a new equality test.

These calculations require actions on **independent original operands**. They
do not assume an action preserving `NP` on a completed composite derivation.
The latter is constructed by the induction below.

## 4. Inner induction on the original DeclContribution derivation

Use the exact §3.4 constructors of the adopted native grammar. Simultaneously
retain the `PortProv` field diagram and the actual licensed-field selector.
For each constructor, inspect the actual field that the key selects. The
following list includes all native declaration forms and the relevant actual
source instances of the operator form.

### 4.1 Genuine primitive, external, and inherited leaves

At `PrimLicenseContribution(alpha,h,...)`, NP returns its supplied whole
profile/license packet. On the left of NPR the leaf is the original restricted
packet; on the right it is that same original action applied to the same
packet. The records agree, including `PrimOrigin(intro_alpha,h)` and the real
governed witness. A primitive's opaque meaning, admission, non-source arm,
provider change or live permission is not proved here. Such data is retained
exactly where the original primitive requires it.

An independently inherited child boundary certificate is treated the same
way. This is an actual PF1 leaf, not a license or completed recursive
membership inferred from a registered root. Its retained hereditary action
already quantifies over compatible future uses. If the leaf lacks that
action or an independent license, it is not an input to the theorem.

### 4.2 Genuinely local unannotated introduction

The actual introduction and governed-field selector place the key in `Own_n`.
The license witness is already the genuine original `w`. Both sides of NPR
retain its restricted original packet and append the same selected policy at
`n`'s same field. Section 3 proves equality directly. No policy is placed on
an unrelated inherited projection, even if its owner label equals the receiver.
An annotated local field uses its actual annotation rule and independent
packet, not this no-annotation case.

### 4.3 Operand

The constructor stores `Operand(j,Omega_j,rho_j)` and the actual operand
injection. Apply the induction hypothesis to the selected antecedent field,
then `tagged_restriction` to the injection. The entire original packet is
preserved. The route gains the same operand occurrence on both sides and
receiving attribution stays inherited; it does not gain a fresh default.
The complete child schema remains present, including unreached fields.

### 4.4 Ref, Scope, and Rename

`Ref(v,m,...)` stores the actual registered antecedent and its original scoped
substitution. Apply that substitution to the whole tuple once and retain the
same use occurrence. Every dependent field uses the original instantiated
leaf action at that substitution. Projection of the record gives the same
substituted field on either path; then apply the induction hypothesis and the
tag/route-composition equations of §3. No equation between two arbitrary
substitutions is being assumed. The source's lawful instantiation of the
original hereditary packet is the independent input.

Scope retains the entire package under its original binder. Compute the
induction hypothesis there; no hidden witness is moved outside that binder.
Rename applies the same original lawful renaming to all field indices and
their evidence, then uses this same calculation. Neither case introduces an
owner, policy seed, permission, or new license. A registered cycle is a
reference to its stored interface. The induction descends through the actual
finite proof development, not an infinite unfolding of the graph.

### 4.5 Union / Alt

For `Alt(left,d1)` or `Alt(right,d2)`, the licensed key retains its actual
branch tag. Use the induction hypothesis for that child and the unchanged
tag equation (`restrictAlternative_left/right`). Both complete branch schemas
remain in the interface, but an unselected or empty schema acquires no witness.
No proof from the other branch is requested or synthesized. An independent Z
branch remains independent and is not made to pass through source execution.

### 4.6 Conjunction / Pair

The input is `Pair(d1,d2,shared)` at the one original dependent tuple.
Apply the two induction hypotheses at this same tuple and use the first
shared-record equation in §3. Each licensed projection keeps its original
origin and witness. The retained shared equation is transported together
with those fields; it is not an identification of the two origins. The
construction never pairs separate existential worlds.

### 4.7 Op and its actual license fields

The actual constructor is

```text
Op(q,k,intro_n,typing_q,operand_interfaces,original_license_fields).
```

Its complete partition is the tagged dependent union of all original operand
partitions and precisely the genuinely new `LocalOrigin(intro_n,k)` fields.
For an inherited field, apply its antecedent induction hypothesis and its
actual GC1/IF field injection. For a genuinely new field apply §4.2, or retain
the actual annotated local packet. The partition equation is the constructor's
equation, so §3's case-analysis calculation assembles the entire family.
Every independent `original_license_fields` entry is retained with its own
action. The rule does not infer such an entry from the existence of the port.

`typing_q` remains the actual suspended local function. For PF2's constructed
operators its event-indexed function is already uniform over original typed
operands and independent compatible demands. Restricting the suspended
function means retaining it on the actual future inlet/tail, by dependent
precomposition. `restrictSuffix_comp/apply` check that operation. This does
not assert a new arbitrary world-substitution theorem for operational typing,
nor equality of separately chosen implementations of `typing_q`.
At each later admitted demand the two sides evaluate the retained function
on the same concatenated actual history and the same original challenge.
This is restriction of a hereditary future obligation, not a comparison of
unrelated executions started in different current states.

In detail, PF2's Name law restricts and looks up the same binding certificate.
Record and Result laws introduce their records from the actual evaluated
children at their common current tuple. The selected Name Call law is the
same GC3 phase function; GC4 retains each actual independent arm's local law.
Lambda/Strict stores its original introduction function on genuine capture
and body certificates. Restriction of these suspended functions uses the
same original leaf actions and record equations just proved. It produces no
capture/body certificate, recursive member, actual observation, or new
challenge. An opaque operator requiring complete C0 continues to retain that
original independent C0 and its lawful action; PF2 does not supply it by
source-default construction.

### 4.8 Dependent Bind and its pending suffix

The actual IF constructor inserts the first computation, the actual returned
`(v,r,C')`, its typed rebind, the second computation under that binding and
the ordered remaining suffix. At a Return, both paths of NPR use exactly
that tuple's original action and the second shared-record equation in §3.
All profiles depending on the result provider therefore use that provider's
restricted future family. No other provider with the same printed type is
substituted.

Before Return, the suffix remains a dependent function. For a Request the
original equation is

```text
Request(q,C,k) >>= S
  = Request(q,C, lambda(response,C'). k(response,C') >>= S).
```

Restriction retains the original request/response endpoint/raw handle and
uses the independently supplied resumed current configuration. The untouched
suffix is restricted by the same precomposition on both sides. No result
binding is installed early; no completed receipt is repeated. This is a
field/profile calculation on the original pending constructor, not a claim
that a pending computation returns.

### 4.9 Call

Use the actual GC1/IF fields: callee, whole carrier, checked challenge, actual
returned provider/current configuration, receipt, entry, body, designated
consumer, result, dependent future and every actual declared arm. Callee and
carrier fields use Operand/Ref; current-provider dispatch and result-to-rebind
use §4.8; receiver and arm placement use their actual tag/insertion maps.
The result future depends on the same actual result provider on both sides.
Only the actual local Call introduction/upper exposure uses its selected
local default. Imported callee/result/arm fields remain inherited.

Retained entry keeps its carrier and adds no Force. Value entry restricts the
actual Return/rebind certificate only when that Return exists. The initial
and lookup stages carry the original suspended obligation; Delay, challenge
and receipt evidence appear only at their respective actual stages. Current
authority/eligibility fields are evaluated by their original evidence at the
new event. A spent maker receipt is not treated as a new live grant.

For a complete operation, source and independent arms keep their own branch
tags or original shared Pair. Their whole licensed packets follow §§4.5–4.7.
A provider-changing W arm uses its actual output provider/future/domain
certificate; Z retains its independent witness without an execution premise.
No actual arm is deleted, no absent arm is invented, and the source branch
does not supply an independent arm's law. The case thus covers the complete
interface precisely when its genuine original leaves are present.

### 4.10 Record, Result, Delay, Lambda, capture, and designated consumer

For a Record, first retain the original ordered child computations and Bind
suffixes. After their actual Returns, all field certificates inhabit the same
current tuple. Apply the child hypotheses and `sharedFields_restriction`, then
the actual record field injections. Reused child fields keep their original
policies; only genuinely new record fields use §4.2. No latent field is forced.

Result inserts the same actual value/root/current configuration, with its
own dependent future slot. Delay/Lambda retains its inert capture/body/future
schema and suspended function; restriction uses the same dependency-closed
capture projections and original future inlet. Formation performs no latent
execution. The designated consumer inserts only its original one-layer port
and retains the resulting provider/future dependencies. These are the actual
operand/reference/local-field instances already enumerated by native §3.4
and IF §5. Their projections commute by §3, so they add no unproved composite
case to the induction.

## 5. Outer native license induction, including wrappers

The inner result feeds every actual `L` constructor in native §4.2; its
whole-rule extension is the explicit §6 construction. The proof retains the
same actual constructor tree and original leaf records.

**L-DeclaredPort / Insert.** Apply §4 to the stored `DeclContribution` and its
`PortProv`. Root insertion is exactly `ins_(r,q)` on the whole record. The tag
equation proves commutation. It sets the receiver to `beta_root(r)` and
appends the insertion route; the source owner/classification and every
license witness remain those of the inner derivation. A Ref nested inside
a declared clause remains inherited.

**L-UpperCall.** Retain the exact original `q/reg/route/seed/O0/O1/Q/SpecCall/C0`,
`kappa_orig/o/c/J-Owned` and the original complete same-operation IF
correspondence, together with `Omega_Call`. These are the independent original
upper inputs, not outputs manufactured by NP. Their actual lawful actions
transport both lexical and checking facets separately. Section 4.9 applies
to the full frame; §4.2 applies only to its genuinely local selected upper
projection. The original scalar own-upper subrecord is preserved alongside
all inherited constituents. Neither `u_f=u` nor equal owner/receiver labels
are used to identify fields.

**L-Reference.** Apply the outer induction hypothesis and the same actual
use/substitution injection as §4.4. All source origins and genuine witnesses
remain; the route is inherited at the receiver. This includes repeated
references and distinct proofs at one registered slot.

**L-Annotation.** Retain the actual original annotation rule, governed field
correspondence, scoped constraint/permission/realization evidence and its
original lawful action. Apply the induction hypothesis to the antecedent,
then the rule's field action. An annotation packet is an independent leaf
where its meaning is opaque; there is no assumption that every printed
annotation is realized. Source-local defaults do not overwrite this packet.
Nothing adds a license to a schema-only projection.

**L-Whole.** Use its actual selected whole certificate, not an arbitrary
endpoint function. The structural cases can be read directly from native §6:

| Actual whole certificate | Restriction calculation |
| --- | --- |
| Whole injective freshening | Rename the entire tuple, original introducing fields and routes once; restrict the original instantiated leaves. Rigid imports retain the certificate's fixed image. |
| Legal uniform graft | Apply the same legal dependent substitution everywhere. Each leaf retains its original instantiated action; tag and route composition give the generated equations. |
| Locally proved equivalent rewrite | Retain the original registrations and apply the certificate's whole relation/evidence map to each original leaf. Its actual lawful hereditary action is required; a bare logical equivalence does not qualify. No profile commutation for the generated graph is supplied as a premise. |
| Total fresh-coordinate definition | Append the original defining coordinate/equation to the one tuple, then use the dependent-record equation. Existing projections remain those of that tuple. |
| Unchanged client/direct-query conjunction | Retain the same original row and client evidence; pair the antecedent action at that row. The client contributes no owner or default policy. |
| Original-scope joint hiding | Keep `Hide_b(v,w_whole,adm_b,F_b(v))` under the original binder. Restrict `v,w_whole,adm_b` and the whole family together, using the inner hypotheses there. The dependent Bind equation keeps the one hidden witness for every projected port. |

For a whole certificate which changes a static presentation, the restriction
used at its target is its original certified action on the corresponding
compatible event; this theorem does not assert that unrelated arbitrary maps
commute. Where a certificate has an opaque original semantic component, its
lawful field/evidence action is the same independent requirement already
retained in native §§2/6 and the source-interface authority. The generated
operand/local-policy/partition cases are derived above, not folded into that
requirement. In particular, no new whole hidden admission is derived from NP.

This exhausts the selected native `L` grammar. An empty license fiber has no
induction case and remains empty; its support schema is retained separately.
Finite registered cycles do not enlarge the induction measure: each outer
license premise and inner declaration premise is a strict finite proof
subdevelopment. Therefore NPR holds at every actual licensed projection. □

## 6. Application to the actual fresh ValueBind and Name Call

Use exactly VB1's independent original inputs: the hereditary immutable
`b_h : ValueMem_H*(v_h,r_h,e0)`, one independently compatible extension to the
actual post-Return event `e1`, the genuine typed returned tuple
`Return(v_a,r_a,C1,w1)`, its `JointWF`, `ValueMem_A` and original
result/root/provider/world incidence, plus the actual fresh rebind occurrence
`d_x@kappa`. These are child judgments; a recursive candidate is not one.

Construct the existing original environment

```text
E1 = ValueBind(E0 restricted to e1, d_x@kappa, r_a, A,
               actual rebind origin).
```

VB1/W gives its exact old and new projections. For every actual native
licensed field inherited from `E0`, NPR supplies its profile at `e1` as the
restriction of its original package. The new x certificate is the one in
the actual typed Return. Any genuinely new local binding field gets only its
original selected local policy. The shared tuple for both is `(C1,w1)` with
all its original dependencies. Section 3's `valueBind_profile_restriction`
checks the exact old/new/profile record equation for a subsequent extension;
the paper NPR theorem supplies the generated child actions recursively.

**Corollary VB-NP.** For every original compatible later event `e2`, profile
construction for this actual ValueBind after restricting its original old
and returned child packets agrees, field by field, with restricting the
profile construction made at `e1`. The old h and new x projections retain
their same value/root/provider and their own restricted profiles; no receiver
policy is reseeded on imported h. The construction supplies this component
from the real child actions and typed Return/rebind, without an independent
assumption named `GeneratedProfileTransport` or a complete q_h certificate.

For `q_h=Call(Name h,Name x)`, apply the actual Resolve/capture route to these
two projections. Its Operand/Ref/Scope/insertion maps commute by NPR. Thus
the same h certificate used by HC1, the inert `Delay(Name x)` of W/D, and the
same whole-carrier identity check carry the original native profiles at the
same live tuple. The Call's genuinely local fields receive the already
selected defaults, while h, x, every actual independent arm and every actual
returned provider retain their own original packets.

GC3 already constructs the selected source result
`ReadInvoke(H*,D_h,IF_h)` from these actual typed operands and the original
source observation derivation. NPR now makes the generated native profile
component coherent through its actual fresh rebind, pending suffix and every
compatible future use. No pre-existing q_h license at `e0` is needed for a
field first introduced at `e1`: construct the original `Op` there from PF2's
suspended law and its genuine independent license fields, then use NPR for
later restrictions. Earlier inherited fields still use their original action.

This yields one additional concrete original Call component beyond PF1/PF2's
static formation: **the selected generated native profile/evidence family at
the actual ValueBind/Name/ReadInvoke use is the hereditary transport of that
same original family**, including shared result/provider/future dependencies.
In the original certificate-construction category table, the native local
profile row therefore no longer needs a separate generated-profile
transport premise. Its independence from live admission and annotation truth
is preserved. The source-result inclusion continues to be supplied by GC3,
not by profile naturality.

For complete original `G_call` solutions, the shared existential witness
already contains `TypedCallCert_Dec`; reconstruction may project and use it
with the existing decorated Call rule. This theorem is not a reason to block
that reconstruction on a new certificate declaration. Conversely, constructing
a full solution from native success still requires the actual source/native
bridge and genuine independent fields; the naturality theorem does not make
the known category list an exhaustive certificate introduction rule.

## 7. Boundaries and discriminating examples

The component just removed was generated-native-profile hereditary transport.
The following remain distinct and are not strengthened or assumed away:

- Genuine primitive, external, annotation and independent complete-arm laws,
  licenses and lawful leaf actions; an omitted actual leaf cannot be filled by
  local defaults.
- The actual source derivation or typed entry/RHS Return needed to apply VB1;
  in particular the realization of recursive f and its histories.
- Complete original native-success-to-`G_call`-solution correspondence,
  exhaustive original source reconstruction and all unchanged original
  `SourceProblem.InferenceSoundness` quantifiers.
- Original source constructors outside the selected native/IF envelope. This
  result neither supplies their source rule nor excludes them from the parent.
- Foreign profile interpretation, current dynamic authority/eligibility,
  original annotation realization and any separately fixed active-consumer
  correspondence. A static FullProtection value does not assert a live grant.

Three small cases expose the actual force of the proof. First, a primitive
introduced at `t` and referenced/included at receiver `r` keeps its original
packet under both restriction orders, even when their printed owner labels
coincide; applying r's defaults instead would fail §4.4. Second, a mixed Pair
with two different origin packets remains `(sigma t,sigma p1,sigma p2)` at
one tuple; allowing separate post-restriction worlds would not inhabit the
dependent Pair type. Third, a port with an empty license fiber still has no
key `(ell,k,field,w)` to which a default can be attached. The proof never turns
that schema into a license. These are source-grammar tests of the construction,
not claims that the user's program violates a contract.

No `sorry`, project axiom, assumed generated commutation law, new native source
syntax, narrowed source language, compiler edit or root import is introduced.
The companion's algebra is checker evidence for the displayed record steps;
the native-constructor/source correspondence and this paper proof require
the independent review assigned by the primary.
