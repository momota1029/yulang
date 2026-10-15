# Outer use: joint source-witness transport and its first unsupported read

Date: 2026-10-16
Status: bounded constructive reindexing/source-packet derivation; original
native semantic applicability unresolved. Fresh independent review CLEAN.
Primary baseline: `c52345489`; native production remains
`0a9af0da5080469f930da0032aa96d7d89d358c5`. Test hooks are moving and excluded.
Exclusive lease: this file only.

Integration review: independent compiler-referee `ordinary_carrier_semantic`
reviewed producer SHA-256
`d18a2c9eaeeb70b64c40a4768161d3493feff85aa566bbcce5c7fc1111f9af6f`
and returned CLEAN. Actual mapped/shared/original environments and joint same-z
packet naturality are accepted within their stated scope. The native predicate
interpretation at FunctionPort Result, together with same-parent RE/entry and
reached post-check contexts, remains OPEN. Complementary read-only falsification
found no concrete unscoped constructor/read mismatch; it is not proof closure.

## 1. Frozen original statement

The original parent is FIRST-RESULT-ADEQUACY for

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

For every original `xi=(nu,K,D)` and every original returning complete first-
Call witness z, the native representation must admit the **same** returning
value/provider W_z and matching callee-result packet F_R,z, jointly through

```text
M_W* W_z union_tagged M_res* F_R,z
```

and the original pending Bind to g, Name and future invocation. The original
scope, provider, whole carrier, source witnesses, K predicate identities, D
incidences and pending/future dependencies remain shared. Unsolved original
obligations stay predicates; arbitrary xi need not satisfy them unconditionally.
No new marginal provider or packet is chosen to make a native constraint true.
The captured/direct source programs are discriminators, not the quantified
source domain of this parent.

This pass tests whether the actual final outer Capture/FreshUse construction
permits applying joint renaming to that original witness. It may transport an
already completed semantic derivation without redispatching each old internal
comparison. It must establish the applicability premises, rather than assume
a complete original native interpretation or a complete captured semantic
view. No native runtime execution of packets/receipts is required.

The result below proves actual coordinate/payload reindexing and a joint
source packet naturality equation. It stops at an exact native predicate
interpretation read. It does not close the parent, change source acceptance,
select new Function semantics, or establish all-native-model completeness.

## 2. Required postcapture semantic reads, enumerated first

Here G is the actual captured graph and u its actual FreshUse. M means a
current mapped coordinate, A an unchanged live anchor, O an original source
or historical-evidence reference. The categories describe evaluation roles,
not three independently selected witnesses.

| Required read | Owner and actual representation | Map / fixed data |
| --- | --- | --- |
| Current root and signed Value/Effect variable occurrence | `fresh.terms[graph.root]`, `Node::Row`, `FreshUse.rows` | M for eligible canonical local RowKeys; A for older/nongeneric rows. One row lookup is shared across all its occurrences. |
| Four Function fields, signs and field incidence | `Node::Function`, reconstruction; `FunctionPort(parent,field,operation)` | All current children use the same M/A map. Field/Swap/Preserve roles stay fixed. An original parent relation used as evidence remains O. |
| Current lower/upper bound endpoints and orientation | `Bound`, `begin_candidate_fresh_bound`, restoration | Current endpoints M/A; captured side is preserved. Original `source_bound` and imported admission/emission snapshot remain O. |
| Effect atom/member, allowed families, symbolic tail | `Contribution`, `View`, Support/Allowance/AnnotationMember | New native atom/view handles are mapped presentation identities; tail uses M/A. Resolved family, source position and operation declaration are O. A copied contribution is not a new source runtime event. |
| Executable context and source-weight attachment | `relation_context`, context DAG, `context_views`, weight/view maps | Context/weight/view handles map together; ordered children and operations are preserved. Owner, source position, lexical annotation identity and concrete family list stay O. |
| Post-check context of a compiled Effect relation | `post_check_context`; `candidate_context_bound_for` | The actual captured residual/context is read. The source meaning of an already discharged check is a separate semantic obligation, not supplied by renaming its ID. Value parents are not discharged. |
| Source checking/callee/argument/result origin | `ApplySourceInput`, `NativeInterface`, original HIR/source table | Source occurrence, original children and checking identity stay O; current native fields are followed through the actual u Transport/map. |
| Same-use evidence ancestry | imported snapshots; Transport from/to; Replay parents/BoundKeys | Current child/to is M/A; original parent/from and snapshot heads remain O. `use_origin=u` selects the actual transport, not an arbitrary sibling use. |
| Source packet, actual provider and private captures | existing complete source witness z and immutable source interfaces | Original value/provider and captured bindings stay O. Only their current typed native presentation selectors are reindexed. |
| Pending Bind, response/raw continuation/future interface | same complete Call witness and source code references | Same dependent suffix, provider/current world and binders O. They are not recombined from separately chosen returns. |
| Protection, predicates and dynamic eligibility coordinates | `(v,t,chi,K,D,L)`, original receiver/handler/activity/Receive/Observe | Source typed paths are presented through M/A; boundary/event/receiver IDs, K predicate IDs, nu, L and current source configuration stay O. Fresh inference scope/use IDs are not runtime receivers. |

This is the read inventory needed for the original witness. The code proves
coverage of current graph/context operands below. It does not, merely by
providing this inventory, prove that every listed source semantic read has a
native evaluator or that every source dependency was represented in G.
The first unresolved read is isolated in §6.

The public `retained_input` closure is not the current-use semantic support.
At `candidate_context.rs:1015–1095`, selecting any dependency endpoint selects
its other endpoints; Transport therefore reaches original parents and sibling
uses. Its reader exposes useful ancestors but can be larger than one u.
Applying one current mu to that whole closure would rename the wrong objects.

## 3. What the actual FreshUse construction establishes

### 3.1 One current coordinate map

Capture interns canonical endpoints and RowKeys; its worklist expands every
local row it reaches and the exact signed structural Function children
(`candidate_scheme.rs::Capture::intern/row/expand_node/expand_row`, approximately
`:341–750`). Older/nongeneric rows are retained as live anchors, rather than
expanded into a second private copy. The context-payload loop also interns
symbolic tails and retained latent negative demand roots (`:806–884`).

Preparation immediately follows capture without running typed children between
its row decisions. `prepare_candidate_fresh_use:1095–1140` uses one
`canonical_rows` map: one fresh RowKey per eligible original representative,
otherwise that representative itself. Fresh allocation is disjoint from the
existing row namespace. Capture already interned representatives uniquely;
without an intervening semantic mutation, distinct local representatives get
distinct fresh rows. Value and Effect RowKeys are tagged identities, so an
identical numeric ordinal in their two arenas is not accidental aliasing.
Every actual occurrence of one RowKey uses the same map entry.

The signed structural DAG is rebuilt from those entries, using one terms
table and the unchanged four child roles (`:1230–1287`). Cycles return through
row lookups, not unbounded structural unfolding. This establishes the finite
endpoint part of the renaming premise. It does not select a semantic carrier
for those lookups or split a common source assignment by role.

### 3.2 Atom, view and context support

`prepare_candidate_fresh_use:1160–1230` creates current effect operands from
actual captured nodes. Contribution copies retain the resolved family and
source origin. The view map is keyed by original view and mapped tail; repeated
references to that same view/tail share the copy. It does not identify two
original source views merely because their allowed vectors coincide.
`candidate_copy_effect_view:885–910` preserves owner, position, allowed vector,
operation provenance and attachment source, while replacing its tail.

For each captured context payload, preparation validates its original
weight/view pair, obtains the corresponding current view, and records the
current weight. `context_payloads:1588–1624` follows the complete constructor
DAG: PrefixLeft/SuffixRightPops, ordered Replay, Swap and WithoutLeftFilter.
A BothFromRight payload without an authentic retained owner causes availability
failure; it is not silently interpreted as identity in a successful copy.
`rename_fresh_contexts` reconstructs exactly this DAG with the common weight
map (`candidate_context.rs:1463–1582`). Thus every current payload it actually
reads is mapped, shared or explicitly source-fixed. Ordered Replay is not
commuted. Preserving this syntax does not import the detached StackWeight
algebra as source semantics.

The ordinary unscoped route has no scoped transformer. In the optional scoped
branch, current ScopeTransformer/input/demand references have their own actual
common scope/input map (`candidate_scheme.rs:1290–1318`), while original Call
identity and source binder remain fixed. This records its additional reads;
this note proves no general semantic adequacy of that experiment and adopts
no collector rejection as a source restriction.

### 3.3 Evidence needs an indexed interpretation, not global renaming

`begin_candidate_fresh_bound:1373–1420` makes the current pair from the same
terms/rows/operands, preserves its captured owner/side and records a Transport
with parent, original source BoundKey, current target BoundKey and u.
`candidate_context_fresh_transport_scoped:3658–3675` retains original source
sets and attaches the actual child. The imported EvidenceSnapshot is unchanged.
The original relation/FunctionPort/Replay remains an ancestor of the copied
bound; there need be no new numerical parent comparison Pprime.

Consequently a legitimate interpretation has two indexed environments:

```text
current-u endpoint read      -> current assignment through mu
original ancestor judgment   -> its original/template assignment
Transport(parent,child,u)    -> the actual from/to correspondence between them.
```

An old template derivation can be instantiated at this use's pulled-back
assignment. That does not mean all historical original-session identities
receive the current assignment globally. Shared anchors use the same live
assignment in both environments. Source/provider/runtime identities are fixed.
Other transports exposed by reader closure keep their own use indices.
This is the exact setting in which a same-member joint renaming argument
could transport an established semantic derivation.

## 4. Constructive joint packet reindexing under the actual map

This part uses the already constructed original source packet, not a desired
packet inferred from a bare row. At every original xi and z, retain the same
source positions, packet and complete Call/suffix. A current native selector
has the form `(current endpoint/view occurrence, original typed path)`. Apply
the actual mu to its current endpoint presentation and leave the original
typed path's field labels and source identities unchanged. At a variable
reference, the source view package supplies its original typed paths; no
recursive unfolding of native bounds or finite enumeration of alpha is needed.

Write J_mu for this change of presentation. Binding identity and structural
Result-prefix removal commute with it because actual Function reconstruction
preserves the selected field and its direction. If M is an original generated
typed correspondence, define its *presented* counterpart by the actual mapped
endpoints and same typed correspondence. This is presentation of that existing
M, not a new arbitrary flow relation chosen to obtain protection.

For an original profile incidence, expand both images:

```text
J_mu(M_*chi)(J_mu(p'),b)
  iff exists p. chi(p,b) and M(p,p')
  iff (J_mu(M)_* J_mu(chi))(J_mu(p'),b).
```

The source witness p, boundary b and source tag are identical in the two
existentials. The same proof applies to each D incidence pointing to its
original predicate k. K is the same shared ledger under the same nu, not a
newly copied formula; L and all original provider/event/runtime identities
are fixed. The proof does not use b's current activity as an invariant across
execution: activity is read from the same source configuration at the query.

Apply this equation to both tagged source inputs of the **same** z:

```text
J_mu(M_W*W_z union_tagged M_res*F_R,z)
 = J_mu(M_W)_*J_mu(W_z)
       union_tagged J_mu(M_res)_*J_mu(F_R,z).
```

No independent marginal witness, new result seed or new profile union by
value-pointer identity occurs. Compose with the actual source Bind/Name
identity maps; the original pending suffix/response binder is unchanged.
Private captured packets remain at their original private binding references;
public source packet presentation does not paste them onto every public port.

For an already source-derived Receive/Observe/Path witness, J_mu changes only
its native presentation selectors. The same actual view, source typed path,
receipt, receiver and event witnesses establish the corresponding source fact.
The source current-scope filtering theorem therefore uses the same activity
checks. This applies the existing typed-boundary §6/receiving theorem; it is
not a claim that inference allocated a new dynamic receiver or that the
abstract renaming theorem independently proves handler hygiene.

This establishes joint naturality of the known source packet representation.
It does **not** prove that assigning this packet to a current native endpoint
satisfies every incident native constraint. The distinction is essential for
the original parent and is the remaining read below.

## 5. Why the abstract joint-use theorem is not yet fully applicable

The draft's joint-use theorem (`intrusion-abstract-semantics-draft.md:876–961`),
reviewed in the 2026-09-30 joint-use record, requires:

1. a complete selected member support for all view/continuation/observation
   reads;
2. actual role packages and endpoint/constraint/evidence evaluators;
3. equivariance of those evaluators, including payload validity;
4. one common assignment for coupled uses and a well-sorted joint continuation.

§3 supplies the actual current coordinate/context copy, with shared anchors
and historical ancestors treated correctly. §4 proves the joint source packet
operation's equivariance, preserving the original common xi/z. The original
source Call supplies the same dependent continuation; it is not split into
per-port or per-use marginal worlds.

These facts do not establish premise2 for the native comparison whose result
is being reused. In particular, an original completed native Function
comparison is an executed four-child generation/processing event. It is not
already a semantic derivation of the complete source descriptor predicate.
Transporting its four mapped field constraints with its exact parent preserves
their incidence, but cannot create that missing semantic conclusion.

The first unsupported read below remains even if the current finite graph is
fully enumerated and every structural payload has been copied. Conversely,
retained_input's extra sibling uses do not constitute a data-loss counterexample;
they only prevent treating its whole closure as one renamed current support.

## 6. First exact unsupported interpretation clause

The first missing native semantic read for the original conclusion is:

> Evaluate the copied Result Value relation, with its actual original
> Function parent and same-use Transport ancestry, as the source relation
> on the same actual returned provider and matching callee-result view,
> jointly with that parent's Effect/entry/context obligations.

Operational owners are `lib.rs::dispatch_live_item` at its four Function child
construction (`12590–12618`) and
`candidate_context::candidate_function_port_admit` (`3000–3064`), then the
captured Result bound's `begin_candidate_fresh_bound`/Transport above. The
native Result child has correct field3 endpoints and Preserve context. The
selected original source call supplies the same z and its two packet images.
What is not established is the following evaluation equation at those
actual correlated inputs:

```text
the current Result/Effect/entry constraint predicates at (parent,u,mu)
are satisfied by the source-image packet from that same (xi,z),
with their original complete challenge and pending/future obligations.
```

This equation is not an additional language definition. It is the required
source-to-native predicate adequacy clause. Its antecedent is not "the
original native interpretation already satisfies all of G": proving that
would assume the missing conclusion in a larger form.

The selected source rules do construct the complete source descriptors and
same-provider membership/actual challenge for the original witness. Thus this
is **not** another claim that an abstract whole source interface I must first
be invented. The unsupported step is using the particular native Value/Effect
predicates as that source relation. A source packet with correct tags can
still be merely a label on native field3 until these incident predicates have
that interpretation.

The necessary local check is the complete same-provider action from contextual
Function membership: at the same original challenge, retain its whole carrier,
entry/receipt/current context and provider, then check its complete/pending/
future observations jointly under xi. Native Function dispatch's four child
constraints do not state that action by themselves. The 2026-10-13 joint-field
transport theorem §4 leaves that exact semantic action open; the
2026-10-14 disposition theorem §4 shows why its structural-arrow conclusion
does not supply the complete target-challenge lift. Here source origins and
actual selected dispatch are available, so their earlier absent-source-seed
limitation is repaired, but their semantic implication is not thereby proved.

The copied Effect/context predicates are part of this same read. For a
nonidentity compiled Effect parent, `relation_context(parent)` can read its
post-check residual; interpreting that residual requires the source law of
its original discharge together with its exact retained Allowance check.
The actual evaluator's nominal allowed-family test does not by itself prove
full K/D/path/receipt semantics. The detached `evaluate_context` fold has no
live source semantic consumer and cannot be adopted as that law. Identity
contexts in the concrete discriminators avoid this extra case; they do not
remove the Value/complete-Call clause for the original all-xi/z parent.

### Residual classification and smallest owning conclusion

This is category **(a): an already selected source predicate whose constructive
native interpretation has not been instantiated**. Contextual Function
membership fixes actual admission and complete observations at the same
provider/challenge; typed-boundary §6 fixes both Result packet inputs and their
joint K/D action. No new observable choice is selected here. No category-(b)
missing runtime/native behavior or evidence has been demonstrated, and no
category-(c) architecture decision follows merely from this failed proof.
The native comparator need not execute those source observations.

The smallest owner is the actual Result child admitted by
`candidate_function_port_admit`, together with its same-parent RE/entry
obligations. Fix its genuine source descriptors, actual challenge d and
complete first-Call return z from the selected original source judgment.
Construct the current Result endpoint interpretation from that same d,z so
that the source obligation implies the native Result predicate, and its packet
projection is exactly the two tagged original images, while the same
interpretation evaluates the parent's Effect/entry predicates under xi.
This asks for one source-qualified local interpretation at the real consumer,
not an assumed interpretation of every constraint in G. The source-side
predicates are already selected; their identification with these particular
native row/Function/effect predicates is the missing proof.

There is no proved source-qualified contradiction here. The copied fields,
source references and original semantic witness have not been shown lost.
This is a localized missing interpretation law at an actual relation consumer,
not a claim that current metadata is incapable of representing it.

## 7. Consume the frontier result and stop at the remaining owner

The independently reviewed
[demand frontier](2026-10-16-native-returned-callable-demand-frontier.md) derives
its source-time negative upper path, merged/nonmerged g uses, one-map restore,
and selected lower at live mu(a). The census independently authenticated the
selected future dispatch and outer AE image. A complementary source audit
reported no final unscoped capture/read mismatch: payload discovery covers
weight-backed views/tails, one view map serves operands and weights, and the
original snapshots remain joined by actual FreshUse causes. This is independent
negative falsification evidence supplied by the primary, not a premise proving
§4 or §6. Thus reconstructing the original
first-Apply negative Function or redispatching every completed internal
comparison is not the next prerequisite. It would leave §6 unchanged.

The source captured/direct discriminator remains represented by §4's two-world
packet presentation: captured's original V read supplies Observe joined to
outer's entry receipt; direct supplies no such read from the coexisting
captured declaration. No whole-reader-closure union can manufacture that
source path. This is positive source-witness reindexing, not proof that the
native predicates already distinguish every such semantic observation.

Economy audit: original A/B source/native adequacy stays required. No new
restriction, role policy, registry, runtime packet evaluator or metadata
repair is licensed by this missing proof. The source coordinate/evidence
retention work and pure packet naturality are consumed above; repeating an
inverse-map census, scalar Name equality or conditional whole-graph formation
would not establish the native same-provider predicate clause.

Next source/proof owner action: prove or refute §6 at the actual
FunctionPort/Result consumer, using its authentic source descriptors and the
existing complete Call/entry/packet rules. Its exact inputs are the joint
parent, both original admissions, same use map and original xi/z. Keep the
Effect post-check law explicit when reached. Neither arbitrary-native-model
completeness nor a new exhaustive Function grammar is requested. Until this
clause is established, FIRST-RESULT-ADEQUACY, full B, hygiene, soundness and
principality remain OPEN.

## 8. Checks, dependencies and commit packet

One bounded construction-led static pass; ordinary configured Sol/high requested,
effective model/effort metadata unavailable. No delegation or model override.
Read-only `cat`, `sed`, `rg` and hashes; no Git, tests, builds, probes, network,
compiler/test/shared-record edits. Only this leased note was written. Zero
heavy processes or measured samples; assigned cap 30 minutes, CPU/RAM and exact
elapsed time uninstrumented. Fresh independent review is required.

Baseline `c52345489` supplied by primary. Production owner baseline remains
`0a9af0da5`; candidate_scheme/test hooks are moving, so this pass reads only
production bodies and asserts no whole-file test-hook hash. Native census
verification/review/integration is primary-owned. No executable evidence is
claimed from this leaf.

Exact lease: `notes/theory/2026-10-16-native-outer-use-source-witness-transport.md`.
Claim class: constructive actual-map/source-packet naturality with explicitly
unestablished native predicate applicability; not a parent theorem or compiler
counterexample. Proposed checkpoint:
`research: derive joint outer-use source packet reindexing and isolate predicate bridge`.
Shared-record delta for primary/curator: record the mapped/shared/original-read
separation and same-z two-input naturality, preserve the source/native predicate
clause at FunctionPort/Result and compiled Effect post-check owners as OPEN;
no first-demand readback or metadata repair prerequisite follows. No shared
record or previously reviewed proof was edited.


Frozen dependency observations (SHA-256):

```text
ad2ba2b0d388063311d472dda8bc5da60df4e6ad5889957560208f2e239d9c44  notes/design/2026-09-29-intrusion-abstract-semantics-draft.md
6d1db7fe3d78a24e6043003eebd23885a9643e7bd02a57815a35258fefdf3649  notes/progress/2026-09-30-intrusion-joint-use-renaming-review.md
786cf5da327aa97329ebc29f57cc328ebd55ad50ef6fd07424e3b70ce40760a1  notes/theory/2026-10-13-fresh-use-function-port-joint-transport.md
97bc16f074411914b292cfddcb57e39e1e4df93948b7e1a9bebbc4bcc30b5fd6  notes/theory/2026-10-14-fresh-use-function-disposition.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
b5b2a3176ffb3e5271d2d1150ec0e131752ed881a1eafefd0be40827df593e16  notes/theory/2026-10-16-native-returned-callable-demand-frontier.md
5ccc9cce1ec6f8626276f1b9d214524b1bf30ab1a8ac9430b805a57df96d7b71  notes/theory/2026-10-16-native-received-root-interpretation.md
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
a37c0c605802fc482c20a59199eea7a09b56ab966454db2b11dfe2d62b1dead7  crates/yu-solver/src/lib.rs
```

The three hashed native owners match the supplied frozen production inventory.
Current research-note hashes include primary review/integration metadata;
producer review hashes are distinct as recorded in their headers. The moving
candidate_scheme cfg(test) instrumentation is not assigned a new dependency
hash by this leaf. Changed dependency semantics: none reported; no direct Git
comparison performed. Writes stop at this handoff.
