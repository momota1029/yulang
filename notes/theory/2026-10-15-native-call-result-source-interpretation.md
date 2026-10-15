# Native Call result: a source-indexed interpretation of the actual result fragment

Status: independently reviewed constructive forward source-indexed interpretation and
bounded native wiring proof; native interpretive adequacy, executable packet
transport and the original B/Call parents OPEN.
Baseline supplied by primary: `0a9af0da5080469f930da0032aa96d7d89d358c5`.
Exclusive lease: this file only; constructive leaf, no delegation or source edits.

Independent review: `ordinary_carrier_semantic` found no findings at SHA-256
`1979f7f0538569f6a08cce546e0ea8d8020260946dc2586a08f94abbffbfdfb6`.
The accepted result is source-origin decoding, constructor coordinate preservation
and pointwise source-rule application. It is not a native constraint-model
valuation or proof that Replay computes the annotation. The original native
Replay/post-check and copied/merged-history adequacy gates remain OPEN.

## 1. Frozen statement and exclusions

Use the original case and binders of the independently reviewed
[returned-value classification](2026-10-15-callback-result-exposure-classification.md)
§1: original receiver definition d, Value formal f, annotation a, binding
scope S, shared result value endpoint alpha, original beta_f and first/second
upper uses u1/u2. The source is

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

Quantify pointwise over **every original xi=(nu,K,D)** and **every original
returning witness z of the first complete Call at u1**. Its returned packet
W_z and callee-result packet F_R,z are projections of that same z, with its
same provider, entry, argument, scopes, dependent Call challenges and pending
Bind suffix. No independently chosen returned callable or marginal witness is
introduced. The first Apply's actual unscoped native construction is in scope;
the scoped collector's rejection of the second Local-callee use does not
restrict the source quantifier.

The required local interpretation represents the original returning value and
the two tagged source images at the actual native result origin. On return:

```text
result(u1,xi,z) = M_W* W_z union_tagged M_res* F_R,z
M_res(Result.q,q), only at matching existing typed paths.
```

K,nu and original lineage remain those of z; each D incidence retains its
original predicate reference. The pending Bind uses this same return binder;
for a Request it retains the original pending suffix and response binder.
No new protected-variable seed is introduced by this result construction.

The statement concerns a **source-indexed relation on retained native term
occurrences**, not recovery of a unique runtime value or profile from a bare
type row. A type row may describe many returned values. A shared raw Term may
occur in different typed views. Equating those views would contradict the
governing typed-boundary rule. The interpretation below is relational in the
original z and keeps the original source occurrence/derivation index.

Excluded: proving native scalar success equivalent to complete Call inclusion;
constructing an original Call witness from solver success; activating every
retained dependency; complete replay/capture/generalization; actual native
packet/effect consumers; handler selection, profiles at runtime, soundness,
principality and F5 retirement. None is silently assumed or closed.

## 2. Governing sources and independent inputs

- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6, “One relational transport operation”: packet evidence belongs to typed
  views; result formation has actual-value and matching callee-result inputs;
  matching result projection removes exactly its prefix; the tagged image
  acts jointly on chi,D under the original K,nu,L.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3,6,9: Application binds the original complete Call output; Lambda uses
  Result(I_body); Binding/Name preserve that returned value; requests retain
  the same continuation suffix. Native production is distinct from its
  declared result consumer.
- [Returned-value classification](2026-10-15-callback-result-exposure-classification.md)
  §§1,3–5: the actual source constructors generate these maps and no new
  outer-formal seed. This is the source rule being applied, not a native
  transport premise supplied as a hypothesis.
- [Callback B](../design/2026-10-03-callback-context-delivery.md) §§2,2.1,4:
  preserve the complete context, original slot/profile and final inequality;
  no expected-endpoint substitution or row-only replacement of complete Call.
- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–4 and [legacy withdrawal](../design/2026-10-10-simple-sub-legacy-withdrawal.md):
  ordinary generation/accumulation, not execution or solve-at-generation;
  no resurrected registry or captured-binding reconstruction prerequisite.

The [owning audit](../progress/2026-10-15-native-call-result-profile-transport-audit.md)
identifies the first Apply/Result seam and downstream retention. This note
does not infer absence from its observer's MissingSuppliers list. It uses
the actual constructor records below.
The audit was initially supplied at SHA-256 `3168611e0fe633bc39debbbd3d286437b594888c7ee0cc396f5514c4a1c93b26`;
the primary subsequently recorded its independent clean review in the header.
The final metadata-bearing audit hash is listed below; every inspected native
source hash remained unchanged at this note's freeze.

## 3. Decode the actual finite source/native result origin

For the retained Apply source record c, read its actual LocalSource Apply and
its callee/argument by the stored original owner/expression/child indices.
Read its checking occurrence, recipe, component result and NativeInterface.
Call the resulting finite origin O_c. This is a deterministic read; it
chooses no semantic provider, return or profile.

`candidate_source.rs:978–1020` supplies exactly this tuple before solving.
`shadow_apply.rs:1524–1547` checks that the recipe's original callee, argument,
effects, result, checking occurrence and source record agree. At 1550–1625
the actual native demand is constructed as

```text
D_c = NegativeFunction(argument, argument_effect, invocation_effect, r_c)
r_c = native endpoint of this exact Apply's result component.
```

The stored NativeInterface retains D_c and r_c before admission. The observer's
`term_view` validation (`candidate_call.rs:483–500`) independently reads all
four actual fields and checks field 3 equals that stored r_c. Neither a
later Function shape nor a successful subtype query supplies O_c.

The source-side decoder of O_c is the original Application constructor at
that same Apply occurrence, with its original callee/argument and source
result binder. It is fixed by typed-core §6 and the original source rule;
it is not an inverse search for a convenient application. The source alpha
and native r_c need not be equal rows. O_c identifies the **result origin**,
not a scalar equality with alpha.

There is an actual base for the original callee result coordinate.
`candidate_effect.rs:1037–1056` keys annotation variables by their original
(AnnotationScope,name), producing the shared polar row pair.
`candidate_formal_value_pair` at 1118–1136 recursively places the original
result pair in field 3 of the paired Functions, separately from field 2.
`candidate_formal_annotation` at 1185–1224 admits the positive annotation into
f's parameter row at slot 43, and that parameter row into the negative
annotation at slot 44. These are generated at the original annotation/formal,
before the later Call. Source alpha is interpreted at that original scope
by xi, not replaced with the Apply's new result row.

The first Apply's `formal_name` joins its exact f Name to that same formal
registration. A canonical source-origin route uses the lower annotation
admission at slot 43 and upper Apply admission at slot 0 of this c. Its join
key is this original **source formal registration and Name**, not mere equality
of native row ordinals. Native bound replay has an actual constructor for
this ordered pair: `candidate_extrusion.rs:799–842` visits each opposite bound
and passes both actual BoundKeys to `candidate_context_begin_replay`.
The latter at `candidate_context.rs:3393–3460` retains both original relation
parents and BoundKeys in `Dependency::Replay` and in the evidence recipe.
Thus the graph has a canonical same-callee join anchor in addition to a
field-3 pointer. A second source origin aliased to the same row is not that
same source registration and cannot silently replace this route.

For a Lambda provider the actual source/body correspondence has its owning
constructor too: `candidate_source.rs:1071–1086` records the exact body value
endpoint in LambdaRecipe, and `lib.rs:11289–11399` uses that endpoint as
positive Function field 3. A parameter Name's endpoint can be a shared formal
row instead of a body component; the constructor preserves that case. Thus
field 3 denotes Result(I_body)'s value position, not ResultEffect. An opaque
received provider needs no invented local Lambda origin: its source typed
callee view is an input of the original z. Its body/return remains bound
inside that same complete Call witness.

## 4. Canonical relational valuation, without marginal choices

First interpret the **source constructor** decoded by O_c, independently of
the native constraint's truth. Under xi let Call_c(xi) be its existing
original complete source relation, with its original event/return binders.
Its returning fiber contains records

```text
(z, provider_z, original return binder W_z, matching callee view F_z,
 original challenge/suffix/dependency data of z).
```

This is a restriction/projection of the original source relation. It neither
postulates a new Call relation nor constructs witnesses from endpoints.
In particular W_z and F_z cannot be selected from different records.

Interpret the native **origin occurrence** (O_c,r_c), rather than r_c alone,
by this returning fiber, exposing the original return binder as its value.
This definition is grounded by the actual O_c decoder and its exact field-3
wiring. It provides a semantic valuation family for the symbolic result
variable; generating that variable does not evaluate the Call. Shared raw
terms are interpreted as a relation indexed by these origins and z, rather
than overwriting one alias's packet with another's.

For the canonical Replay route above, the source valuation of its two parents
is joined on the actual f binding of that one source environment. The lower
parent is the original annotation view of f; the upper parent is the actual
Name f use at c. Source Name reads that existing binding by identity. Hence
their provider is the same provider of z, rather than two independently
chosen inhabitants of the common native row. The Replay record's ordered
parent/BoundKey references specify where this join is made. Defining this
source-indexed relation is semantic interpretation of those retained
references; it does not assert that scalar replay itself checks profile
equality or computes that join at runtime.

Now evaluate the finite *source view-formation rule* at each such record.
There are precisely two source inlets:

1. ActualReturn(c,z): the whole actual returned packet W_z, with the source
   returned-value correspondence M_W.
2. CalleeResult(c,z): the result subview of that very F_z, with the structural
   correspondence removing Result from matching typed paths.

These are projections of the record, not assumed already transported packets.
Expanding typed-boundary §6's source result-formation operation on those two
inputs **constructs** the displayed tagged image. It determines the result
profile/packet, rather than assuming preservation of a supplied result packet.
For every original typed path p, the output incidence is witnessed by exactly
one tagged inlet and its matching source path; expansion of relational image
gives both directions. A path at the complete Call's immediate effect port
has no Result-prefix match and cannot acquire a latent result incidence.
An independently existing incidence in W_z still has the first inlet, even
when the second supplies none, and conversely for a callee-result incidence.

K and L are the original projections of z, and D follows the same indexed path
maps as chi. No new predicate ID or origin is generated by either inlet.
Thus this construction is pointwise for every xi,z and preserves original
shared predicates/provider/scopes. It does not require a finite enumeration
of the possible shape of alpha or an empty incoming profile.

## 5. Actual FunctionResult edge implements the structural projection

The native Function dispatch reads the four children of one actual positive/
negative Function pair. Its Result child at `lib.rs:12590–12618` is exactly
`lower.field3 <: upper.field3`; its ResultEffect child is separate.
`FunctionDispatch` retains that one ordered four-child array; the actual
admission/enqueue split at `lib.rs:12740–12766` selects a field and child from
that array. It does not independently look up a second provider result.

`candidate_function_port_admit` at `candidate_context.rs:3001–3063` retains
the same processing parent in `Dependency::FunctionPort { child,parent,
field:Result,operation:Preserve }`. It reads the parent's post-check context,
preserves the parent's source references and creates the child's relation
with those values. The deferred demand is authenticated against the parent's
actual negative Function root. Result consumes that demand without adding
an AE/RE transformer or seed. That is distinct from discarding inherited
context or packet evidence.

Interpret this field-labelled edge by structural projection **in its parent
fiber**. The field tag selects Result and therefore its result-prefix map;
Preserve supplies no argument-direction swap. The origin O_c fixes the
target result binder, and the parent fiber fixes z once. Consequently both
inlets of §4 are interpreted with that same z on this actual child edge.
This is a dependent projection, not the Cartesian product of two independent
scalar port models. The actual parent/child/field references are precisely
the finite graph data needed for that interpretation.

The decoder must also validate actual copies before identifying a parent with
this origin. `candidate_extrusion.rs:220–255,343–370` reads the original four
Function children, makes one ordered child-key array and rebuilds from that
same array. Result is always entry 3 with the original polarity; argument
reversal affects entries 0–1 only. For a newly copied row, lines 93–128 retain
its actual parent/copy/operation and install its one-sided source link.
`candidate_context_value_rewrite` at 2977–2999 retains the original relation,
rewritten pair and source references, and follows the copied upper demand.
A copied Function's Result coordinate is therefore decoded by following this
actual field-3 rewrite and its actual row-parent record. It is not decoded by
asserting equality between alpha, the Apply row and its copied row.

This proves the **coordinate-origin** step for these actual copy constructors:
the source path remains Result.q while its native term reference changes by
the retained mapping. It does not by itself prove that all later copied bounds
are activated or that arbitrary context evaluation preserves packet meaning.
A missing/inconsistent mapping is an interpretation gap, not permission to
choose a new source witness at that copy. The first Apply's original O_c
remains the source anchor throughout.

Two static deletion discriminators make this construction depend on native
evidence rather than permit any graph to satisfy it. Delete c's retained
ApplySourceInput/source-input link and there is no authenticated native
result/checking/source tuple for the decoder; HIR alone still has a source
Call, but this native-origin interpretation is unavailable. Delete the
FunctionPort(Result,parent,child) edge and the target scalar pair may still
exist, but the decoder has no licensed Result projection from that parent;
it must not infer one from row equality. Relabel the edge Argument, or wire
its child to field 2, and validation against the actual four-child array
fails. These are structural falsifiers of the proposed decoder, not executed
mutation tests or claimed source counterexamples.

No premise says that native scalar Function decomposition by itself proves
the parent complete Call relation. The original z is the universally
quantified source input, not obtained by reversing scalar success. Nor does
this theorem assert that every native valuation is induced by a source z.
Those converse/soundness questions are separate from the original pointwise
representation prerequisite.

## 6. Retention, pending Bind and exact coverage boundary

The relevant graph index is not `RelationKey.sources` alone. Those source
sets are checking/Value-reference associations (`candidate_value_graph.rs`),
useful for the original source join/SCC relation; they are not profile packets.
`Origin` retains the source checking occurrence, while FunctionPort retains
the exact parent relation and selected field. EvidenceSnapshot retains that
relation plus bound and admission/emission heads. The complete batch also
retains the same HIR and ApplySourceInput/NativeInterface. Therefore the
finite O_c/parent/Result interpretation can retain references to all original
profile/dependency coordinates of z as semantic parameters, without inventing
a new profile table or choosing witnesses from the source set.

In particular, merging the same raw Term or deduplicating a checking-source
set does not force the origin-indexed packet relation to identify two typed
views. Ordered Replay dependencies keep their lower/upper parents, and
FunctionPort dependencies retain their original parent. The interpretation
uses those derivation references and the shared source fiber, not equality
of endpoint rows or families. This proves **capacity to represent** the full
two-input packet at this local constructor; it does not prove that a later
native effect consumer evaluates that relational image or every bound is
activated/replayed with it.

For the local binding, the original source Bind uses the source Application's
same W_z binder, already identified by O_c. Return then binds that packet;
Request appends the same Bind suffix to the original continuation, leaving
its response/event/dependency binders untouched. Nothing in the native
first-Apply/Result constructors creates a competing source return binder.
This derives the source interpretation of the pending suffix, without
claiming native continuation execution or complete local capture replay.

The completed result is a **forward source-indexed valuation construction**
and an actual native coordinate/projection bridge, for every original xi and
returning z, with no supplied native result-transport premise. A bare-row
interpretation is inadequate; the retained original registration/Call,
ordered Replay parents, field edge and actual copy origin provide the
relational index. No source-qualified counterexample to the compiler has been
established.

This does **not yet discharge native interpretive adequacy** for the original
parent. The exact remaining clause is at the ordered Replay/native-context
consumer: prove that its denotation on the actual lower annotation/provider
fiber and upper Call fiber is their **joint source-binding/provider/xi join**
used in §4, and that its actual post-check/copy evaluation realizes the same
two-inlet Result image. Retaining two parent references makes that interpretation
possible; it does not prove the current native evaluator executes it. In
particular this note does not establish that every later canonicalized/copied
Result relation has a complete validated origin path or that scalar success
excludes a mismatched-source fiber. The target is an exact local commuting
square at `candidate_context_begin_replay`/`candidate_function_port_admit`,
not another supplied-packet preservation lemma or a new global registry.

The original A/B parent and its first-result adequacy premise remain OPEN.
The primary may consume the concrete origin-qualified construction separately;
it must not promote this forward interpretation into executable transport,
complete Call, replay or solver soundness/principality.

Proof-obligation-economy audit: the initial raw-field reading and provenance-only
reading do not establish this same joint-interpretation clause. It is A/B
source/native correctness and natural result transport, not an optional
all-native-model characterization. It is also not established D loss: the
source AST, original formal/Call identities and ordered derivation parents are
still retained, and no actual discarded W/profile constructor was found.
Therefore neither a new registry nor a new per-result profile field is justified
by this packet. A further attempt must address the actual Replay/context
denotation or a source-qualified counterexample to it, not restate the
two-input image with its native interpretation assumed.

## 7. Checks, resources and commit packet

Method: one bounded constructive source-indexed valuation method, with actual
constructor/consumer tracing. The initial bare-field/metadata readings exposed
why a unique packet cannot be inferred from a raw scalar row; the constructive
interpretation instead uses the source origin already retained at the owner.
No false-constructor conclusion was inferred from an observer flag.

Budget: 35 minutes supplied by primary; bounded static shell reads only,
zero heavy processes, tests, probes, builds, measurements or delegated jobs.
Wall/CPU/RAM were not instrumented. No code, Git operation, shared-record or
other leased-path edit. Requested runtime Sol/high; observed effective
model/effort metadata unknown. No Astra or runtime override claim.

Dependency SHA-256 values are recorded below; comparison to the baseline Git
tree belongs to the primary because Git commands are excluded from this leaf.

```text
9e3cf4d00f50a897d00cb211d8bca3517551f33d4274bef556cefd96c9c2ff82  notes/progress/2026-10-15-native-call-result-profile-transport-audit.md
6f2bc05137e451c38391655bb2d45e9224f12eebf7d58c7f5a78c8abd69c93f4  notes/theory/2026-10-15-callback-result-exposure-classification.md
26abb65f09f2dcf7b3f798329d7f9cf867d3e6196b4cd79c03b3b558d90566e5  crates/yu-solver/src/candidate_source.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
a37c0c605802fc482c20a59199eea7a09b56ab966454db2b11dfe2d62b1dead7  crates/yu-solver/src/lib.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
4689e2ee34c69c9492ecc1a58af15d7c802f44dca82d69f76e3e1520d8d5f3dd  crates/yu-solver/src/candidate_call.rs
1a3c55abf2da669342076465c53d72aff185a9d7307374a9011d47ddd7458ef5  crates/yu-solver/src/candidate_value_graph.rs
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6  crates/yu-solver/src/candidate_scheme.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a  notes/design/2026-10-10-simple-sub-legacy-withdrawal.md
```

Commit packet: exact lease
`notes/theory/2026-10-15-native-call-result-source-interpretation.md`;
baseline `0a9af0da5080469f930da0032aa96d7d89d358c5`; dependencies above,
none edited by this leaf. Research-only constructive forward interpretation
and bounded wiring proof,
independent review pending. Checks: static source reads/hashes and final
whitespace check; no executable verification. Proposed checkpoint:
`research: interpret native Call result at its original source fiber`.
Shared-record delta left to primary/curator: record the constructive
origin-qualified forward interpretation and actual coordinate/copy bridge,
while retaining the first-result native-adequacy premise and all original
parents OPEN. One next action: independent proof review should test the
origin decoder and identify whether the actual Replay/Result evaluator
realizes its joint source-fiber semantics; no further equivalent
supplied-packet lemma is indicated.

Frozen at producer handoff for independent review; no further writes by this
leaf without an explicit returned lease.

### Primary integration (2026-10-16)

The producer handoff above is historical; the independent review is recorded
in the header. The primary checked all 16 distinct dependencies across this
note and the complementary falsification note: every recorded current hash
matches, and all 10 native source files match `0a9af0da5` exactly. M2 review
used one compiler referee for this coherent research artifact; no code or
executable verification was required, and zero measurements were consumed.
Task, laboratory and design-index records retain the original adequacy gate.
