# Original source environment: raw identities, decorated folds and admission

## Result and boundary

[`OriginalSourceEnvironment.lean`](lean/YulangClosure/OriginalSourceEnvironment.lean)
constructs a heterogeneous payload for the accepted source rule program and
an ordered interpretation of its complete frame prefix. Actual event identity
is separated from logical description/evidence. Publication readback retains
the actual entry state, completed retained state and captures separately.
An actual native Received/Receipt constructor supplies a source invocation
candidate, and the original Function checking constructor transports its
observation child's complete positive obligation at that same candidate.

The new source applications use the entire decoded environment for literal
and ordinary value-formal Name clauses. They no longer read only the unchanged
`Environment.root` assignment when the source is inside later frames.

This is not a completed interpretation of every original Kernel field, a
completed semantic induction over `Checking`, or original/native inference
soundness. In particular, the actual original view/event field readback,
primitive/structural checking cases, target Function guards and captured
certificates remain genuine requirements. They are identified below at their
exact declarations, rather than packaged as a whole source-typing atom.

The packet began at `ee61ba0b68789e2dea9eac024130f21c5a4e6453` and pins the
accepted Interpretation source
`feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`, published at
`8622f29d2c1b8934f8b257574c4b6b0e3db5ca42`. Syntax and Generation are unchanged.
The concurrently published SourceSignatureConstruction module was inspected
read-only; its static provenance result does not itself supply semantic view
readback, so it was not added as a dependency. No new mutable project snapshot
was imported.

## Governing source distinction

The ownership split comes from
[`source-generalize-definition-and-proof`](2026-10-08-source-generalize-definition-and-proof.md)
§3.3, selected by the source Generalize definition. Its actual `Executed`,
`OneShot`, `Shared`, `EventField`, `ViewLogic`, and `EventProof` records have
different owners and dependency telescopes. A proof about an execution cannot
change its actual fields. These records are proof/compiler construction data,
not new runtime tags.

The interpreted semantic tuple and complete independent challenge/observation
relations are the selected ones from
[`contextual-function-membership-definition`](../design/2026-10-08-contextual-function-membership-definition.md)
§§2–3 and the accepted
[`original-source-interpretation`](2026-10-26-original-source-interpretation.md).
Its simultaneous operator retains original `nu/K/D`, assignments, live current
configuration, witnesses, scope, authority, incidences, dictionary, every
actual provider decomposition, and every independently admitted complete
challenge and raw observation.

The existing source environment already constructs original event keys from
origin, actual parent path, owning source binder, occurrence and actual payload.
It preserves initializer entry snapshots, separate completed replay history,
and aliases. The task here is to give those operations a useful heterogeneous
data interpretation without putting an entire logical assignment or decorated
semantic `Event` into the runtime payload.

## The six concrete maps

### 1. Fixed root assignment and distinct endpoints

`Root` contains the original `SourceAssignment`, computation-interface and
carrier maps, a logical interpretation of actual view tokens, installed
object data, and the immutable source-owned `CallOwner` registry. The assignment retains separate source `Endpoint` ports;
synthesis, final root, written target, descriptor, callable image, returned
value, formal carrier, body consumer, invocation return, branch join,
pattern input and reference content are not identified.

`Root.decoded` initializes the full decoder. A `.root` payload is not admitted
as a source binder value. The original source operations keep the root fixed;
later data is read from ordered frames. This is still a proof-side assignment
carrier: actual identification of its opaque semantic sorts with the native
original model is a separate source-field map, not an assertion made by its
record constructors.

### R1 repair: actual callable subject versus checked descriptor

Independent review found a material source-correspondence defect in the
compiler-successful `fcb6c1f5…` snapshot. Its `Decoded.callRow` read the value
and root at `(binder.site, finalRoot)`. The unchanged original App rule in
[`OriginalSourceGeneration.sourceRules`](lean/YulangClosure/OriginalSourceGeneration.lean)
generates the value goal `callee.returnedValue ≤ app.descriptor`. For
`(lambda x. x) Unit`, the old readout could therefore select the Unit result
instead of the closure that is actually invoked.

The repair retains source-owned incidence as ordinary static data:

| Declaration | Source-owned construction |
| --- | --- |
| `CallOwner.application` | Original App site/context and callee/argument sites. Its subject is the callee's `returnedValue`; its initial goal is the exact original App value goal. |
| `CallOwner.closure` | Original Lambda site/context and formal/pattern/body sites. Its subject is the closure's own `finalRoot`. |
| `localCallOwner` | Reads the unchanged `sourceCallIncidence` and `closureFormation` atoms emitted by the source builder. It consults no solved descriptor or safety predicate. |
| `callOwners`, `forestCallOwners` | Traverse every rule-tree/forest constructor, including annotation and source event/publication wrappers. |
| `sourceCallOwners`, `Root.withSource` | Apply that registration to the accepted builder on the raw original source. They do not accept a supplied successful judgment. |
| `Decoded.callOwner`, `Decoded.callSubject` | Read the same immutable source registry at the owning invocation site. |
| `Decoded.callRow` | Reads callable value and root from that actual subject, and the original source binder's descriptor slot separately. |
| `Decoded.goalRow` | Keeps the same actual value, root and event while selecting the current checking goal's upper descriptor. |

`source_app_value_incidence` proves membership of the actual original App
value goal in its generated local premises. `source_app_call_owner`,
`registered_app_subject`, and `registered_app_callable` connect that source
construction to the endpoint and its value/root readout. The corresponding
Lambda roots prove that the genuine closure case retains its own `finalRoot`.
The source traversal covers all raw grammar containers; the registered owner
classes proved here are App and Lambda. This does not claim that every other
source/client value-check occurrence already has its remaining authentic
subject interpretation.

The complete decoder and its raw `Actual` projection retain `callOwners`.
`decoded_call_owners` proves that every frame class preserves this registry;
`logical_preserves_callable_owner` also proves the resulting value/root
readouts are unaffected by logical redecoration. Publication restoration and
aliases continue to use their original entry/completed frame prefixes. The
registry is not inserted into `Runtime`, and no checked descriptor is inserted
into `EventStep.data` or an anchor key.

`DataAdmitted` selects its value/root using `callRow`. An admitted invocation's
observation capture reads the same raw operands, as proved by
`admitted_invocation_captures_subject`. No anchor filter, alternative provider,
new target-domain restriction or extra runtime tag is introduced.

The total `callSubject` function has an absent-owner fallback for provisional
data. That fallback is not an original incidence theorem. `FunctionShape`
requires the actual registered owner, and the App/Lambda applications construct
it from source registration. No source correspondence is claimed for an
unregistered fallback or for an arbitrary caller-written registry.

`FunctionShape` now retains the registered owner, original site/context,
mode and child incidence, and Function classifications. It does **not** equate
the immutable subject with `goal.lower`, nor equate the original descriptor
slot with every `goal.upper`. `function_shape_for_registered_owner` constructs
this shape for arbitrary lower/upper descriptor endpoints at the same source
occurrence. `goal_row_same_subject` retains the subject as those descriptors
change, including through ordinary composition.

The unchanged `Kernel.admitted` interface receives environment, binder and
candidate, not a `CheckGoal`. Its existing source invocation telescope still
uses the original binder descriptor. Consequently the local semantic
`function_checking_constructor` now carries the explicit `targetReadback`
equation outside `FunctionShape`, and concludes membership at `goalRow`.
Authentic telescope/domain alignment for an arbitrary intermediate target is
still open. This repair does not repurpose `Binder.arity`, encode descriptors
in raw identity, quantify over a newly enlarged domain, or silently assume
that all intermediate domains coincide.

### 2. Description and logical evidence

`LogicalKind` has precisely the original description-owned classes used here:
`description`, `viewLogic`, `publishedInstance`, and `eventProof`. `Logical`
contains descriptor/interface updates, logical interpretation of actual view
tokens, `eta`, and the joint witness. It cannot overwrite actual endpoint
values/roots, carriers, bindings, installed object data, history or current
configuration.

`Decoded.logical` performs those explicit updates. `logical_preserves_actual_fields`
and `actual_logical` prove preservation of the actual fields. The original
binder kind, site, arity, entry path and occurrence remain in the surrounding
source frame; this construction does not infer ownership from the solved type.

`logical_extension_keeps_actual_path`, `logical_extension_keeps_anchor`, and
`two_descriptions_one_runtime_key` prove that arbitrary description/evidence
changes cannot replace the original actual-event path or Shared anchor. The
result does not rely on a chosen constant strategy or on equality of the
logical assignments.

### 3. Complete actual event payloads and decorated readout

`Runtime` has the original event classes `invocation`, `receipt`,
`returnRebind`, `response`, `rigidOperation`, and `oneShot`. Their data is
explicitly separate from `Logical` and from the semantic `Event` record.

| Runtime data | Retained original fields |
| --- | --- |
| `Invocation` | Raw history/current configuration; actual callable/root; context and continuation; complete carrier/root; actual view token; receipt, typed path, consumer and incidence. |
| `ReceiptData` | Complete original receipt, actual view token, typed path, consumer, incidence and actual following history/configuration. |
| `Outcome` | The whole raw observation, optional actual returned value/carrier/root, actual following history/configuration, actual endpoint-object updates and binding updates. A pending outcome is allowed; eventual Return is not required. |
| `ResponseData` | Whole raw response observation and its complete original receipt data. |
| `RigidData` | Original declaration identity, rigid packet arity, whole raw packet and actual following history/configuration. The packet's authentic typed interpretation remains its original local contract. |

The actual view token has its own parameter type `View`. It is not identified
with `s.Interface`. The semantic interpretation `View → Interface` lives in
the logical environment. Thus two descriptions can interpret one actual token
differently while the original runtime key remains unchanged.

`Invocation.decorate` supplies the raw incoming history/current configuration
to a semantic decoration. `Invocation.challenge` reconstructs all original
challenge operands. `encodeInvocation`, `decode_encode_challenge`, and
`encode_decode_invocation` give exact round trips, with the original view
presentation equation stated explicitly. `invocation_redecoration` proves that
semantic description/event decoration does not replace the raw operands or
token. `distinct_runtime_payloads` proves that different raw candidates remain
different at the same source occurrence.

`RuntimeReadout` exposes every remaining opaque event-field readout separately.
Each field map receives the exact prior fixed frame prefix as well as the
prior decorated event, current owning binder and raw runtime data. The prefix
retains Shared witness data and its original binder/entry-path metadata; it is
not a list of freshly chosen logical descriptions.

| Semantic Event field | Computed source |
| --- | --- |
| `fiber` (`nu/K/D`, source graph, binder tree) | Preserved from the one original root/event fiber. |
| `eta0` | Preserved from the original assignment. |
| `eta` | Explicit original runtime-field assignment readout. |
| `history`, `current` | Actual runtime payload's `Current` data. |
| `witness` | Explicit original joint-witness readout. |
| `scope` | Explicit original scope/dependency readout. |
| `authority` | Explicit actual authority readout. |
| `incidence` | Explicit original whole-tuple incidence readout. |
| `dictionary` | Explicit original dictionary readout. |

These are data maps. None returns a source derivation, a recursive membership
proof, a successful body, or solver success. No resulting decorated `Event`
is inserted into `Runtime`, `EventStep.data`, or `AnchorKey`. The actual
definitions of the opaque field maps remain to be identified at their source
owners; declaring them as data maps does not prove that arbitrary maps have
the original meaning.

An early provisional fold would have left a future invocation at its closure's
creation configuration after publication restore. The implemented correction
puts raw current history/configuration in `Invocation` itself.
`invocation_uses_incoming_current` proves that the later actual invocation
supplies its own state. Its decorated semantic input is assembled from those
actual fields and the original readouts. No captured maker activation is
treated as the current caller merely because source replay restored its prefix.

### 4. Original Shared data

`Shared` retains the actual binding-address updates, installed value/carrier
tuples and witness value at its original source binder. `Decoded.shared`
records their object projections, while `decodeFrame` retains the entire
original Shared frame in `Decoded.fixedFrames` and `Actual.fixedFrames`.
Subsequent runtime readouts receive that exact prefix. The underlying source environment's
one anchor map and original raw event key select this data across descriptions;
description frames cannot replace that map or key.

`shared_frame_retains_whole_witness` exposes the full retained field, not only
its installed-cell projection. `logical_preserves_fixed_prefix` proves that
logical redecoration cannot alter it. `decoded_fixed_prefix` proves the ordered
fold law, and `retains_original_fixed_class` plus
`decoded_original_fixed_prefix` identify the retained frames with the original
`Binder.isFixed` prefix for every correctly classified source frame.

This does not move Shared above its initializer's actual response/return
dependencies. Generation's existing `initializerE`, `returnRebind`, `sharedE`
and continuation scopes are unchanged. A new actual invocation has its own
raw parent/event/occurrence/payload, while two descriptions of the same actual
event reuse the same anchor.

### 5. Full ordered fold, publication and aliases

`decodeFrame` interprets each heterogeneous frame. `decode` folds the complete
ordered frame list from `Root.decoded`. It does not skip to the last logical
assignment or read only the original root. Actual endpoint changes, binding
changes, installed objects, current-state changes, descriptor updates and
view interpretations all occur in their original order.

The decoder also retains the most recent invocation's decorated input and
its separate raw payload for checking the corresponding observation child.
These are source-checking input records. Their presence is not an assertion
that a native invocation owner is still active; native lifetime/authority
comes from the actual current configuration and its original guards.

`Actual`, `actualFrame`, and `actual_frames` compute a separate actual-data
projection of the entire fold. `fold_actual_independent_of_readout` proves that
logical readout choices cannot retroactively change actual values/roots,
carriers, installed object data, current history/configuration or raw invocation
input. This proof covers all Runtime constructors, not only the invocation case.

`Payload.atKind`, `data_admitted_has_original_field_kind`, and
`admission_preserves_typed_frames` establish the source field-class invariant.
For typed frames, `nonfixed_typed_frame_is_logical` identifies exactly the
nonfixed caller frames retained during publication restoration.

`restore_decodes_actual_entry` uses the accepted source operation:

```text
entryFrames ++ caller's nonfixed description/evidence frames
```

It proves that this decodes the publication's actual entry state. Completed
publication `fixedFrames` are kept separately as replay lookup history. They are not
preloaded as an execution prefix and then appended again. `entryNames` are
restored independently from completed `captures`.

`restore_retains_entry_witness_prefix` separately proves that the decoded
Shared/runtime prefix after restore is the original entry prefix, rather than
the completed initializer's later fields. Replaying an original fixed event
then appends its actual frame once through the ordinary fold.

`publicationData` computes both the actual entry and completed retained state,
plus original captures and identity. `publication_data_matches_fold` relates
these projections to the full decorated fold for every readout map.
`published` is a raw readback of the existing publication registry; it is not
a substitute for the source publication validity/lookup checks.

`alias_preserves_complete_publication` and
`alias_preserves_publication_observers` preserve the whole publication object
projection, including installed tuples, captures and creation/completion state.
They do not establish alias agreement merely by comparing name strings.
`decode_alias` also proves that aliasing does not mutate the current decoded
state. The accepted source publication construction and replay validation
remain unchanged.

### 6. Original admission correspondence

`DataAdmitted` handles the original field classes separately. Invocation uses
the complete unchanged `CheckedDomain` at the reconstructed actual callable,
root and decorated incoming event. It retains actual receipt/path/consumer/
incidence and the interpreted original token. The other field classes use
explicit `LocalAdmissions` inputs for their original local source contracts;
they are not defined by Function/body membership or final query success.

`Admitted` adds the actual source parent-path equation and decoding of the
current environment. It does not test membership in the anchor or publication
maps. `admission_ignores_stored_maps` proves that replacing either stored map
does not change the admission relation.

`admitted_scoped_iff` is the exact scoped/data correspondence at every
occurrence. `admission_recovers_challenge` recovers the full admitted semantic
challenge from a source candidate. In the other direction,
`original_challenge_supplies_admission` constructs a source candidate for each
original admitted challenge at every occurrence, given its actual registered
view presentation and event-field readback.

Those two readback equations are material. The theorem does not assert that
an arbitrary `View → Interface` map represents every original admitted view,
or that an arbitrary `RuntimeReadout` reconstructs every original decorated
event. Original checked incidence must supply the actual carrier/receipt's
view token and semantic equation, and the original field construction must
supply the event equation. Restricting the original domain to whatever a map
happens to represent would change the claim and is not done here.

The native application is concrete at its actual owner:

- `nativeReceiptSorts` retains the full original receipt with owner, view,
  source site and formal identity.
- `nativeInvocation` reads `Received.value` and the actual `Received.view`
  token while retaining that complete receipt.
- `native_receipt_token_owned` uses the actual `Receiving.record` constructor.
- `native_received_encoding` proves equality with the complete challenge's
  raw encoding.
- `native_received_supplies_admission` constructs the source candidate and
  the actual stored owned receipt. Its semantic view/event readback equations
  remain explicit; token equality alone is not semantic surjectivity.

## Application to original source and finite Function checking

`foldedLiteralKernel` and `foldedNameKernel` interpret their exact local source
atoms using `decode`. The predicates contain raw primitive/lookup relations,
not `Meaning`, `Satisfies`, or a desired whole source derivation.

`folded_generated_literal_membership` and `folded_generated_name_membership`
invoke the accepted raw-source reconstruction theorem before interpreting
the local source rule. `folded_name_constraints_from_binding` constructs the
actual generated Name constraints from the decoded raw binding and installed
tuple. The full current-world certificate needed for Name membership remains
an actual premise, as required by the selected world clause; it is not supplied
by the bare frame fold.

`FunctionShape` identifies the value/domain/observation modes, original binder
kind and owner, contravariant domain endpoints, observation endpoints,
contexts, decoded source-owned callable incidence, and genuine Function classification. It
contains no domain inclusion, output inclusion, body certificate or whole
source-typing predicate.

`functionKernel` installs this shape and the explicit admission relation while
retaining the other original Kernel fields. `DomainMeaning` interprets the
domain child on full original challenges. `ObservationMeaning` interprets the
observation child on the captured full actual input and every raw observation.
It uses the accepted descriptor-indexed `ObservationMem inputs Z` throughout.
It does not reuse one unchanged trace certificate under two different checked
result descriptions.

`observation_child_transport` constructs the actual scoped candidate, derives
its admission, computes the extended environment, and applies the observation
child at exactly that candidate. The readback equalities recover the same
complete original challenge, and the child's entire `P_A[Z]` obligation is
transported to `P_F[Z]`.

`function_checking_constructor` constructs both the actual original
`Checking.function` derivation and the same-provider semantic constructor
step. Both original recursive Checking children remain in the derivation.
The domain/observation semantic hypotheses are the explicit recursive
induction hypotheses, not laws hidden in `FunctionShape`. Target
`functionGuards` and `capturedFields` remain genuine requirements. The shape
does not eliminate them, nor are they consequences of matching scalar ports.

### No arbitrary-candidate checking closure is claimed

The distinction in
[`source-check-positive-transport-proof`](2026-10-13-source-check-positive-transport-proof.md)
§§3–4 applies directly. Ordinary L3 inclusion at completed `Meaning` does not
automatically give an action on an arbitrary provisional family `Z`. A
positive returned-value field can require a target `Z.V` tuple that is absent
even when the corresponding completed-semantic inclusion holds.

The new Function theorem is therefore a constructor step conditional on the
actual child actions at `Z`. It is not a completed Checking induction, a
candidate-closure theorem, or recursive introduction. The next checking route
needs a genuinely constructed proof-directed transport/closure and its
compatibility with the actual positive operator, while direct conversions
remain separate. No same-`Z` closure is assumed here.

There is also a concrete scope precondition for a future full Checking theorem.
`Checking.identity` permits any environment and mode, whereas
`ObservationMeaning` is false when there is no recorded invocation input.
Consequently an unconditional `Checking → ObservationMeaning` statement would
be wrong even for identity. The full theorem must be indexed by an actual
decoded, mode-admissible generated occurrence and derive observation-input
scope from that original telescope. The constructor proved here explicitly
opens and decodes the invocation before using its observation child.

No naive up-to condition such as `U(Phi S) ≤ Phi(U S)`, nor membership plus a
one-step closure assumption, is established or used by this packet. Union
elimination and transparent recursive equation unfolding must retain their
actual proof obligations. L4 recursive introduction remains open. At completed
`Meaning`, its proved `meaning_iff` is available; it cannot be silently applied
to an arbitrary provisional family.

## Exact remaining owners

| Remaining fact | Why it is still required |
| --- | --- |
| Semantic view registration | `Received.view`/`Receipt.view` gives the actual token. The original registry must establish its complete `Interface` interpretation for each original checked incidence. |
| Runtime event-field readback | The six opaque `RuntimeReadout` fields must be the actual `eta`, witness, scope, authority, incidence and dictionary actions at the owning source event. The raw fold preserves fields but cannot invent their interpretation. |
| Other source-field admissions | `LocalAdmissions` must use authentic original primitive/entry/response/rigid/Shared rules with their complete telescopes; arbitrary supplied predicates are not certified original inputs. |
| Function child actions and target guards/captures | The actual primitive/structural/source checking derivations must supply these at the required family. They are explicit in `function_checking_constructor`. |
| Intermediate checking target alignment | The original binder's independent domain must align with the current checked descriptor. `targetReadback` is an explicit local application premise, not a general field of `FunctionShape`. Other authentic source/client subject owners also remain to be interpreted; App/Lambda registration does not close them. |
| Original later-event relation | Carrying the actual later history/configuration does not prove original compatible-future or lifetime laws. Their source-owned relation and full typed incidence remain required; the Function constructor does not discharge them. |
| Actual installed-world interpretation | Decoded object/alias readback does not itself establish complete `PhiW`, source/native registry agreement, or valid mutable State transitions. |
| Full source/native correspondence | The remaining source atom meanings, whole Call, optional records/methods, rigid operation hygiene, effects/handlers, recursive introduction, native generated satisfaction and SameScoped remain in the original parent goal. |

The Shared-prefix access is constructed here; a later joint-witness action no
longer has to recover newly introduced Shared data from an opaque prior Event
that omitted it. The remaining original field map must use those actual data
correctly, including every dependency and registered shared position.

These are concrete source-owner and proof-construction obligations. Their
presence is not a claim that parametric original soundness is impossible or
that the language must reject those forms. The accepted full source grammar
and its existing rules are unchanged. No W/Z grammar or State policy was
chosen by this packet.

## Verification and immutable evidence

The packet uses one owned cache/TMPDIR and only pinned accepted input modules.
Each focused invocation uses the authorized Lean 4.35.0 toolchain, one thread,
`-j1 -M1024`, and a 120-second timeout. The initial stage consumed 15 calls
from cap24. The independently requested R1 repair received a supplemental
1800-second/12-call bound and consumed 7 calls, numbered16–22. Total consumed:
22. No Git, children, shared import edits, native/runtime edits,
dependency/configuration changes or expected-output changes were made.

Checks01–15 and their original logs remain unchanged. Check11 was an audit
fixture failure, including rejection of its error-generated probe placeholders;
its failed source is retained. Check12's successful source
`3b89f37656c8163ca18ababe5565e34a60e2b14b30c7b0950288d161d3f6392d`
was superseded by the Shared-prefix repair, with its source/olean/audit/census
preserved in `superseded/shared-readout-before-repair/`.

Checks14–15 then passed source
`fcb6c1f530aa6b84aa8e0af012d0ed7a997e75034183145515c173fdcbb45ed3`
and census
`858ca5fe417aa310b69da36a87716bf5f500299e7b850a249d0b32f06020b43b`.
That successful 651-declaration/242-theorem/63-root evidence is also
**superseded** by independent review R1. Before repair, its exact source,
olean, note, inbox, audit, census, summary, input manifest, check ledger and
freeze manifest were copied to `superseded/call-subject-before-repair/`.
Neither compiler success establishes source correspondence nor the old count
identifies this final code.

Repair checks16–20 retain their actual unsuccessful diagnostics: original
source equation normalization, an invalid private numeric name spelling,
reserved/local identifier and qualified AtomKind elaboration, and one missing
payload equality in the frame induction. The final proof uses the public
`sourceRules` equations plus an explicit original App premise list. It does
not depend on private-name access or any checker bypass. Check21 compiled the
repaired module with empty diagnostics. Check22 passed the fresh full census
and all 13 concrete discriminators with no errors or warnings.

The eight earlier discriminators remain: raw event stability under logical
descriptions; independent semantic view meanings for one raw token; incoming
history/current configuration; both Bool arguments at the same occurrence;
a source-produced publication record; distinct entry/completed/future states;
Shared witness data reaching later runtime readout; and entry restoration
excluding completed Shared fields while preserving replay.

The five R1 discriminators additionally establish:

- the actual original App value premise from `sourceRules`;
- a nonconstant identity-Lambda/Unit assignment with closure value `true` and
  root7, versus Unit result `false` and root23;
- the encoded invocation retaining that closure and differing from the App
  result in both value and root;
- the genuine Lambda invocation retaining its own closure `finalRoot`;
- intermediate descriptor40 and descriptor30 retaining exactly one callable.

These are source/representation discriminators, not invented complete Yulang
semantic models. The independent primitive inputs, complete world semantics,
original guards/captures and other remaining owner relations are not proved
by the fixture.

The fresh inventory uses Lean's originating module index and includes every
private/generated declaration: **753 declarations**, **289 theorem
declarations**, and **76 public theorem roots**. Every full type and axiom
dependency is printed; all 753 begin/end pairs match. No project axiom or
`sorryAx` is accepted. The actual axiom union remains `propext`,
`Classical.choice`, and `Quot.sound`.

| Frozen R1 artifact | SHA-256 |
| --- | --- |
| `OriginalSourceEnvironment.lean` | `971f67a932a663981bc7f72eaeb818d558c4ab65ed7580057c2f0b2cfeb11f07` |
| Checked `.olean` | `5f81410b528aeea26b4fea939843195eb5d69a3ed7e3d9d01eaeaa6413f99efe` |
| `OriginalSourceEnvironmentAudit.lean` | `fb4222727dd9549fb7c2eec7cb10b6c70112a6c189c906703e49c8fa660062f7` |
| Complete check22 census | `977ca2c089ce3eb7cca11337886b56d8ed17feaea3353219d714fca84edd867f` |

Exact input hashes, all old and repair logs, both superseded successful
snapshots, summary and final manifest remain under
`/workspace/scratch/f98087c7ac1a/source-environment-r4/`. Fresh independent
review remains the acceptance gate. Full original Kernel, Checking, L4 and
native inference soundness are still open; this is a repaired constructive
packet, not their closure or an independent acceptance receipt.
