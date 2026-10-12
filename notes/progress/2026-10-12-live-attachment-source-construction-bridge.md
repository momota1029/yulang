# Live attachment: source formation and payload ownership bridge

Date: 2026-10-12
Status: frozen, independently reviewed research handoff; H and complete Call OPEN
Claim class: bounded static constructor/consumer characterization
Y3 assigned baseline: `06430602372f7c94ca8cba362fd360a728388ffa`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; complementary researcher leaf

## 1. Objective, authority and exact conclusion

Locate any real source-owned identity or payload before
`candidate_signature_view -> source_weight` that could already supply the
required live contextual attachment. This is a static ownership audit distinct
from the reviewed conditional fresh-map lemma in
[the live-attachment proof](../theory/2026-10-12-live-attachment-call-residual-proof.md)
§3. That lemma is an input, not reproved here.

Governing sections: [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, especially set-wide identity/member ordinals in §3.1;
[residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md),
“Selected policy” and “Preserved contract and open obligations”;
[inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§2. The index was used only as a locator.

Accepted meanings remain composed-negative local subtraction, composed-positive
concrete allowance, connected symbolic variables, one attachment identity per
exact annotation set/fresh instance, independent member ordinals, and distinct
residual constructor lineage. The withdrawn callback result supplies no oracle.
No concrete-formal admission or new language meaning is selected. Necessary
safe nonpublication remains; exhaustive internal rollback is not imposed.

**Conclusion in the inspected cone:** source formation already retains the
exact immutable row occurrence and resolved payload needed to *construct* an
attachment. It contains no pre-existing live concrete attachment handle or
operation. An actual earlier `AttachmentBundleId` constructor exists for
composed-negative **empty** rows, but it carries inert provenance only.
The first set payload for supported concrete annotation views is the
`LocalWeightId` allocated by `source_weight`; its executable words are empty.
Thus “no earlier identity” is too strong, and “a payload field is first lost at
signature-view formation” is unsupported: there is no live attachment to lose
in the preceding typed source data. The missing producer is the owning
annotation-to-live-operation transition at this seam, together with its actual
source/Call/output incidence. Equal support or allowance endpoints cannot
supply it.

Hypotheses for constructor facts: exact source bytes in §6, valid branded input
handles, one live private session, and normal completion of the listed fallible
calls without allocation exhaustion. No source admission, complete capture,
activation, replay completion, output subtraction or residual theorem is assumed.
This is neither a source-program counterexample nor a general absence theorem.

## 2. Finite source formation cone

| Owner / inspected route | Retained identity and data | Attachment boundary |
| --- | --- | --- |
| `yu-syntax/src/full_parse.rs:72–101` | `SourceNodeKey` retains parse brand, green allocation and start; clones preserve all three. | Immutable syntax identity, not a fresh attachment instance. |
| `yu-hir/src/module.rs:181–221,1390–1428` | Branded `HirOccurrenceId`, `DefinitionRootId` and actual parameter IDs; the HIR lowering event calls `local_source::form` and stores its result by definition root. | No contextual attachment field in these IDs. |
| `module/source_annotation.rs:68–94,316–378,399–574` | `SourceAnnotation {owner, position, ty}`; recursive Function argument/result types; each `SourceEffectRow {position, concrete, variables}`. `parse_row` resolves a concrete spelling to exactly one `SourceEffectId {module,declaration}`, separately retains a symbolic name, and rejects multiple names. | Typed resolved annotation data, no solver view, attachment ID, context word or Call witness. Group/arrow parsing moves the same retained row/tree data. |
| `module/local_source.rs:16–173,289–329,375–389,506–525,730–788` | Definition annotation, local-binding annotation, actual parameter annotation and expression Ascription; parameter/local IDs and lexical scope remain distinct from annotation owner. Local formation records local parameter ownership. | Annotation clone/move preserves source identities; no live payload is minted by these records. |
| `candidate_source.rs:83–133,169–201,274–282,317–324,413–434,479–490` | Four action routes: FormalAnnotation, LocalAnnotation, Ascription, definition Annotation. Actions retain `Arc<SourceAnnotation>` plus actual parameter/slot or endpoint, occurrence, level and applicable scope. Formal registration is separately owned by the Lambda. | Actions carry no attachment handle. Composed-negative concrete rows are rejected by preflight; a successful general annotation action does not establish negative admission. |
| `candidate_source.rs:649–683` | Normal/local stage dispatches the corresponding constructors; local annotation construction precedes local publication. | Dispatch is real, but does not establish successful execution or publication. |

The alternate shadow identities were also inspected at
`yu-hir/src/shadow.rs:1038–1045,1077–1147`: `AnnotationId` and
`AnnotationOccurrence` retain an artifact-local syntax incidence whose
correspondence is `PendingTypedPortAndProfile`. They are explicitly distinct
from typed permission/owner evidence. No constructor in the traced action route
passes this ID as a contextual attachment. This bounds the claim to that route;
it is not a whole-repository reachability theorem.

## 3. Exact solver seam and the earlier empty-set constructor

`SignatureContext::Annotation` (`candidate_effect.rs:154–163`) borrows the
resolved annotation and owns an `AnnotationScope`; it adds no payload handle.
Formal construction (`1034–1111`) starts Negative and retains the actual
parameter domain. Its concrete-negative guard is independent of preflight.
The permitted positive formal-port case calls `candidate_signature_effect`
twice with one position-keyed view map, preserving source variance separately
from endpoint polarity.

Definition/ascription routes use `candidate_annotation_pair:1184–1279`;
local initialization uses `construct_candidate_local_annotation:1125–1178`.
They retain the same annotation/scope through paired signature construction and
computation checking. Function recursion at `1392–1444` flips variance on
argument descent and preserves it on result descent. `candidate_signature_effect`
at `1447–1576` checks the concrete-negative guard before making a concrete view,
preserves symbolic coordinates via `(AnnotationScope,name)`, and keys the
per-action view map by the exact `row.position`. The scoped variable allocator
at `979–997` retains the named connection, not a concrete grant.

There is a real pre-view constructor that an absence claim must include:
`candidate_negative_empty_bundle:1280–1313` traverses the retained annotation,
collects composed-negative rows with **both** concrete and variable lists empty,
and constructs `EmptyAttachmentSet {owner,row.position,AttachmentSource}`.
`retain_bundle:2097–2111` allocates `AttachmentBundleId` with a constraint
occurrence anchor. One bundle can contain several such empty-set occurrences;
its ID is not a set-wide concrete attachment identity. `candidate_context.rs:141–156`
explicitly separates these identities from relation keys, context expressions,
executable views and endpoint comparison. This is source-owned inert provenance,
not the missing operation or a certificate for nonempty negative rows. The
formal route does not invoke this empty-bundle constructor.

For a supported explicit positive annotation row, `candidate_signature_effect`
at `1540–1563` forwards owner, exact row position, cloned concrete members,
actual tail, source variance and lexical scope into `candidate_signature_view`.
The ephemeral `AttachmentSource` contains only polarity/scope, no identity.
`candidate_signature_view:733–774` allocates a view index and asks
`source_weight:2174–2196` to allocate the payload. That `LocalWeightId` is the
set identity: `LocalWeight` owns members, owner and row position;
`AttachmentSet` owns polarity, scope and ordinals `0..allowed.len()`.
The boundary number is this view index; it is not the source position.
`SourceUnitPush` is prepared only for positive nonempty sets and is dormant.
`left_word` and `right_pops` are structurally `[();0]`. No earlier constructor
in §2 supplies an executable operation to this allocation.

All `candidate_signature_view` call sites in this file were accounted for:
test-only helper `731`, copy `829`, operation-family `1463`, omitted-row `1484`,
and explicit-row `1549`. Operation provenance uses `SourceOperationDeclaration`
and does not allocate a source weight. A closed omitted annotation view can own
a zero-word payload without `AttachmentSet`; an open explicit annotation view
retains source payload but has no `closed_weight`. Therefore Support/Allowance
view identity alone never proves an attachment payload exists.

## 4. Directly inspected forwarding, copy and replay consumers

For source annotation data, HIR derives `Clone`; action construction clones the
annotation and branded IDs, and signature recursion borrows them. Original
source IDs survive these copies. That is not fresh-use attachment independence.

For earlier empty bundles, `candidate_context_seed:2515–2523` anchors annotation
slots 40/41 to 41 and ascription slots 45/46 to 46. `bundle_link:2138–2162`
preserves the same bundle ID over retained diagnostic edges and selected
Extrusion/ParentCopy/EqualityCanonicalization transport edges. `dependency`
at `2300–2334` links Derived/FunctionPort and both Replay parents through
`edge`, whose `2376` call forwards bundles; selected late transport edges are
also retained. This is provenance forwarding, not contextual execution.
Capture at `candidate_scheme.rs:784–801` enumerates bundle incidences only on
the bounds it actually retained. Fresh preparation at `1021–1034` clones each
captured bundle once per old ID, allocates a **new** bundle ID and retains the
original occurrence/set metadata. Restoration at `1257–1261` links that mapped
bundle to the fresh relation through `candidate_context_fresh_bundle:3157–3162`.
No all-path capture theorem follows. The separate transport helper at
`3164–3173` has no discovered caller in the searched scheme/extrusion/intrusion
files and is marked unused; its existence does not prove activation.

For concrete payloads, `candidate_copy_effect_view:806–830` validates any source
weight, retrieves its polarity/scope and clones owner, position and members;
then it calls `candidate_signature_view`, allocating a new payload when that
constructor's conditions hold. Original row position is preserved; payload ID
is replaced. The existing reviewed fresh-map result describes same-key reuse
within one use and remains conditional on a source payload being present.
This audit does not rederive it or infer a live operation from it.

`candidate_context_source:2483–2501` seeds only a **closed Allowance** payload
as `PrefixLeft(weight,IDENTITY)`. This supplies the zero-word filter, not a
PUSH. `candidate_check_effect_operand:888–958` expands Support into member
endpoints and its actual tail; an unmatched concrete member forwards the
**same lower endpoint** to the Allowance's tail. Matching members succeed as
allowances. `materialize_unit_push:2200–2215` is explicitly detached and
installs no live relation, bound, registration or operation. The inspected
constructors therefore do not join the retained source ID/payload to a live
contribution/Call/output attachment or a residual recipe.

## 5. Oracle comparison, independence and recommended action

Direct reads of Oracle `annotation/constraints.rs:363–390,424–470,657–690`
and `lowering/expr/lambda.rs:919–944` match the pinned blob IDs in the reviewed
[transfer audit](2026-10-12-oracle-effect-source-transfer-audit.md) §8.
The authentic paired annotation constructor allocates a fresh `SubtractId`
for the entire resolved nonempty set, emits a positive stack weight and negative
filter, and returns `AnnEffectBounds.subtracts`. The Function owner retains that
immediate result predicate in `AnnValueBounds.output_subtracts` and wraps the
returned Value. Parameter-local formation copies those actual predicate
weights into `LocalBinding.call_predicate_subtracts` and records their frame.
This is a real retained operational payload before later call processing,
unlike Y3's resolved HIR data and dormant marker. Descendant Function predicates
are not all returned as the enclosing Function's immediate predicate.

The direct Call/frame-output route is taken **only** from the reviewed pinned
transfer audit §3, not the Oracle working `tail.rs`: its observed blob hash is
`f2b05c8d967f5e285299229e4d09aa2b8e330de6`, different from pinned
`8289bfdc6a17b2469ae168ac7939d34813fda474`. Its initially read line windows were
discarded as evidence. The existing audit supplies the bounded same-ID direct
formal-call/output pairing with its whole-callable wildcard guard and other
hypotheses. No one-pop or generalized instantiation law is assumed here.
Oracle evidence is separate historical implementation evidence; agreement
does not prove global H, every copy/export route, or Y3 source semantics.

One next authorized action: have the primary pin a bounded source-construction
packet at `candidate_signature_effect -> candidate_signature_view/source_weight`
that supplies the actual live operation and its source/Call/output incidence,
using the retained owner, row key, scope, resolved members and binder inputs.
Require the coupled invariant and fresh independent review before dependent
admission implementation. This observation does not require a new HIR semantic
identity or authorize a patch; representation and implementation remain with
their responsible owners. H, complete Call and production gates remain OPEN.

## 6. Checks, coverage, resources and dependency snapshot

Static commands: `cat`, `sed -n`, `rg -n`, `rg --files`, `sha256sum`; Python only
read bytes to compute Git-blob SHA-1 and later document-integrity checks.
No Git command/mutation, compiler/Oracle execution, test, build, probe,
benchmark, delegation or user contact. Seeds/ranges/mutations: inapplicable;
the finite envelope is the named constructor windows/call-site searches above.
Some combined output was truncated; decisive source windows and governing
attachment/lineage sections were reread separately. Two guessed identity-file
paths did not exist; the actual definitions were found in `shadow.rs`,
`module.rs` and `full_parse.rs`. No failed search is interpreted as absence.

Only this leased note changed. Source/dependency hashes below were read from
the working files; no dependency was written. Y3 baseline equality remains for
the primary to validate without relaxing this leaf's no-Git packet. The four
solver-file hashes agree with the reviewed live-attachment proof snapshot.
Oracle constructor/predicate blob identity was checked independently of the
worktree ref. Static wall-time budget: at most 20 minutes; elapsed/CPU/RSS were
not instrumented. One foreground lightweight command at a time, except initial
small parallel static reads; zero heavy processes and measurement samples.

Requested role: complementary `researcher`; packet supplied no explicit
model/effort override. Configuration requests GPT-6.1 Sol/high for unpinned
children, and `researcher.toml` contains no model/effort pin. Observed assignment
identity: `/root/live_attachment_source_formation_bridge`; effective runtime
model/effort unknown. No role switch, Astra execution or independent review of
this output is claimed.

Unverified: source acceptance/completion; all alternate parser/HIR routes;
parameterized effect operands; all capture/transport/export paths; actual
Call/provider completeness; current/future activation and drain; output POP,
residual gamma/feedback and lineage; lifecycle/publication; global H,
soundness, principality, termination and F5 cutover. The complete Call route
and output owner are not reaudited by this packet.

```text
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8  crates/yu-syntax/src/full_parse.rs
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5  crates/yu-hir/src/module.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc  crates/yu-hir/src/shadow.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
efafd2a067a2b7db708f85237eb0ac377398c1aa042dc67772622acd87ddf27a  notes/theory/2026-10-12-live-attachment-call-residual-proof.md
f222d83d51af22f26b786bad6bc07d27a2b2fb5b97e0dadbada9159d667bbb32  notes/progress/2026-10-12-oracle-effect-source-transfer-audit.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
```

Verified Oracle blob IDs: `annotation/constraints.rs`
`d2cf0e18266233c1e3c2943448244ee2a3499529`; `lowering/expr/lambda.rs`
`724b103cda8b4e2c457aacf0a674372fb191e3d6`. Their observed SHA-256 values are
respectively `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db`
and `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9`.

## Commit packet

- Exact frozen lease: `notes/progress/2026-10-12-live-attachment-source-construction-bridge.md`.
- Baseline: Y3 `06430602372f7c94ca8cba362fd360a728388ffa`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency changes: none written; source hashes above; Y3 baseline equality awaits primary validation. Oracle working `tail.rs` differs and is intentionally excluded from pinned evidence.
- Claim/review: bounded static source characterization; fresh independent `spec_auditor` PASS with no findings; no parent gate closure. Reviewer identity: `/root/live_attachment_bridge_review`; effective model/effort unknown.
- Checks already run: constructor/call-site static reads, SHA-256 snapshot and Oracle blob-identity comparison; all seven local links exist, no trailing whitespace, and all 16 recorded Y3/document dependency hashes remained unchanged at freeze. Zero tests/builds/runtime probes.
- Proposed message: `research: trace source identity and dormant attachment payload formation`.
- Shared-record deltas left for primary/curator: record the source-data / inert empty-bundle / concrete payload distinctions and exact live-operation producer gap; retain H and complete Call OPEN. No shared task/index/authority/theory-status file was edited.
