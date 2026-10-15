# Native retained Value rewrites: producer and lifecycle invariant

Date: 2026-10-16
Status: independently accepted origin/lifecycle invariant and actual source
bridge; original local native operational obligation-retention claim proved
within the existing transition laws. Source semantic parents remain OPEN.
Baseline: `8d2699197`; original native owners `bf0562382`.
Exclusive write lease: this new note only. Construction §§1–7 preceded the
implementation freeze. The primary then released the exact frozen source
snapshot for the correspondence in §§8–10; no live edits were consumed.

Primary acceptance receipt: independent semantic `checked_result_semantics`
accepts the production delta and §§8–9's native operational composition at
producer `a79926444a3e212b63e718f1f0ed653830aa073fc68b7ed17dd691058b7ac716`.
Its minor source-qualification correction is closed at
`98ec44ba2b4e3550d05bf8912edd3dff0c4ba29948eaf8855156f3f8a686649d`.
The sole major finding concerned a new test fixture's unfinished diagnostic
stage; the final fixture uses complete production drains and has CLEAN delta
review. Production hashes below did not change. Resource reviewer
`rewrite_provenance_cost` returns CLEAN; all primary focused/phase checks pass.
The primary closes only the original local native operational retention
subgate. Semantic adequacy of underlying extrusion/context laws, source MODEL,
full H2/U and global soundness/principality remain separate OPEN obligations.

## 1. Original obligation and selected operator

The [accepted responsibility finding and repair plan](../progress/2026-10-16-native-value-rewrite-provenance.md)
select a candidate-only inline
`retained_extrusion_rewrite: Option<CanonicalValuePairKey>` in each existing
Value pair memo. Diagnostic children remain independent ordinary consequences.
Authority is [contextual attachment §4](../design/2026-10-10-contextual-attachment-admission-design.md)
and the [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md).
This restores an existing consumer precondition; it selects no new semantic
rule, source restriction, solver policy or general validity generation.

The original [universal duplicate claim](2026-10-16-native-relation-duplicate-preservation.md)
remains unchanged: every necessary native consequence at a suppressed current
relation must be retained or drain-owned, with later mutation propagated or
suppression invalidated. This packet proves the narrower repair invariant:
**a selected retained replacement has genuine whole-Value extrusion origin,
and ordinary diagnostic children alone cannot select one**. It also restores
the normal admission branch for the newly encountered relation in the mixed
producer case. The construction proof alone does not prove every old
extrusion's semantic adequacy, universal duplicate redundancy, source MODEL, H2/U or principality;
§9 separately composes its actual bridge with the other native mutation cases.

Fix an actual successful candidate-mode operation sequence, original raw Value
pair K, every distinct current full relation on K, all canonical mutations,
diagnostic growth, bound restoration and route checkpoint/rollback events.
Use the selected existing copy reuse/recapture policy. A replacement is tied
to its actual stored copy graph, not freshly reconstructed from diagnostic
frontiers. Per-key uniqueness below is not uniqueness across distinct raw
keys which later share representatives.

## 2. Fully specified repair transitions

Let E(K) denote the new Option field; keep the existing children/witness/
completion fields, relation keys, context stages, queue and copy machinery.
The selected changes have these transitions:

1. **New memo:** initialize E(K)=None, regardless of diagnostic children.
2. **Canonical forwarding:** handle raw-to-current canonical redirection before
   replacement lookup. Retain its diagnostic edge normally. This is not an
   extrusion producer and does not set E on either key merely for forwarding.
3. **Retained replacement:** if E(K)=Some(W), reuse that one W before entering
   the extrusion producer. Perform authentic recapture and the current
   `candidate_context_value_rewrite(K,W)` construction, then enqueue its one
   retained child. Do not iterate diagnostic children as replacements.
4. **No replacement:** E(K)=None does not suppress ordinary dispatch. Continue
   shape/extreme/Function/ordinary bound handling as appropriate, even when
   K already has diagnostic children. The current relation still receives its
   normal bound attachment/replay when that is its ordinary transition.
5. **Genuine changed whole-Value producer:** finish the actual endpoint-copy
   computations applicable to its structural/row orientation and obtain one
   final W different from original K. Only after successful copy construction and successful current rewrite-relation
   construction may the dedicated setter publish Some(W). Retain its normal
   diagnostic edge and enqueue that exact child. A partially copied endpoint
   or a computed but unauthenticated candidate pair is insufficient.
6. **Setter:** journal the pre-update memo before mutation. None may become
   Some(W); an existing equal value may be treated idempotently; a conflicting
   value is rejected without overwriting the original replacement.
7. **Ordinary update:** replacement of diagnostic/completion data, completion
   invalidation and root reopening preserve E(K). Edge insertion/deduplication
   does not alter E(K). A new diagnostic-only memo starts with None.
8. **Checkpoint/rollback:** manual memo snapshots include E(K). Restore an old
   memo with its old Option and the same checkpoint's graph/forest state, or
   remove a newly admitted memo with the copied graph created by that route.
   No restored memo may retain a key into a graph discarded by that rollback.

These are the selected concrete transitions, not an opaque assumption of memo
soundness. The production correspondence obligation is to inspect every actual
constructor/read/update/journal/rollback site against them (§6).

## 3. Origin, uniqueness and lifecycle proof

Induct over successful transitions of §2, keeping the following invariant:

```text
E(K)=Some(W) implies
  W was the final changed whole-pair output of the genuine extrusion producer
  for K, with its copied graph retained;
  its original producer relation/context construction succeeded;
  no ordinary diagnostic producer established or replaced E(K).
```

At new allocation the implication is vacuous. Canonical forwarding, shape
checking, ordinary bound application, Function child admission and diagnostic
edge insertion do not write E; they preserve the invariant. The sole publishing
producer has completed every applicable endpoint copy and its final current
rewrite relation, so it establishes the invariant for exactly W. A failure
during endpoint copying or before that relation is constructed publishes no
Some. The actual two structural/row orientations are mutually exclusive; the
frozen code does not perform two unconditional endpoint copies. This proof
does not compose separately successful endpoint snapshots.

Once Some is live, subsequent dispatch for the same eligible raw K takes the
retained-replacement branch before the producer. Thus it cannot create a
second live replacement there. The setter additionally rejects inconsistent
publication, including any otherwise missed call path. Equal idempotent
publication does not create a second graph or a new origin. This proves at
most one replacement **per live memo K** by direct control-flow induction,
not by endpoint equality or a global registry.

Completion invalidation does not invalidate the producer's historical origin:
an actual copied graph remains an actual copied graph. The existing intrusion
generation still decides whether a relation's ordinary work must be revisited.
The new field neither certifies all semantic consequences nor introduces a
fresh generation policy. After intrusion, W can have changed representatives
or become canonically equal to K; origin retention is not a claim of perpetual
canonical inequality. Current canonical transport and recapture keep their
existing responsibilities.

Rollback has two cases. If K predated the checkpoint, its first journaled
snapshot restores its old Option; a replacement created in the failed route
cannot remain after its graph is removed. If K was new, rollback removes that
memo along with its route-created graph. If Some predated the checkpoint, its
graph also predates it and the original snapshot/forest/bound restoration
keeps that graph's identity. Manual copying must carry the Option by value,
not synthesize it from the saved children. An abandoned unsuccessful source
operation is not permitted to publish its partial state as a successful result;
no new retry or complete abnormal restoration requirement is inferred.

Publishing Some can precede the local enqueue only within the same synchronous
dispatch if the selected code does so. A successful dispatch must enqueue or
otherwise retain its exact child before yielding completion. An enqueue failure
propagates failure/route restoration. The already reviewed
[owned-drain lemma](2026-10-16-extrusion-replay-capture-completion.md) applies to
that actual queued child; the Option itself is not a drain completion receipt.

## 4. The consumer precondition and ordinary new-relation path

`candidate_context_value_rewrite` requires an actual whole-Value extrusion
rewrite. The invariant supplies its **origin** precondition when Some(W) is
read; diagnostic existence, a field=None edge or endpoint shape supplies none.
The consumer must still use the current parent relation, its post-check context,
sources/scoped flow and legitimate demand-root update, together with authentic
recapture of W's retained graph. No proof of arbitrary context transport,
global semantic equivalence or source MODEL follows solely from Some.

For E(K)=None, diagnostic growth cannot change the branch. Consider the mixed
source/action case already established in the mutation audit:

```yu
my apply (f: 'a -> int) (x: int) = {
    my first = f x;
    f x
}
```

The first Argument relation p<=a ordinary-replays Int<=a and records that
diagnostic child. It performs no changed whole-Value extrusion on K=(p,a),
so E(K) stays None. The second call has the same endpoint pair but a distinct
source relation R2; pair_is_current is false for that new relation. The new
read sees None even though the old diagnostic vector is nonempty. Hence
ordinary row application now inserts/attaches R2 at its true level-selected
bound B and runs ordinary opposite replay. Later opposite additions can use
that retained fiber through their normal writer-owned replay. Mixed ordinary
diagnostics no longer provide false authority for a whole-Value replacement.

This proves the causal repair of that branch under the selected transitions.
It makes no claim that the old example necessarily changed an observable
type outcome; x:Int could compensate scalar inclusion. The responsibility
defect and repaired bound association remain meaningful independently of an
observable separating program. The reviewed
[initialization replay theorem](2026-10-15-extrusion-initialization-replay-invariant.md)
and ordinary replay still own what their actual bound writers generate.

If a memo contains both a **genuine** Some(W) and ordinary diagnostic children,
the consumer chooses only W. It does not discard those diagnostics, relabel
them as W's parents or allocate a fresh copy graph. Their diagnostic ownership
and conflict propagation are unchanged. Thus both producer combinations are
covered without assuming a complete future-stable diagnostic frontier.

## 5. Cost and representation obligations

The Option is inline and its pair key is copied by value; no new registry,
per-memo heap allocation or variable-length replacement list is required.
Lookup and setter work are constant apart from the existing map/journal
operations. A reuse drives one retained replacement instead of D diagnostic
children, eliminating that D multiplier in recapture/relation/queue work.
Recapture's own group/source scans and normal newly required bound replay
retain their actual costs; this is not an O(1) claim for all dispatch.

The enum's physical size can grow, including Effect entries stored in the
same enum-sized HashMap buckets. Accounting must use the changed
size_of::<TypedPairMemo>() / containing-entry sizes for pair caches, journal
snapshots, resource estimates and tests. It must not charge only populated
Some values or assume only Value buckets grow. Copying the inline key adds
no nested heap capacity; existing diagnostic-edge allocation stays separate.
No timing measurement or benchmark claim is made.

## 6. Pre-freeze actual-code correspondence checklist

At the construction checkpoint the code writer was live. That pass did not read the moving
`lib.rs`, `candidate_intrusion.rs` or tests. Baseline owners below come from
the previously frozen mutation audit and its recorded native hashes; they are
locators for the forthcoming immutable delta, not certification of future code.

| Owner/path to inspect after freeze | Required evidence |
| --- | --- |
| TypedPairMemo::Value declaration and every initializer | Candidate-only Option; every fresh constructor None, including canonical diagnostic admission and all feature/test configurations. |
| `dispatch_live_item`, old lib.rs:12480–12620 | Canonical forwarding precedes lookup; Some drives exactly its W; None ignores diagnostic count and reaches normal admission; Function/shape/extreme behavior unchanged. |
| Genuine changed whole-pair branch, old :12545–12590 | Final W computed after all applicable successful endpoint-copy steps; current rewrite relation succeeds before setter; exact W retained/enqueued; no ordinary writer publishes Some. |
| Dedicated journaling setter | Memo exists and is Value; pre-update snapshot retained; no overwrite on conflict; idempotent case creates no replacement graph. |
| `record_typed_pair_admission`, old :13020–13110 | Existing-entry replacement updates diagnostic witness/completion while preserving Option, even when incoming constructor has None. New entry receives None. |
| `candidate_reopen_root` and intrusion invalidation | Completion-only changes preserve Some; generation/pair key semantics unchanged; no invented stale-certificate clearing policy. |
| `journal_candidate_memo`, old intrusion.rs:386–423 | Manual copied Value snapshot contains the Option as well as diagnostic fields; no child-derived reconstruction. |
| Memo rollback, new-pair removal, forest/bound/store restoration | Old Option restored with old copy graph; new memo removed when its new graph is removed. No dangling retained key and no leaked Some from a failed route. |
| Diagnostic insertion/deduplication and canonical edges | No setter calls; diagnostics remain retained and distinct. |
| Retained reuse current relation/recapture owner | One current contextual rewrite child, correct recapture sources, original graph reused; no assumption that Option itself proves all semantic copy laws. |
| Cache/journal/resource/accounting sites and focused tests | Changed inline enum size accounted everywhere; ordinary duplicate associations, genuine reuse, mixed diagnostics, rollback and intrusion paths covered. Primary owns executable checks. |

The final correspondence in §8 inspects the frozen source and
all constructors/matches of the changed enum. Successful tests alone cannot
replace this lifecycle correspondence. Nor does this local certificate prove
that every old extrusion/canonical map is mathematically sound.

## 7. Snapshot, status and handoff

Direct frozen research/plan inputs:

| Input | SHA-256 |
| --- | --- |
| selected repair plan | `c606cfbae01e73468c4d0230c355fa65d4b96e9c001c447406e5aa0e8949389c` |
| mutation audit with primary adjudication | `92e6b6a0a7e502f485db43256d6e6553e9502dcaf3172f9253e441bcca5071ae` |
| replay/capture completion proof | `f286eb3d0280b614caf2a870aa36204ff766241033c9dc49b75f01cde9d87fd7` |
| initialization replay proof | `cb1ffafb226d1b8443c6d6f3206b5205fc2ec760137e58e16b964f659d67797c` |

Historical baseline code hashes consumed from the prior frozen source audit:
lib.rs `199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070`,
candidate_intrusion.rs
`2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c`,
candidate_context.rs
`72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
These are historical pre-repair code inputs, superseded only for the two
changed production files by §10. Actual correspondence is supplied in §8.

Checks: static plan/proof reads, direct research-input hashes, note whitespace,
fences and local links. No live compiler reads, code/tests/builds/probes, Git,
children or shared-record changes. One bounded normal prover pass; requested
configured Sol/high, effective runtime model/effort metadata unavailable.
No executable samples/heavy processes; CPU/RAM not instrumented.

Commit packet: sole new path
`notes/theory/2026-10-16-native-retained-value-rewrite-invariant.md`, baseline
`8d2699197`; no dependency edits. Producer construction ready, review pending;
at that construction checkpoint code correspondence and the original
universal duplicate/H2/MODEL parents remained OPEN. The actual bridge and
review handoff now follow in §§8–10. Suggested checkpoint: `research: prove retained Value rewrite origin and lifecycle invariant`.
Shared-record integration/adoption remains primary-owned.


## 8. Actual frozen constructor/consumer correspondence

The primary froze writes at parent `8d2699197` and supplied the two production
hashes in §10. Direct hashes agree. All production Option accesses and all
`TypedPairMemo::Value` matches/constructors were searched, not just the new
setter. This establishes correspondence for the selected repair on successful
production paths; it does not derive semantic extrusion correctness from a
Rust data field.

| Actual owner | Correspondence and preservation argument |
| --- | --- |
| `lib.rs:4212–4224` | The field is inline and compiled only with `shadow-apply-candidate`. `Clone`, `Eq` and `PartialEq` include it automatically. Effect has no separate replacement field. |
| Fresh Value entries, `:12491,12503,12520,12540,12589,12633,12676` | Every production constructor supplies None. These cover canonical forwarding, reuse's admission argument, incompatible shapes, extremes, genuine extrusion admission, ordinary application and Function admission. No entry is populated from diagnostic children. Test constructors also supply None; they do not justify a production origin. |
| `dispatch_live_item:12480–12515` | The current relation's ordinary memo check remains first. On a miss, canonical forwarding precedes the Option lookup. A noncanonical raw key records its edge and queues canonical work without setting Some. A Some read records the current admission, recaptures that exact W, constructs its current contextual relation, enqueues exactly W and returns. It never enumerates diagnostic children. |
| Genuine producer, `:12552–12605` | The two mutually exclusive structural/row cases call `candidate_extrude` with the receiving row level and appropriate polarity. Their successful output replaces only the applicable endpoint. The final changed pair is admitted, its diagnostic edge retained, its current rewrite relation successfully constructed, then its exact W passed to the setter, then queued. No-op copying sets no field. |
| Setter, `:13040–13059` | Exactly one production caller, at :12599. A missing/non-Value memo fails. Existing equal W returns idempotently; different W returns `IdentityExhausted` without replacement. None journals its original memo before setting Some. The equal-value case creates no graph. No diagnostic producer calls this setter. |
| Existing admission replacement, `:13105–13131` | New keys are journaled and inserted with the supplied None. Existing keys are first snapshotted, then only `direct_witness` and `completion` are overwritten; the existing Option and children survive even though the incoming entry has None. Thus Some's reuse admission does not erase its own authority. |
| Reopening/SCC completion, `:11580–11585,13597–13605` | Both snapshot before mutation and write only completion. Intrusion's generation publication and root reopening do not clear or reconstruct Some. Diagnostic-edge insertion, `:13155–13275`, journals and changes only children/index/accounting. All other production enum matches read fields or mutate diagnostic-only data. |
| Manual snapshot, `candidate_intrusion.rs:386–436` | The first snapshot of an old memo copies the Option directly together with witness/completion and independently allocated children. Already-saved and new-route keys are excluded from repeated snapshots. Inline identity is never reconstructed from the child list. |
| Rollback, intrusion `:145–181`; lib `:9460–9596` | Store rollback and intrusion rollback are synchronous: forests, group/output indices, activations, reuse records, generation, relation completion and old complete memo values are restored. Row bound lengths/levels and fresh row arrays are then restored/truncated; new route memo keys are removed. No dispatch can observe the intermediate restoration. A pre-route Some points only into the pre-route retained graph; a route-created Some on an old key is replaced by its saved value, and a newly created memo is removed. This is the existing route's restoration protocol, not a new global rollback law. |
| Actual reuse, intrusion `:317–349`; context `:2979–3004` | Recapture searches only groups indexed by original key and W's actual output endpoints, leaves original parent records immutable, and adds the current source-use association once. Newly qualified groups become pending and dirty. The rewrite consumer checks the actual processing parent pair; derives current context/source/scoped flow, rejects unsupported transformers and authenticates/updates an existing demand root only through the actual copied upper Function. Its Derived edge is retained before enqueue. Some certifies origin; these actual consumers still perform their checks. |
| Resource owners, lib `:4687,6432,6516,10938`; intrusion `:214` | Cache, independent inventory/estimate and journal capacity use the actual containing `(TypedPairKey,TypedPairMemo)` size. Every bucket, including Effect buckets, therefore reflects any enum-size growth. Nested diagnostic bytes count children only: the new inline Option contributes no additional heap payload. No new variable-size allocation is introduced by the field. |

The only ordinary production writes to the new field are its None
initializers and the dedicated setter. A full-memo rollback is restoration,
not an additional origin. The constructor induction of §3 therefore applies
to this code, including new/existing memo transactions. Its conclusion is
origin, uniqueness and lifecycle preservation for the actual retained W.

The old mixed-producer trace now has a direct operational resolution. In
`candidate_apply_value` (`candidate_extrusion.rs:844–874`), the new relation R2
selects its original level-owned B, invokes `candidate_insert_bound`, and
invokes `candidate_replay_bound`. The insertion's evidence admission precedes
physical insertion (`:442–493`), and `candidate_bound_origin_with_evidence`
(`candidate_effect.rs:426–455`) attaches the current relation before its
origin-key duplicate shortcut. Thus R2's bound fiber is actually retained;
the proof does not rely on a diagnostic child's possible scalar equivalence.
If genuine Some and ordinary children coexist, only Some drives replacement;
the other diagnostic edges remain independently retained. The ordinary-child
case has the authenticated source trace. The mixed Some-plus-diagnostic case
is covered by the operational invariant; its manually assembled fixture does
not independently establish source reachability.

Tests were read only as verification obligations. The frozen intrusion test
covers new-memo rollback, genuine production, reuse without copied-row growth,
mixed diagnostics, post-intrusion preservation, conflicting-setter rejection,
replacement/reopen and old-memo rollback. Its runtime assertions are not
premises of this derivation. The primary owns all execution and any missing
focused coverage.

## 9. Composition with the original duplicate obligation

**Independently accepted conclusion:** the repair discharges the
specific unsupported diagnostic-frontier premise of the prior mutation audit.
For the original successful candidate-production scope, the composition proves
preservation of the native transition obligations named there: current context
checks; retained genuine rewrite work; ordinary bound/fiber admission and
ordered replay; Function-port work; evidence/bundle propagation; and invalidation
or writer-owned propagation after the mutable changes below. This is the
original local native obligation-retention claim, not a theorem that these
native transitions completely model source typing or complete Call semantics.
The primary accepts that exact native scope through the receipt above.

Here is the composition as an execution induction, rather than assuming a
completion stamp is sound. For every relation R stamped at generation G,
retain either its concrete local terminal obligation or its exact emitted
child/cursor/replay work under the active drain. Every dependency/evidence
arrival has its writer-owned propagation even if R's ordinary expansion is
memoized. At a later skip the full key and generation select this same R;
Transport and Context have already run on the current work item. The following
cases establish and preserve the induction hypothesis.

1. **First dispatch establishes it.** Effect Bottom/equal/nominal checks retain
   their ordinary terminal result or conflict. Support expands every immutable
   member and the live tail. Value extremes/shapes retain their terminal
   diagnostic state; row application retains the bound fiber before replay;
   Function application retains all four children under the actual Function
   cursor. Canonical aliases queue canonical work without stamping it as the
   raw semantic task (`mark_candidate_pair`, intrusion :352–383). Genuine
   extrusion produces its actual W plus copy/parent work. The new origin
   invariant makes reuse take this last case only when it has that producer;
   otherwise ordinary dispatch establishes the missing original bound case.
   Stamping before enqueue/descendant completion is harmless on a successful
   dispatch because work is owned before return, then by the reviewed drain.
   Failure is not a successful dependent publication.
2. **Same-generation new bounds/fibers are handled at their writers.**
   Ordinary Value/Effect admission always inserts/attaches then enumerates
   physical opposites (`candidate_extrusion.rs:799–905`). For lower fiber heads
   L'/L and upper heads U'/U, replay's two loops enumerate
   `(L'\L)×U'` and `L×(U'\U)` in ordered-parent orientation
   (`candidate_context.rs:3406–3459`). An already retained exact Replay
   dependency accounts for a duplicate; incoming-use restoration forces its
   diagnostic replay separately. Thus later growth cannot require an old
   dispatch to discover a bound interaction which its writer has omitted.
   The restored R2 association in §8 is essential to this argument.
3. **Merge invalidates before a later skip.** The only production representative
   and existing-level join writer copies both bound sides/origins, moves
   capture incidence, changes the forest and canonicalizes all bound fibers,
   including third-owner occurrences, then publishes the incremented generation
   and replays merged-owner intersections (intrusion :518–611; context
   :3612–3632). It drives no nested source dispatch during the intermediate
   transport. Consequently no old-generation stamp can suppress work after
   that mutation. Forest compression alone changes no representative.
   Some survives as the same retained copy graph; this is origin persistence,
   not a claim that old and new endpoint spellings are identical.
4. **Context/effect records do not silently acquire new operands.** Interned
   relation/context/scoped/source keys, structural Function terms, Support
   members, allowed sets and contribution identities are immutable on these
   paths. A changed key is a different relation. Context execution precedes
   each skip. A first discharge installs its Allowance registration and
   replays current lowers before recording discharged/residual state; later
   lowers meet that physical upper through case 2. Reusing discharge does not
   suppress construction of a newly required mutable filter.
5. **Evidence arrival is independent of re-expansion.** A new Derived,
   FunctionPort or ordered Replay edge calls `edge`/`bundle_edge`, which
   backfills every already-linked parent bundle. A later bundle traverses
   existing successors and eligible zero-use transports through the incidence
   append queue (`context:2365–2402,2660–2755`). These two orders establish
   the closure invariant by induction on edge/bundle additions. FunctionPort
   additionally invalidates watched source-support registrations under its
   distinct lifecycle generation. It does not need to invalidate semantic
   pair completion. FreshUse is still its own authenticated transport; no
   template-to-use constraint is invented. The new field does not change any
   of those constructors.
6. **Qualification/recapture and restoration remain owned.** The sealed source
   graph fixes qualification for a source event. Different source sets cannot
   inherit each other's full relation stamp. Actual genuine reuse recaptures
   W's group for the new source association and retains newly qualifying
   pending pairs (§8). The initialization-replay theorem supplies the actual
   copied-bound/restoration replay work; its completion theorem keeps that
   work drain-owned until consumed. Rollback restores the entire previous
   induction state and removes route-created tasks/memos/graphs; it cannot
   leave the newly added certificate with a discarded graph. No arbitrary
   partial-error retry is postulated.

The reviewed drain theorem supplies the final ownership step for the queued
consequences in all six cases: a successful action cannot return while queued
work, Function cursors, dirty intrusion or unconsumed replay acknowledgements
remain. Within an active drain a second memo hit leaves the first expansion's
work owned; across successful drains that work has completed. The new Option
is neither that completion receipt nor a substitute for it.

This discharges the prior audit's **one unclassified dispatch producer** without
requiring a future-stable ordinary diagnostic frontier. It does not prove the
mathematical meaning of all old extrusion rules, arbitrary contextual
interpretations, source MODEL, whole H2/U, principality, or global inference
adequacy. Those original parents remain separate and OPEN. In particular,
this composition supplies no missing source-to-native generator. These
exclusions match the original native transition-retention gate frozen in the
prior audit §1; they impose no restriction on its source programs or later
mutations.

## 10. Final frozen inputs and handoff

| Actual source snapshot | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `crates/yu-solver/src/candidate_context.rs` (unchanged) | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_extrusion.rs` (unchanged) | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/candidate_effect.rs` (unchanged) | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_source.rs` (unchanged) | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_value_graph.rs` (unchanged) | `d08f6c5fb9ae4c5f005b6cb40aa3462f4f58b350cd6842b76a15d2dfdb520bec` |
| `crates/yu-solver/src/candidate_intrusion_tests.rs` (final fixture, primary verified) | `30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3` |
| `crates/yu-solver/src/candidate_context_tests.rs` (constructor inspected) | `45465871d4eec1dea86bb7fa652a253b82e293ce91512608df6c06ab248eec95` |

Only this leased note was written. Static constructor/access/mutation searches,
source reads, SHA-256 checks and note whitespace/fence/local-link checks were
performed. Zero tests/builds/probes/benchmarks/Git operations/children; no source
or shared-record edits. The normal prover setting was requested; effective
model/effort metadata is unavailable. No CPU/RAM measurements were made.

Commit packet: baseline `8d2699197`; sole path
`notes/theory/2026-10-16-native-retained-value-rewrite-invariant.md`.
Changed dependencies relative to the historical native audit are lib.rs and
candidate_intrusion.rs at the hashes above; the production snapshot was supplied
frozen, not edited here. Claim class: producer proof and actual source bridge,
pending independent review. Next action: independent semantic/source review of
§§8–9's composition against the original duplicate claim, alongside the
primary-owned executable verification. Proposed checkpoint message:
`research: bridge retained Value rewrite invariant to frozen native owners`.
Primary/curator retains all adoption and shared-record status updates; do not
record source MODEL/H2 closure from this packet.
