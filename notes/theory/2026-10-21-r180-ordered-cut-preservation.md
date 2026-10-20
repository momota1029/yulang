# R180 — physical materialization of plain ordered row cuts

Revision 1; author `/root/r177_source_consumer_proof`; assignment
`R180-ORDERED-CUT-PRESERVATION`. Outcome: **candidate transition-inductive
source/native lemma and exact full-scope obstruction**. No source-qualified
counterexample or independently certified new theorem. All original parent,
A/B, source/native, implementation and production gates remain OPEN.

Contract revision 1 SHA-256
`ddbbe0ec7e288ebf8bb5386b9b4073985428ccea5bc3b320a110b25042138d31`;
issued packet revision 1 SHA-256
`4949d854f4a870b40f8db75b1768e4f0bb599c07496a0b3fb295691cef4449ae`.
Luna's NEW_TASK activated the CLEAN-reviewed packet. Initial active current.json
matched those pins; observed state hash
`cd867a7f52e91a4bea3384bf7fbd6bb2cb250457f52973a636023030a9bbc013`.
Luna owns later runtime/accounting updates; this writer never edits current.json.

## 1. Parent application and precise result

Parent `2026-10-15-computation-forwarding-preservation.md` §§1,6–7, SHA-256
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Preserve shared xi, open incoming E, every finite chain/prefix, repeated and
simultaneous original entries, independent protections, original source/formal/
provider identities, pending inputs, raw continuations, guards/arms, alternatives,
residual/scoped payloads, canonical/self/current/reused cases, anchors and valid
rollback. F1/FK1 remain independent. No restriction of that source domain or
change to ordinary Simple-sub inference is proposed.

R179 established a worked initializer Replay and a finite owner-cut compression
argument conditional on actual cut materialization. R180 now supplies that
materialization step for **identity-context, default-flow row cuts on valid
successful solver paths**, including current-pair reuse. It supplies an exact
physical bound and child relation fiber, not merely a visited task or marker.
It applies to arbitrary finite numbers of such cuts and repeated replay; this
is not another finite fixture census.

Apply it immediately: at a quiescent Capture boundary, for a R179 all-local row
path whose required cuts have identity contexts/default flow and authentic
input incidence, replace the former materialization assumption by §§2–4 below.
R179's compression then yields a genuinely captured boundary path, restored by
one actual FreshUse map per use. For the worked tau->beta->rho path this supports

```text
e_A <= mu_i(tau) <= mu_i(beta) <= mu_i(rho) <= e_C <= e_out
```

when the independent actual provider/Apply consumers supply their endpoints.
No mu_i for an eliminated internal Name row is invented. Universal source
input authentication, contextual meaning, shared-anchor consumer correspondence
and full Capture timing are still separate premises; this does not close the
original parent by assuming those premises away.

The first full-scope unestablished premise is **authentic same-provider/use
incidence for both supplied input fibers through captured/shared/imported
transport**. The actual constructor conserves their ordered relation identities;
it does not by itself establish their original source ownership. Contextual
extension and pending-at-Capture compatibility are additional exact boundaries
in §5. None is a demonstrated source inference failure.

## 2. Actual row Dispatch invariant

All new source reads use only the six permitted candidate owners under
`/tmp/r178-inputs/candidate-e9a7a4f/`. Baseline copies are hash/mode evidence.

Let r be the actual processing relation after Transport, with EffectRow-to-
EffectRow pair, identity ContextId and default scoped flow. Define Mat(r) to mean:
its pair is reflexive, or a real physical row lane contains its canonical
inequality and the exact corresponding BoundKey has r among its attached
fibers. This is stronger than endpoint equality. The predicate is proved from
constructor history, not read from completed[r].

Work in a valid single-threaded solver history: returned operations succeed;
a failed private attempt is discarded, or a valid transaction rollback restores
the preceding valid state before reuse. No theorem about reusing an unrecovered
failed state, panic/abort, allocation success or arbitrary checkpoints is used.
Between representative changes, the following induction establishes Mat(r)
after each successful row Dispatch, including a current return.

### First admission

1. step_typed_drain retains the actual item and runs Transport then Context
   before Dispatch (lib.rs:12375–12471). Relation transport checks canonical
   task correspondence (candidate_context.rs:3629–3646).
2. candidate_context_execute_relation returns false at identity context
   (:3662–3698). Thus this row task is not silently treated as an already
   consumed allowance. Default flow also permits the ordinary reflexive case.
3. A noncurrent Effect Dispatch records its typed-pair admission, then calls
   apply_effect_task because context_consumed=false (lib.rs:12498–12516).
   mark_candidate_pair writes the actual processing relation only when the
   raw key is canonical (intrusion.rs:423–455; lib.rs:13145).
4. In candidate mode apply_effect_task returns through candidate_apply_effect
   (lib.rs:11817–11823). That function canonicalizes, returns on reflexivity,
   or selects one real row owner/lane and inserts it before invoking replay
   (candidate_extrusion.rs:944–971,501–682). This is the candidate path, not
   the later legacy mirrored-row implementation in lib.rs.
5. The bound's actual relation is r. BoundKey's oriented pair equals the
   canonical task pair. candidate_context_bound_for (:3760–3804) selects the
   matching processing parent r. Its post-check context is identity, sources
   remain r's source set, and ordinary same-kind bound payload remains default
   (:2997–3022). relation_with_scoped interns precisely the same tuple
   (pair,context,sources,scoped), hence returns r (:3023–3051). attach places r
   on that exact BoundKey (:3241–3253). candidate_insert_bound_with_evidence
   appends and reads the selected physical slot before publishing its emission
   (extrusion.rs:602–682). Therefore Mat(r) holds.

Identity-context r has no hidden filter-discharge residual: only execution of
nonidentity contexts inserts into discharged, and post_check_context otherwise
returns r's immutable context (:3255–3262,3662–3748). The argument does not
substitute a different equal-looking relation or assume a recipe is an append.

### Current reuse

Strengthen the induction during admission with a temporary obligation owned by
the actual current Dispatch between its mark and physical insertion. There is
no successful return or child Dispatch inside this interval: the selected lane
is appended before candidate_replay_bound generates/queues children. Reservation,
evidence and sampling calls can fail, but do not consume child work. The valid-
history condition handles those failures rather than claiming local atomicity.

For a current row return, pair_is_current requires raw memo membership and the
actual processing relation marked in the current generation (lib.rs:11593–11604).
Choose the first surviving mark of that relation in the generation. A previous
current return cannot create that first mark. It came from a noncurrent row
Dispatch with the same canonical relation/pair; the first-admission argument
has established Mat before another child could be consumed. Physical lanes and
fiber lists are append-only in the unchanged epoch. Consequently the current
return inherits Mat(r). It is not merely assigned satisfaction from the marker.

Raw aliases do not weaken this argument: a noncanonical key cannot create the
relation-generation mark. If an alias subsequently satisfies current, its
actual canonical relation already has the established Mat; otherwise its own
canonicalized row insertion establishes it. This is a physical row-fiber lemma,
not certification of reused FunctionPorts or runtime protection profiles.

### Generation change and valid rollback

A successful merge increments generation only after copies/transports of both
sides and canonicalization (intrusion.rs:618–706; context.rs:4092–4113). Every
old completion value is at most the old generation; checked increment therefore
leaves no current marker for the new generation. New canonical relations cannot
inherit current status solely from an old mark. The first/current Dispatch
induction applies again after actual transport. This does not assert that old
and new raw BoundKeys are identical, or prove their complete source lineage.

Valid rollback restores generation/completion/memos and fiber heads/dependencies
alongside physical lane lengths and current frames (intrusion.rs:201–246;
context.rs:2049–2147; lib.rs:9429–9485,9530–9575). Workspace inverses restore
retained pushes/pops; a fresh abandoned attempt clears its own queue
(:9761–9768,12979–13013). Thus a previously valid checkpoint regains the same
predicate; a rolled-back append or child is not used as surviving evidence.
The runner can pop a frame on error without local rollback, so discard/recovery
before further successful reuse is an essential stated condition. No full
capacity restoration or general unwind law follows.

## 3. Both input lists and actual work ownership

attach (:3241–3253) either retains an existing relation or appends a new immutable
fiber record pointing to the prior head. replay_progress (:3234–3240) journals
the exact previous pair of heads. For an ordinary Replay with old lower/upper
lists L0,U0 and new prefixes dL,dU, candidate_context_begin_replay:3854–3939
actually enumerates

```text
(dL × (U0 + dU))  disjoint-union  (L0 × dU).
```

The old/old product has its prior generated obligations. incoming_use resets
both old heads to None, giving the full current Cartesian product, including
repeated uses. Canonical changes select canonical BoundKeys and append actual
transport fibers; a changed key has a distinct frontier. Valid rollback restores
both heads and replay_progress together. Empty lists legitimately give zero
children; this is not evidence that missing required source inputs were supplied.

For every enumerated pair, the actual constructor retains lower and upper
relations AND lower_input and upper_input, with ordered context/source/flow
composition. No either-parent reachability is used. Identity/default parents
produce identity/default child r, with the exact intended row pair.

Use a ghost history of each successful constructor's actual operation and child
index. It records the pair produced by its nested loops; no production field,
extra file, executable model or assumed transition is introduced. The child is
first owned by ReplayOperation.children, then by the queued work/current frame,
then by its actual Dispatch result. enqueue_item preserves the explicit relation
and reserves before transfer (lib.rs:13028–13051). transfer_replay_child advances
queued, pop transfers the exact front item, and the frame keeps its ack separately
(context.rs:2336–2420; lib.rs:12390–12471,12971–12976). The child cannot be called
returned merely because generation ended or drive_replay returned Queued
(context.rs:4070–4089).

For an identity/default row child whose canonical representation stays fixed
through transfer, §2 makes the Dispatch result Mat(r), or reflexivity. If
Transport changes the recipe child r0 to the actual processing relation r_exec,
the ghost history retains that delegation and §2 establishes Mat(r_exec).
Task/canonical-pair correspondence is checked by the actual transport constructor;
the full source interpretation of that changed spine remains a §5 obligation.
Neither Mat(r_exec) nor endpoint canonical equality alone certifies r0's original
source/provider meaning. Terminal diagnostics and acknowledgements follow real work;
Running->Ready->Idle return barriers check actual operation/index/counts
(context.rs:3942–4036; lib.rs:12761–12825). Acknowledgement alone remains only
administrative completion; the independent §2 proof is what supplies the
physical constraint for this subcase.

Ordinary dependency dedup does not erase the prior obligation: its first
successful generation has the same ghost-history owner or established Mat.
A failed generation before operation ownership must be discarded/recovered,
not inferred complete from its retained recipe. incoming_use can create another
operation for the same structural recipe; preserve that use's actual operation
and transport/admission lineage. Shared relation IDs are not new use identities.
The argument proves conservation/materialization of the given ordered fibers;
it does not turn their structural presence into source ownership.

## 4. Application to R179 Capture compression

At an actual quiescent boundary with no required unqueued/queued/current replay
child, the identity/default row obligations above have materialized physical
bounds/fibers or are reflexive. For local rows with the required interface path,
R179's finite owner-cut argument can now use this actual transition result in
place of its unexplained plain-row materialization assumption. Both parent
relations remain the ordered provenance leaves of each compressed step.
Capture then enumerates the real local lanes and records BoundKey/alternative/
snapshot; one real FreshUse maps the captured path (scheme.rs:835–866,
1084–1244,1633–1986). This is the immediate parent application in §1, valid for
arbitrary finite such paths/replays rather than just the initializer example.

Quiescence must be proved at the actual Capture caller. The module-plan seam
calls member source schedules before staged captures (scheme.rs:1470–1519),
consistent with R179's reviewed successful synchronous trace. A Local first-use
capture happens before starting its own children (:2080–2134). Neither fact
alone proves that every possible earlier pending obligation has become Capture-
compatible. begin_route_transaction's Fresh debug assertion checks an empty
worklist, not the absence of all current frames (lib.rs:9054–9060).

Graph/Capture retains rows, bounds, contexts, snapshots and attachments, not a
mapped typed-drain/worklist/ReplayOperation continuation (scheme.rs:37–57,
1293–1407). Therefore global pending work is not automatically the alternative
Capture-compatible owner allowed by the parent invariant. At a nonquiescent
boundary a separate correspondence or transport proof is required. No actual
source path violating quiescence has been established here, so this is not an
inference counterexample.

## 5. Exact full-scope boundaries and minimal next work

| Obligation / owner | What the pins establish; first missing evidence and falsifier |
| --- | --- |
| Authentic same provider/use on both input fibers | candidate_effect::candidate_transfer_bound_origins:681–718 transports executable source fibers separately from origin metadata. Metadata explicitly lacks an origin-to-fiber association. BoundEvidence::admit:751–779 retains source-authentication/antecedent gaps; a FreshUse cause checks its imported snapshot/use/Transport but cannot establish the original source premise itself. Need actual original-source->captured/shared fiber->same use on BOTH sides. Falsifier: sibling/foreign source or only one authentic parent passes. This is the earliest full-source premise before applying the conservation proof. |
| Contextual/scoped ordered cut meaning | begin_replay preserves ContextExpr::Replay and composes transforms. compose_scopes:2780–2791 calls candidate_scope::ScopeTransformer::then; evaluation also delegates to that owner. candidate_scope.rs is outside these six pairs and was not read. Need the actual ordered semantic law/source correspondence; plain row transitivity is not that law. A new exact dependency needs Luna's review. Falsifier: a residual/transformer is dropped, reordered or treated as independent provider permission. |
| General current/reused Function or checked context | §2 establishes row materialization for identity/default relations. Function Dispatch marks before four fields; current Value return precedes fresh fields. Context filter execution and discharged/residual maps are separate (lib:12519–12521,12710–12729; context:3462–3528,3662–3748). Need actual inherited field/checked-context semantic obligation and matching consumer, not extrapolation from Mat(r). Falsifier: marker or visitation substitutes for required field discharge. |
| Shared anchor consumer | Capture stops; FreshUse preserves an actual canonical anchor under its guards. Actual potential consumers are Function AE/RE tasks (lib:12682–12700), candidate_function_port_admit, Context/Dispatch and allowance/bound replay. Prove the exact old source constraint joins that same-use field and executes or validly reuses its obligation. A retained row alone is insufficient. Falsifier: no matching consumer or endpoint-based source substitution. |
| Pending at Capture / caller timing | Graph has no mapped replay/drain continuation. A universal quiescence proof must consume actual source caller control; execute_candidate_source_root/schedule lives in candidate_source.rs, outside R180's six new reads, with only R179's limited successful trace available. Need a reviewed exact owner if that control proof is the next stage, or a genuine Capture-compatible continuation construction. Falsifier: Capture drops an owned queued/current cut or an unrelated future consumer is substituted. No violating source instance is claimed. |

Minimal TODOs to Luna: **R180-INPUT-AUTHENTICATION** for the first row;
**R180-CONTEXT-LAW** for the exact scoped owner if needed;
**R180-CAPTURE-OWNER** for caller quiescence/compatible transport and anchors.
Use existing actual records and proofs first. If code evidence is necessary,
a separately reviewed provisional receipt must observe both real inputs,
operation/current/return and physical child, with exact provider/use. This
packet authorizes no code or semantic change. Resource erasure remains
independently OPEN for layout/capacity, shared allocator, Arc/refcount,
rollback/publication/unwind; no repeated broad resource audit was added.

## 6. Provenance, checks and stop

Reused R179's final reviewed unfinished-research artifact and finite owner-cut
result within its hypotheses. Its finite worked route and refutation of the
missing-internal-row lead remain valid; it never certified universal scoped or
anchor behavior. The parent's reviewed source/template claims remain within
their original premises. Rejected: recipe presence as work completion, markers
as satisfaction, OR ancestry as both inputs, copying every internal Name by
invention, legacy mirrored insertion as candidate behavior, and a global pending
state as a captured continuation. No source-qualified failing transition was
established. This writer does not independently certify its own new result.

Authors: /root/r177_source_consumer_proof for note/handoff and R179 proof;
Luna for contracts/snapshots and frozen R179 mapping; earlier proof authors
remain as recorded in that pinned dependency; individual compiler authors
UNKNOWN. No descendants or reviewer appointments. Fresh review belongs to Luna.

Requested gpt-6.1-sol/high; exact observed model/effort UNKNOWN. Actual identity
/root/r177_source_consumer_proof; session current-conversation-2026-10-21-r180.
NEW_TASK and subsequent tools are actual activity receipts. First observed clock
2026-10-20 18:52:29 UTC; trusted launch/full launch-to-stop elapsed UNKNOWN.
Charge full **1380s**, 0 returned, 0 remaining; Astra/probes 0, no carryover.
Final observed clock and hashes follow in the frozen handoff/external receipt.

Checks: all twelve permitted file hashes, 0444 file modes and both 0555 root
modes at entry/exit; exact contract/packet, parent/fixture and R179 dependencies;
targeted reads of ONLY these six source owners, manual transition/finite-product
proof and leased prose writes. Other files present in the roots were not new
source inputs. No tests/builds/probes, compiler/evaluator/Yulang2 execution,
network, Git, nested CLI, code changes, scratch outputs or descendants.

Only new/changed paths: this note and tasks/agent-loop/inbox/20261021-r180-proof.md.
The useful plain-row lemma is applied above; full-source input authentication,
context law and Capture/consumer ownership are the exact stop boundary. No
further in-envelope step remains for this writer at that boundary; new owners,
proof allocation, code or review return to Luna. After final hashing both
outputs are **FROZEN; writer STOPPED**, no pending computation or unresolved
child lease and no background RUNNING claim.

Snapshot baseline metadata 7ec64a3788175913a2be46331cf0f64c6bd5b407; candidate
is the contract's immutable R174-v6 subset. R180 HEAD metadata f20c2d1e5 is not
a source snapshot identity. No Git check or mutable compiler substitution.

### Frozen direct dependencies

| Source owner | Baseline SHA-256 | Candidate SHA-256 |
| --- | --- | --- |
| candidate_context.rs | d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb | a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733 |
| candidate_effect.rs | c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1 | c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1 |
| candidate_extrusion.rs | 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332 | 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332 |
| candidate_intrusion.rs | 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97 | 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97 |
| candidate_scheme.rs | 9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225 | 48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25 |
| lib.rs | c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985 | 24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436 |

Other pinned evidence SHA-256:

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f  tools/inference-playground/examples/r171-formal-name-forwarding.yu
4de7c848e29f3de805454f70cf0811fc442905f7622d946db90cd157d7bde1f5  notes/theory/2026-10-21-r179-capture-coverage.md
4111c78800252dfe657b4a90cb1d7446559a65b4a58c69b69a3a1bf20094a1cb  tasks/agent-loop/inbox/20261021-r179-proof.md
359f9e23f254557bcfdbf017665e04590acfac230ad240e7d28e63a758f23095  tasks/agent-loop/inbox/20261021-r179-implementation.md
2ccc635133d7cdec1d9102d6dbac4e193bb21b9ce9c02542c744b98d8ffcc4a8  tasks/agent-loop/sprints/capture-coverage-20261021-r179.md
```
