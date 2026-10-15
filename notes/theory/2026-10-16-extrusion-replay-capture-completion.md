# Extrusion replay completion before dependent capture and use

Status: independently reviewed bounded operational completion/publication theorem.
No promotion of H2, effect hygiene, soundness, principality or cutover status.
Pinned primary baseline: `231a7d2bb`; native production ancestry `bf0562382`.
Exclusive output lease: this file. Leaf; no delegation or compiler/Git edits.

Independent compiler-referee `ordinary_carrier_semantic` returned CLEAN at
producer SHA-256 `938461247efc639e244d5ec9a603e237c1646566c70fab7c13dbf0e9a87d25b5`.
Accepted scope: actual queue-covered emitted work, drain/restoration completion
and source capture/use boundaries. This does not establish missing generation,
universal semantic duplicate redundancy, contextual interpretation or whole H2.
The [independent source attack](../progress/2026-10-16-extrusion-replay-publication-falsifier.md)
has a separate CLEAN bounded-exclusion review; neither result closes H2/U.
Mode M2, one semantic reviewer; no implementation, executable checks or measurements.

## 1. Frozen statement and scope

The original necessary H2 obligation is unchanged. For every successful
source-owned extrusion and actual ordered lower/upper relation-fiber pair
covered by the initialization-replay theorem, its required replay work and
recursive consequences must complete, or remain honestly owned/unresolved
without an invalid dependent result becoming available for capture/use.
Occurrences, bound keys, both parents, contexts and residual constructor
lineage remain distinct. This is an operational obligation; no native model,
complete Call interpretation or source admission theorem is assumed here.

Precisely, fix an actual source-mode candidate session and one extrusion
event E in its production execution. Fix any pair P quantified by
`extrusion-initialization-replay-invariant` §§1,3,7, including each attached
lower/upper fiber, its original BoundKeys and ordered parents. The imported
theorem establishes that the corresponding replay child is queued, or its
exact already-admitted dependency needs no duplicate queue admission. It
does not establish descendant completion. Quantification is over every such
E and P, with no restriction on expression shape or annotation spelling.

The conclusion established below is this lifecycle property:

1. A newly queued P and every subsequently emitted consequence remain owned
   by the active typed drain/worklist until processed. A completed source
   action cannot return while such work or qualifying intrusion work remains.
2. Replay acknowledgement is later than that drain's processing and
   diagnostic phases. A parent restoration cannot advance merely because a
   child was queued, popped, memoized or locally dispatched.
3. Production source execution reaches local installation, module graph
   availability and incoming/local root-link publication only through those
   completed action/restoration boundaries. A temporary captured graph or
   constructed FreshUse is not itself a published route or completion receipt.
4. Future source actions and FreshUses retain ordinary live constraints; they
   do not treat a saved graph snapshot or pair memo as a proof that no new work
   can arise.

“Processed” includes a retained diagnostic conflict and ordinary remaining
symbolic bounds. It does not mean every unknown is solved or every generated
constraint is satisfiable. A graph is not a source soundness certificate merely
because this operational property holds. In particular, the conclusion does
not demand that effect descendants precede the rewritten Value item inside a
drain; it establishes the completed boundary around their common owner.

The successful-operation scope is essential and original. On an availability
error the source driver propagates failure and does not continue to dependent
publication. No claim of arbitrary internal retry or complete abnormal rollback
is made. Finite successful executions are covered; an infinite drain does not
return a completed action. Synthetic test support/pauses are separately
classified in §6. They are not production source suspension certificates.

Excluded: whether every semantic obligation has a native generator in the
first place; arbitrary nonidentity context semantics; pending-cut contextual
equivalence; source reachability/U; complete Call; native model existence;
whole H2 and principality; a new scheduling barrier or default solver cutover.
These exclusions do not narrow the P quantified above.

Authority: top-level inference principles §§1,1.1,3–5; contextual attachment
admission §4; selected residual constructor-lineage policy. Their obligations
permit accumulation and owned deferred state; they do not require fully solved
constraints at generation or capture. The proof below uses the actual drain,
not a proposed readiness predicate or a second inference algorithm.

## 2. Owners and the ownership invariant

The source gateway is `lib.rs::constrain_live_item_with_inferred_entry`
(12069–12088): when `candidate_graph.is_some()`, it immediately calls
`run_candidate_typed_drain`. The following compatibility loop is not a second
reachable candidate-mode drain. The source emission owners ultimately use this
gateway for their live constraints. `candidate_extrude` is reached from the
Value dispatch cases at 12545–12576; its production call sites do not capture
or publish schemes. Reuse of an existing transformed child goes through
`recapture_candidate_extrusion` before enqueueing that child (12494–12509).

Use the following invariant of the actual active drain D, rather than a new
stored certificate. Every outstanding emitted consequence is in exactly its
current operational position: a queued TypedWorkItem; D.current; D.function's
next/pending child; or qualifying intrusion work pending settlement. Replay
operations retain their exact child vector and queued/consumed indices;
acknowledgements of popped children are retained in D.replay_acks. A current
function's unadmitted next child is still owned by its function frame. This
enumeration concerns work, not semantic truth of native operands.

The earlier initialization theorem supplies entry to the invariant. At the
end of `candidate_extrude` (candidate_extrusion.rs:372–386), all selected bound
origins and parent/output records are installed before the retained incoming
Allowance keys are replayed. `candidate_replay_bound` (799–840) constructs
the ordered lower/upper key pair and invokes the contextual replay owner for
each physical opposite. `candidate_context_drive_replay(..., None)` returns
Queued while children await the outer consumer (candidate_context.rs:3566–3609).
It does not return a false completion receipt.

`enqueue_item` (lib.rs:12974–13001) retains relation evidence, reserves queue
and journal capacity, transfers the exact ReplayChildAck and only then pushes
the item. No fallible operation intervenes between transfer and queue insertion.
`transfer_replay_child` checks operation, child index and waiting state
(candidate_context.rs:2045–2062). The earlier theorem supplies original
occurrence/fiber qualification; this step preserves it and does not reconstruct
the parent context from endpoint equality.

## 3. Drain induction: descendants cannot escape completion ownership

`start_typed_drain` (lib.rs:12265–12278) requires an idle worklist, retains the
initial task and original occurrence/cause, then admits the seed. The driver
(12282–12304) repeatedly steps that same frame until DrainStep::Complete.
It has no production early-success branch for queued or partially dispatched
work.

Induct on successful `step_typed_drain` transitions (12336–12444):

* Transport with no current item first settles qualifying intrusion whenever
  the queue is empty. It reserves acknowledgement ownership before popping.
  A popped item is stored in the frame; its acknowledgement is appended to the
  frame's prepared list. A missing queue item enters Diagnostics only when
  intrusion is also not dirty. Thus emptiness before settlement is insufficient.
* Transport with a current item retains the actual canonical relation;
  Context executes it; only then does Dispatch run. The current task survives
  every successful stage transition with its exact relation.
* Dispatch either completes that immediate step or installs a Function frame.
  It returns to Transport only after the function frame is absent/completed.
  `candidate_step_function_dispatch` (12784 onward) keeps the exact next
  child/pending item. It advances its cursor only after successful admission
  and enqueue. Function port consequences therefore cannot hide behind a
  parent dispatch return.
* Ordinary Value and Effect bound admissions call opposite replay
  (candidate_extrusion.rs:844–899). Support expands all declared members and
  its tail; an unmatched concrete/member operand forwards to the exact
  Allowance tail (candidate_effect.rs:967–1034). All these consequences use
  enqueue_item/enqueue_task and return to this same queue. Diagnostics are
  not substituted for those child operations.
* A recursive extrusion repeats the same initialization/queue-admission
  argument. Its new children may follow the rewritten Value in FIFO order.
  They remain outstanding work in D, so this reordering cannot itself make
  D return or enable the next source action.

Intrusion is part of the same induction, including a merge caused by a
descendant. `settle_candidate_intrusion` consumes pending qualified parent
indices (candidate_intrusion.rs:487–514). A nontrivial merge transfers both
bound sides/origins, canonicalizes relation witnesses, increments the
intrusion generation and replays every resulting lower against its uppers
(516–612). Any new queue or pending work is processed before the empty/clean
test can enter Diagnostics. A row-equality representative change does not
erase view IDs or their exact cut endpoints; the earlier lineage theorem's
structural invariant remains applicable.

The induction is a partial-correctness proof. It does not assert a finite
number of arbitrary exact contexts. If work keeps arising, the driver keeps
ownership and does not return success. If an unsupported context operation
fails, `candidate_zero_word_filters` returns an availability error rather than
a successful ignored constraint (candidate_context.rs:3070–3163); source
execution propagates it. No successful suspended production state is inferred
from the existence of that error.

Diagnostics is reachable only with no current task/function, no queued work
and settled intrusion. Its actual callees replay conflicts, settle diagnostic
SCCs and report witnesses (candidate_effect.rs:679–741;
lib.rs:13235 onward,13859–13878). These traverse/report existing diagnostic
data; they do not enqueue live semantic tasks or generate new extrusion work.
Consequently the worklist-empty assertion at 12439 records a consequence of
the owner sequence, rather than supplying its missing premise.

## 4. Acknowledgement is not the relation memo

There are two different completion notions. `mark_candidate_pair`
(candidate_intrusion.rs:352–383), called by record_typed_pair_admission,
stamps a canonical processing RelationId at the current intrusion generation.
This happens during immediate dispatch, possibly before descendants finish.
It is a traversal memo, not an acknowledgement of a completed drain.

An exact memo hit only avoids re-expanding the already-admitted task. During
that drain, the first expansion's remaining tasks stay in D's queue/current
function ownership; the hit does not clear them or advance D to Diagnostics.
Across completed drains they have already passed the completed boundary.
This is the ordinary first-expansion/memo invariant, not an assertion that the
memo field alone certifies descendants. The new raw diagnostic pair must also
exist, and `pair_is_current` (lib.rs:11585–11597) requires the actual relation
and generation. An alias-only diagnostic admission cannot stamp canonical
semantic work. A merge changes the generation and explicitly replays affected
bounds. Context execution precedes even the memo test; a same-endpoint task
cannot suppress a distinct required receiver/context check by that shortcut.

After Diagnostics, `candidate_step_typed_drain_terminal` (12708–12771) alone
advances acknowledgements. It validates top-frame identity and
completed <= prepared <= replay_acks.len. It completes the next exact ack with
`complete_replay_child`, advances the cursor, and reaches ReturnReady only
after every retained ack. ReturnReady publishes a parent replay-return receipt
before popping its frame. `complete_replay_child` checks the exact operation
and next consumed index (candidate_context.rs:2116–2125). No local Dispatch
return or memo insertion invokes this terminal owner.

For several replay operations interleaved in D, queue order preserves each
operation's child order; the drain ack list records the actual pop order.
Each operation's consumed index is therefore advanced in its own required
order. Descendants can interleave without being discarded. The zero-child
case can retire immediately because it owns no queued consequence.

This proves the completion part omitted from the initialization theorem:
every newly queued P and its recursively emitted work has been processed
before a successful enclosing source constraint call returns; its replay
operation's consumed/retired state cannot be obtained merely from Queued.

## 5. Actual capture/install/use transitions

The following distinctions are required; none is interchangeable with a
FrozenScheme or a semantic acceptance certificate.

| State | Actual owner and gate |
| --- | --- |
| Local available anchor | `locals[slot] = Some(LocalScheme { root, boundary, ... })` after source action completion |
| Module graph available | `graphs[position] = Some(graph)` after all schedules in that SCC and staged captures succeed |
| Captured/FreshUse under construction | Owned temporary graph/maps or LocalUse frame; no final occurrence root link yet |
| Routed occurrence | Original use fact/link constrained to completion, followed by committed route provenance |
| FrozenScheme | Separate legacy finalization output; not produced by storing a candidate Graph |

### Source scheduling and available anchors

`execute_candidate_source_schedule` (candidate_source.rs:1255–1266) drives
source actions to completion. `step_candidate_source` increments its source
cursor only after execute_candidate_action returns successfully. Its Install
and LocalAnnotation cases instead retain PublishLocal; the next step checks
support/wait before invoking install_candidate_local_term, then advances the
cursor (1294–1345). Every constraint-bearing action completes its synchronous
drain before control returns to this publication stage. The remaining actions
perform construction/installation/routing, rather than privately popping a
semantic work item and proceeding to a source continuation.

`install_candidate_local_term` (candidate_scheme.rs:1480–1504) installs a
live anchor, not a snapshot pretending to contain completed replay. No dispatch
or context consumer calls this publication owner. A later Local use captures
that live root at that use's source boundary (1519–1542). Older/non-generic
rows are shared anchors whose current mutable bounds remain in the session
(Capture::expand_row,648 onward); they are not stale copied bound arrays.

`execute_candidate_graph_plan` (945–1053) executes every member schedule before
capturing any member graph, stages every capture, then assigns graphs[].
Internal SCC uses intentionally refer to open live roots, not to unavailable
completed graphs. They add ordinary constraints through the same draining
owner; this legal provisional reuse is not a claim that a member is already
generalized or semantically valid. Dependency-first incoming uses require an
existing available target graph. Source-mode expressions run after the graph
plan (`lib.rs::execute`,10397–10417), not by bypassing its availability gate.

No source schedule can run concurrently/reentrantly inside the inspected
typed-drain stages. Those stages call context/bound/Function/intrusion and
diagnostic owners; the capture call sites are the graph planner and source
route owners. Thus a previously available live anchor cannot be newly routed
halfway through another source action's unfinished drain. The Rust session is
held mutably by that synchronous call. This call-site argument, not a new
global readiness scan, connects §3 to capture.

### FreshUse restoration and publication

Module routing does not blindly reuse the old bound snapshot. It reads the
stored live_root/boundary/frontier and recaptures the current graph
(candidate_scheme.rs:1058–1078). `freshen_candidate_graph` restores every
captured bound before returning its root term (1081–1105).
`begin_candidate_fresh_bound` (1380–1426) preserves original owner orientation,
source BoundKey, mapped relation, evidence antecedent, original occurrence/cause
and this FreshUse's use_origin. It does not choose new independent parents.

Restoration owns its emission, saved opposite count, next index, replay handle
and provenance (candidate_extrusion.rs:695–715). For each opposite it creates
the ordered replay. It advances only after drive_replay with provenance returns
Complete (733–795). That path starts a typed child drain, retains Running,
requires the terminal Ready receipt, and then delivers it
(candidate_context.rs:3500–3565). The saved-count traversal rereads canonical
live entries; newly admitted ordinary opposite bounds execute their own
ordinary replay. It does not use a saved count to omit a new admitted bound's
consequences.

Only after every restoration returns does instantiate_candidate_graph call
`route`; route constrains the original occurrence root link synchronously
before publishing routed_use_positions/provenance (lib.rs:16996–17066).
The immutable FreshRoute record is appended after that link
(candidate_scheme.rs:1428–1473). A newly constructed map is not a routed use.

The local route uses the same restoration owner. Its cursor keeps an active
restoration and advances next_bound only after its receipt. Only when all
bounds are restored does step_candidate_local_use constrain the root link
and set cursor.complete (1664–1705). The transaction commits that completed
frame into local_routes only after the final fallible step succeeds
(lib.rs:9286–9310). A retained parent frame between restoration operations
owns its graph/maps and pending cursor; the cursor is not an availability
certificate for an unlinked occurrence.

Capture retains per-bound relation/evidence fibers, exact source keys,
attachment bundles, context payloads/tails and latent scoped demand roots
(candidate_scheme.rs:602–646,840–895). Reuse uses one per-use map and retained
FreshUse transport provenance. This is the previously established structural
retention invariant applied at an idle boundary; it is not a claim that an
arbitrary context has been semantically evaluated. No row canonical equality
licenses merging residual view constructors.

## 6. Deferred/error cases and limits of this result

The production source caller supplies Support::READY and has no production
source-support certificate registration. The synthetic registration constructor
is cfg(test). A supplied wait or invalid registered support causes Suspended
before PublishLocal installs anything (candidate_source.rs:1278–1318).
This demonstrates the guard's control ordering; it does not prove a complete
production recertification mechanism for arbitrary future contextual circuits.

Similarly, production route_candidate_local passes pause_after=None and treats
Paused as unreachable; injected one-step pauses are test adapters. The retained
LocalUse/restoration/Running/Ready owners explain why their intermediate states
are not completed routes. No new production suspension API is asserted.

Every checked operation uses `?` on availability failure. The synchronous source
caller clears its source frame on error and returns Err; the graph plan stops
before subsequent captures/publications. Incoming/local routes have their
existing transaction owner. Previously completed graphs may still be private
session data; this theorem does not require erasing them or restoring every
internal capacity after an abort. Such an error is not a successful reusable
result. Likewise a diagnostic conflict may remain in a completed private graph;
that is not an assertion that the source program was accepted without errors.

This result supplies the queue-covered replayAck → completed source action →
capture/install/FreshUse operational bridge. It does not resolve the separate
pending symbolic-cut transport/context interpretation in the earlier H2
application, nor prove that a semantic comparison absent from the actual
generator was nonetheless executed. It must not be advertised as full H2
closure. The next action is fresh independent review of this exact control-flow
derivation, particularly the first-expansion memo invariant and capture callers.

## 7. Dependency freeze and handoff

Static reads and SHA-256 only; zero builds, tests, probes, delegated jobs or
production edits. Requested runtime: normal Sol/high leaf. Observed model/effort
metadata unavailable. No new allocation/traversal mechanism is proposed; this
argument follows existing operations and adds no runtime cost. Parent owns all
verification and review. Shared-record updates are deliberately not written.

Frozen dependency hashes:

```text
199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070 crates/yu-solver/src/lib.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38 crates/yu-solver/src/candidate_source.rs
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e crates/yu-solver/src/candidate_scheme.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b crates/yu-solver/src/candidate_extrusion.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c crates/yu-solver/src/candidate_intrusion.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6 crates/yu-solver/src/candidate_context.rs
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9 crates/yu-solver/src/candidate_effect.rs
cb1ffafb226d1b8443c6d6f3206b5205fc2ec760137e58e16b964f659d67797c notes/theory/2026-10-15-extrusion-initialization-replay-invariant.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
ae33f4914e5297f8446f231ec9f8b177c4aaea0b42586446a504d6027a774b1a notes/progress/2026-10-10-context-relation-completion.md
7407ffb6a3bbdd36a9d4a214a4a3a8fb56d7db1cb637454955c86b1fdca5b354 notes/progress/2026-10-11-owned-typed-drain-foundation.md
1f2df0b82beecd62572a1a5d9ae384627403beadcc3dd6e05fbeb148a8d706f8 notes/progress/2026-10-11-typed-drain-terminal-handoff.md
```

Commit packet: sole path is this note; baseline `231a7d2bb`; dependency hashes
above, no dependency writes. Review pending, no producer certification.
Proposed checkpoint: `research: derive queued extrusion replay completion before graph reuse`.
Proposed primary/curator delta after adjudication: attach this operational leaf
to initialization-replay's formerly excluded descendant/publication edge;
retain whole H2 and its source/context interpretation obligations OPEN.
