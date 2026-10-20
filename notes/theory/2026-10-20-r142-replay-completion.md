# R142 replay-child completion rights: local conservation and caller boundary

Status: **CANDIDATE/CONDITIONAL; UNFINISHED/OPEN**. This is a partial
constructor/control-flow derivation, not an independently reviewed theorem,
source-qualified defect, implementation authority or production gate.
Author: `/root/r140_action31_proof`, serving assignment R142-PROOF. No
descendants. Luna supplied complementary constructor observations, credited
below; neither contributor can independently certify the combined result.
Requested `gpt-6-sol` / high; observed effective model/effort UNKNOWN.

Contract revision1:
`tasks/agent-loop/sprints/replay-completion-20261020-r142-rev1.md`, SHA-256
`7ee1760617f295bc85cf892c72f3d7af1704cf0095e9c10c1763b14b36e4eb8f`.
Baseline supplied by Luna: `503e5c78ce67a4616044ce981030e5e1bda5223c`.
The contract retains its candidate preparation header; activation/grants come
from Luna's current-session assignment and current.json activation receipt.
No contract mutation or Git action was performed. All 13 live dependency pins
matched at entry and freeze; baseline-tree validation belongs to Luna.

## 1. Original parent and exact result

Apply this work to **R70-DRAIN-1**, not to the entry/fiber premises left open
by R70. The unchanged higher parent is computation-forwarding preservation
§§1,6–7: one shared satisfying assignment, original current formals and whole
Name arguments, arbitrary finite prefixes, repeated calls, simultaneous
receiving entries and independent foreign-continuation quantifiers. R70 entry
validity/fiber coverage, R71, R72/R73, Simple-sub A/B, inference/evaluator,
source/native and production remain OPEN. R50 remains NOT ADOPTED.

The established local contribution is a precise accounting of completion
authority through production replay creation, asynchronous queueing,
synchronous child drain, terminal acknowledgement, retained Running/Ready
return barriers, restoration ownership, successful commit and completed
rollback. It distinguishes a numeric operation ID from an operation lifetime.
It exposes the exact error-cleanup/caller premise preventing the full fixed
outcome: a cleanup can drop a drain carrying uncompleted acknowledgements;
restoration or attempt abortion must then be proved at the actual caller.

The actual Local/restoration caller and `execute_candidate_graph_plan` owner
are in `candidate_scheme.rs`, outside this contract's 13 frozen dependencies.
This leaf did not read/import that owner as a new R142 proof dependency. The
contract's missing/unowned constructor-state stop condition is reached. This
note therefore does not claim complete source closure or an authentic defect.

## 2. Lifetime, index and authority

For a successful operation publication use ghost identity
`lambda=(session, creation event, numeric ReplayOperationId)`. The ghost event
distinguishes two creations with the same numeric ID after rollback; it is
proof notation, not a proposed production field. Restoration creation and
replay creation consume the SAME checked numeric frontier, but publish into
different maps. An extant replay and an extant restoration cannot be allocated
the same frontier slot within one uninterrupted allocation interval.

Let n=children.len(), q=queued and c=consumed for one live replay lifetime.
Children are indexed positions, not RelationIds: two equal RelationIds at
different positions have two distinct completion obligations. At an ordinary
forward boundary the intended invariant is:

```text
0 <= c <= q <= n
for i < c:          completion has occurred in this transaction history;
for c <= i < q:     one queue/drain consumer owns the completion authority;
for q <= i < n:     the retained operation owns the not-yet-transferred child.
```

The claim of one consumer needs actual constructor/control-flow exclusivity;
the interval inequality alone does not prove it. The production transfer API
accepts already-queued indices and cannot by itself be treated as a linear
type. The local caller proof below supplies the new-transfer cases; arbitrary
struct assignments or synthetic duplicate enqueueing are excluded from the
source claim.

For a TypedDrainFrame F, the authoritative completion entries are
`F.replay_acks[F.completed_acks..]`; earlier entries are retained receipts.
`prepared_acks` records undo/preflight preparation, not another authority or
completed child. `F.current.replay_ack`, `replay_destination`, operation wait
ack and transaction undo copies can contain the same `(ID,index)`. These are
references/return barriers or dormant saved state, not independent rights to
call `complete_replay_child`. Running/Ready can retain an acknowledged child.

This formulation is transaction-relative. Rolling back an acknowledgement
restores its prior completion authority and cancels the rolled-back completion
event. It does not acknowledge the same child twice in one committed history.

## 3. Creation and queue transfer

`candidate_context_begin_replay` (`candidate_context.rs:3767–3853`) constructs
an ordered local child vector, retains dependencies/heads, checks the frontier
and map capacity, then publishes an operation with q=c=0, retired=false,
wait=Idle and no restoration. Empty child vectors begin with no child rights;
they are not assumed already reclaimed. A later resource sample can fail
AFTER publication, so an Err from this constructor does not prove absence of
a newly published operation. Such an operation belongs to the enclosing
rollback/abort case, not a fictitious successful caller handle.

`replay_operation_queue_next` selects exactly children[q]. The asynchronous
adapter in `candidate_context_consume_replay_child(...,None)` passes this item
to `enqueue_item(...,false)`. `enqueue_item` first admits missing evidence,
reserves queue/workspace undo, then calls `transfer_replay_child`, followed
only by journal logging and an infallible queue push. The transfer checks Idle,
not retired, index<n and c<=index<=q; only index==q increments q. Thus this
actual new-transfer adapter creates exactly one queued record for the next
index, with exact child relation/task and ack `(operation,index)`.

The already-queued acceptance branch permits an already transferred item to
enter a drain without a second frontier increment; this API possibility is
not proof that the inspected synchronous adapter takes that branch (its Idle
case starts at q=c). It does not authorize arbitrary callers to enqueue
duplicate completion owners. No production constructor in the inspected
replay adapters generates a second asynchronous item for an earlier index:
each new call re-reads q after the preceding infallible push. Test-only
compatibility/synthetic adapters are not a source reachability argument.

The complete asynchronous drive queues every remaining index. If no item is
left at q but c<n, it returns false from consume, hence **Queued** from drive.
It does not call acknowledge on this branch. A successful new nonempty whole
drive has q=n,c=0. If children are empty or already all consumed, the no-item
case can retire the operation, and drive returns Complete only when operation
is absent or retired+Idle. A transfer prefix before an error is not successful
whole-drive completion.

## 4. Queue-to-drain authority and terminal consumption

`start_typed_drain` (`lib.rs:12272`) requires an empty queue, pushes a frame,
seeds/adopts relation evidence and enqueues the initial item. The frame can
already exist if a later step fails. The frame index is its actual stack
position, not the operation ID. Queue transfer happens at `enqueue_item`, not
when the replay parent later stores Running.

`step_typed_drain`, Transport with current=None (`lib.rs:12361–12400`), reserves
ack-vector space and prepares the exact replay completion before `pop_worklist`.
Pop reserves/logs workspace undo BEFORE removing the item. Only after successful
pop does the frame retain the ack in its vector and increment prepared_acks.
Thus failure before pop leaves the queue consumer; successful pop moves its
authority into the frame's uncompleted ack suffix. The same ack in current is
an alias. Dispatch strips replay_ack from its local item before generating
children; canonical requeues and Function children have ack=None. They cannot
inherit a second authority to complete the original replay child.

Currentness suppression, context consumption, raw-to-canonical requeue and
Function dispatch can all complete semantic work without appending a bound.
They do not consume the ack vector. Equality generation and source qualification
may create further replay operations, but their `(lifetime,index)` rights are
separate. Neither `completed[RelationId]==intrusion.generation` nor endpoint
equality is a replay acknowledgement.

The consumer is the terminal owner `candidate_step_typed_drain_terminal`
(`lib.rs:12730–12796`), after diagnostics. It checks top-frame/stage and
`completed_acks<=prepared_acks<=len`. In Acknowledgements it selects precisely
`replay_acks[completed_acks]`, calls `complete_replay_child`, and increments
completed_acks only after success. The completion function checks c==ack.index
and either Idle or exact Running ack with q==index+1; then acknowledgement
increments c once. A repeated call for that consumed index fails c==index.
Returning to Acknowledgements cannot replay already completed vector entries.

The vector order matters. Asynchronous children of one operation are appended
back in increasing index order. Their consumers pop front; non-ack Function
children inserted at front do not reorder those siblings. Nested independently
created operations do not merge rights even when their relations coincide.
This supplies the sibling order for the inspected normal adapter, rather than
assuming that the completion function accepts out-of-order consumption.

The terminal stage changes to ReturnReady only once every ack-vector entry
is completed. On success it publishes any exact return receipt, removes the
frame, restores the enclosing processing pair/relation and returns transitions.
Therefore a successfully returned normal frame has no undisclosed completion
authority in its own ack vector. This is a safety statement; it does not prove
that diagnostics, settlement or the drain loop eventually reach ReturnReady.

## 5. Synchronous Running/Ready and restoration barriers

`candidate_context_step_replay_child` (`candidate_context.rs:3872–3929`)
requires q=c and an empty worklist at Idle. It selects children[c], prepares
operation undo, starts a drain and ONLY THEN installs
`F.replay_destination=ack` and `wait=Running{ack,drain_index}`. The initial
enqueue inside start is the transfer event q->q+1; writing Running does not
increment q. If start fails, the enclosing error adapter must clean its
partially created frame/queue and operation state (§7).

While Running the parent validates the exact lifetime handle/index and drain
position, q=index+1 and c in {index,index+1}, plus the frame's destination,
occurrence and cause. It steps that same frame. After its replay child is
acknowledged, Running can validly have c=index+1. The child has no remaining
completion right, but F still owns its terminal return barrier. For the final
child retired can already be true; reclamation must not erase Running.

ReturnReady validates Running and q=c=index+1, retains Ready with the actual
completion receipt, then pops the frame. This moves the return barrier to the
operation, not another completion right. The Ready branch requires the popped
frame's former index to equal current stack length, prepares undo, changes
wait to Idle and returns Delivered. It never calls complete_replay_child.
If a preparation/resource error happens before that Idle mutation, Ready and
its receipt remain, even though the drain is already absent.

`retire_replay_candidate` requires retired AND Idle AND no live nonretired
restoration that still points back. Thus c=n is not immediate reclamation.
A restoration carries one replay handle and the replay points back to it;
`validate_restoration_replay` checks both directions. A successful restoration
child driver advances its saved opposite index only after replay Complete or
returned=true; `advance_restoration` removes the pointer and can then reclaim
the replay in nontransactional mode. This pointer delays storage release;
it does not create extra completion authority. A restoration with no replay
or an empty replay follows the same retirement distinction.

The shared numeric frontier includes restoration IDs. Counting every number
as an operation with a child would be wrong. Only the replay-map publication
creates indexed child rights.

## 6. Commit, rollback and numeric ID reuse

Within a route, `prepare_replay_ack` saves q,c,retired and wait BEFORE mutation.
`prepare_typed_drain_update` saves the entire frame (including ack vector,
cursors, pending dispatch and destination) before mutation or terminal removal.
`prepare_restoration_update` saves its index/pointer/retired state.
The saved copies are dormant undo authorities. The active frame/operation
continues owning forward execution until route choice; undo is never dispatched
as a second concurrent consumer.

`commit_replay_operations` (`candidate_context.rs:2122`) discards typed-frame
undo and resets retained frames' preparation to their completed frontier. It
visits created replay/restoration IDs and saved operation/restoration mutation
references. Each candidate is reclaimed only under the guard in §5; restoration
pointers are tested in their final state before retired restorations are removed.
Only afterward are replay/restoration undo vectors truncated. A retained Ready
or Running operation is not reclaimable merely because the ack was completed.
Successful commit chooses the forward authority and discards rollback copies.

`State::rollback` (`candidate_context.rs:2004–2043`) instead restores old frames,
truncates new frames, reverses restoration and replay-operation undo, removes
all objects allocated at IDs >= checkpoint.next_replay_operation, and resets
the numeric frontier to that checkpoint. Therefore IDs ARE reused after
rollback. A cancelled creation's lifetime ends; a later creation at that number
is a different lifetime. Monotonic numeric identity across rollback is false.

For a fully completed route rollback, `lib.rs:9429–9795` additionally restores
source/Local state and then queue state. RetainedResume reverses workspace
Push/Pop/Growth logs, returning the exact old queue items and cancelling new
queue items; Fresh clears the worklist under its empty-entry requirement.
That requirement appears as a debug assertion in begin_route_transaction_for;
its all-source caller applicability is not inferred from the assertion alone.
Combined with context frame/operation undo, this restores old indexed rights
and erases new-lifetime holders before another dispatch. LIFO ordering reverses
the infallible post-transfer pushes and the logged pre-pop removals.

This coupling is essential. Context rollback resets IDs BEFORE workspace undo
removes stale queued acknowledgements. Inside that interval there can be an
ack with a number whose operation has already been removed. No dispatch is
performed inside the rollback sequence; treating the interval as an ordinary
callable forward state would give an invalid conservation equation. A rollback
phase owns the inverse actions until its complete return. Old IDs must not be
acted upon in that phase, nor handed to a caller for dispatch.

There is an additional error case: rollback is not infallible. For example,
`state.refresh_bytes()?` at lib.rs:9484 occurs after context reset and before
workspace restoration. This note therefore does NOT assert that every Err
from finish_route_transaction yields a restored reusable session. If rollback
fails, the partially rolled-back attempt must be aborted without reuse or
publication. The actual non-reuse supplier is part of §7's open caller bridge;
no full rollback requirement is imposed on accepted inference semantics.

## 7. Error cleanup and the exact missing constructor premise

Two pinned adapters remove transient drain frames on Err:

1. `run_candidate_typed_drain`, lib.rs:12303–12309, pops the newly started frame
   if it remains above the saved index, then restores previous processing.
2. `candidate_context_consume_replay_child(...,Some(...))`,
   candidate_context.rs:3950–3956, truncates newly created drains back to its
   saved frame_count and resets the parent wait to Idle only when such a frame
   still exists; it then restores previous processing.

Neither cleanup directly restores q/c or re-enqueues the truncated frame's
uncompleted acknowledgements. Thus an isolated helper-return invariant saying
"every q-c right is still in queue or frame" is not preserved across all
error returns. One possible frontier has a popped child (q>c) whose ack vector
is dropped by cleanup before any completion. Another has some completed
entries and remaining uncompleted entries. Resetting wait to Idle does not
recreate the missing consumer. These are source-code transition cases, not a
claim that an arbitrary bad state or particular fault is source-reachable.

The needed repair to the PROOF is an error-phase/attempt owner: the enclosing
transaction must complete restoration of the pre-route state, or the caller
must propagate the error and abandon that private attempt. Dropping an aborted
obligation is not acknowledging it. A replay whose publication/sample failed
before returning its handle is covered by that same rollback/abort supplier.

Acknowledged Running and Ready require different cleanup cases. In Running
after c advances but before ReturnReady, an error can remove the frame; the
completed child remains completed in the transient state, but its return
barrier is aborted or restored by rollback. If Ready already removed the frame
and preparation then fails, frame_count is unchanged: the adapter does not
reset Ready. That receipt remains retained. Neither case licenses a second
acknowledgement. Failure before transfer leaves q unchanged; failure after
transfer but before helper return belongs to the attempt owner.

Pinned lib.rs establishes that InferenceSession is private and
`run(mut self)` / `run_candidate(mut self)` execute with `?` before result
publication, so an error reaching those consuming entrypoints drops the
private session. The public solve path returns no session on Err. But this
does not establish that EVERY actual intervening source caller propagates
each error rather than catching/reusing the session. In particular,
`execute_scc_plan` calls `execute_candidate_graph_plan`, and the actual
Local/FreshUse restoration caller is outside this 13-pin proof boundary in
candidate_scheme.rs. Retained resume adapters can also retain preexisting
frames; their caller-level transaction selection cannot be inferred from a
helper's q/c guard. Test-only resume helpers in lib.rs do not establish a
production source supplier.

**R142-ERROR-OWNER-1 (OPEN):** supply the actual source caller chain for replay
restoration/drain errors and failed rollback, including retained owner cursor
and every error catch/return. Prove that before any continuation/reuse, complete
rollback restores all old rights and erases cancelled-lifetime references; or
prove that the consuming source attempt terminates without publication/reuse.
Owner: Luna's source/native lane; first required source owner:
candidate_scheme.rs Local restoration and execute_candidate_graph_plan.

This is a dependency/constructor-coverage boundary, not a code fix request or
a proved defect. No observer, simulated transition or arbitrary private struct
assignment can substitute for that source-authentic caller chain. Per the
contract, further dependent proof stops here rather than importing an unpinned
owner or silently assuming propagation. No new external dependency is added.

## 8. Application to R70-DRAIN-1 and mutual TODOs

R70's transfer statement can consume §§3–5 as a candidate local ownership
derivation: actual new replay children have separate operation/index rights;
queue transfer preserves them; Dispatch retains them despite currentness or
canonical requeue; successful terminal drain consumes them once; Running/Ready
and restoration references explain delayed reclamation. Completed rollback
uses a coupled frame/operation/workspace inverse, with lifetime-specific ID
reuse, rather than permanent numeric IDs.

**R70-DRAIN-1 remains OPEN.** The ownership subproblem first requires
R142-ERROR-OWNER-1, plus fresh independent review of this local derivation.
Even after that supplier is established, eventual consumer progress remains
separate: actual settlement/diagnostic/drain termination or successful
consumption must be proved where needed. No entry-validity, required-fiber,
source qualification, raw/canonical lineage or foreign-continuation premise
is discharged by conservation. R71's required lineage is unchanged.

Mutual TODO `R142-ERROR-OWNER-1`: Luna must pin/authorize the missing exact
caller owner before another producer reads it as a proof dependency. Required
input is actual Local/restoration/graph-plan error control and cursor state;
required output is the restoration-or-abort proof above. Falsifier: an authentic
source path catches an error after cleanup, reuses q>c state with no consumer,
or reuses a rolled-back numeric ID while a cancelled lifetime holder can act.

Mutual TODO `R142-RECLAIM-REVIEW-1`: fresh reviewer checks lifetime/index,
acknowledged Running/Ready, restoration pointer and transaction undo ordering
against the frozen local source proof. Multiple references are not automatically
multiple completion authorities. Falsifier: an actual constructor grants a
second consuming invocation, returns with an unowned right, or reclaims an
operation while an authoritative old holder can still execute. This is a
request to Luna, not a producer appointment of reviewers.

No authentic defect was established, hence **NO_SAFE_CODE_SLICE**. No
implementation/observer TODO is necessary before resolving source authority;
a later authentic defect would require a separate Luna repair contract.

## 9. Evidence, authorship, checks and frozen inputs

Prior work reused within actual premises: R70 by
`/root/r70_ordinary_extrusion_proof`, with complementary trace contribution
`/root/r70_extrusion_countertrace`, supplies the conditional extrusion and
correct successful whole-drive transfer boundary. R71 by
`/root/r71_raw_canonical_proof` supplies the separate open lineage boundary,
not completion or error ownership. Historical pins are not substituted for
current constructor bytes. R70's original W and later progress gaps remain.

Luna's current complementary messages identified transfer/completion guards,
Running/Ready and rollback/reclamation ordering. This author independently
read those pinned definitions and found the fallible pre-workspace rollback
boundary. Luna's contribution is source-audit authorship, not certification.
Rejected: q=n as completion, c=n as immediate reclamation, numeric ID as
permanent lifetime, all stored ack references as consumers, currentness as
acknowledgement, a restored session inferred from any Err, and tests as proof
that source constructors emit a proposed transition.

The exact 13 direct pins are:

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb  tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md
620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e  notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md
b7bc24379472bf840d111c379cbbf000516265c350d4ba55d47ecd06bb3fe2c6  tasks/agent-loop/inbox/20261019-r71-proof.md
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
```

Checks: static source/rule/proof reads, symbolic constructor/cursor analysis,
hash-only Python3 validation of 13 live pins and contract digest. No tests,
builds, compiler/solver execution, instrumentation, probes, Git, network,
external contact, nested CLI or delegation. Repository source authorship is
not reassigned by this proof; no Git author lookup was performed.

Stages: intake/pins complete; normal local ownership and transaction inverse
derivation complete as candidates; error/caller closure stopped at the named
dependency boundary. No full invariant or source-authentic counterexample.
Grant: 900 active seconds, zero Astra, no renewal. First explicit clock
2026-10-20 00:35:23 UTC; exact stop and conservative resource charge are in
the assignment handoff/final hash receipt. CPU/RSS and provider-side active
duration UNKNOWN. Only this theory file and the exact R142 inbox are written;
no scratch paths or descendant leases. Both freeze for Luna intake, and the
writer stops rather than claiming to keep running while waiting for authority.
