# R249: prior replay/restoration owner lifetime

Revision 1. **Candidate static source-native derivation; fresh review pending.**
Author `/root/sol_r249_prior_owner`; no coauthors or descendants.
Contract `tasks/agent-loop/sprints/prior-replay-owner-lifetime-r249.md`, current
SHA-256 `3a1d10f09a84dc3fc35621ee0c202672009349dadf2d386b00c06a49028757b5`.
Baseline `5903770e4ee58cbae726ae3424010ab8d0853e94` matched by reading
`.git/HEAD` and `refs/heads/yulang3`, without a Git command.

## 1. Parent, result and domain

The unchanged parent is Yulang inference soundness and its Rust implementation.
The application edge is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, specifically
`R248-PRIOR-OWNER-1` in R248 §8 and R245's current-return retention premise.
All accepted source forms, original Simple-sub A/B, arbitrary independent
satisfying assignments, shared witnesses, F1/FK1 and foreign-continuation
quantifiers stay unchanged. The frozen parent artifacts contain no concrete
fully quantified full-inference Lean declaration; none is invented here.
Lean declaration, theorem type and axiom dependencies: NOT APPLICABLE.
No checker was run under this source-only/no-Lean lease.

**Result: the successful-history storage component of R248-PRIOR-OWNER-1 is
DERIVED below and applied in §7.** The full semantic parent delta is zero.
No drain-progress, evidence-authenticity or soundness conjunct closes.
This is a source derivation awaiting independent review, not a checked theorem
or a production approval.

Use R248's exact accepted non-test successful-history domain: one initialized
candidate session, including successful histories that produce type diagnostics,
and the actual constructor paths reaching the two calls at lib.rs:14822/14835.
R248 §1's previously established exclusion of failed-route continuation is
reused with that premise only. This packet establishes no new error-restoration
or source-activation theorem. It covers each finite prefix of those successful
histories, with no assumption that remaining work eventually succeeds.

The informal source result type is:

```text
D-OWNER249:
For every such prefix H and authoritative pending handle h produced by the
actual constructors, every successful forward extension preserves h's
creation lifetime, operation/restoration payload, child index and current
owning queue/frame/parent until the designated transition consumes/moves it.
No reclamation removes an unconsumed child or live return barrier.
An exact child index can be successfully acknowledged at most once.
Consumed handles become receipts; their old numeric IDs need not stay live.
Cursor advances are exactly the transitions in §§3–6, not constant-cursor
equalities across the very transition which consumes that cursor position.

C-RETURN249:
R245 C-RETURN / R248 C-RETURN248 with their established entry projections,
D-OWNER249, remaining semantic/evidence premises and successful checked helpers
=> their stated current structural/retention/queue-transfer postconditions.
No eventual drain/acknowledgement/settlement follows.
```

## 2. Identity and the invariant actually preserved

Use ghost lifetime `(session, publication event, numeric ID)` for a replay or
restoration, and `(session, frame-push event, stack index)` for a typed frame.
These are proof notation, not proposed fields. In the successful domain the
shared checked allocation frontier never decreases, so no number is republished.
Replay and restoration IDs draw from that same frontier but live in distinct
maps. A number alone identifies neither the map nor a child. The rollback reset
at context:2214–2221 exists, so global permanent numeric identity would be false;
rollback is outside this successful-forward claim.

For a replay lifetime O write `n=children.len(), q=queued, c=consumed`.
The invariant at completed owner-transition boundaries is:

```text
0 <= c <= q <= n
retired => c=n
task, inputs, heads, prior, incoming_use, children[i] never change
i<c: completed history, with any remaining aliases passive receipts
c<=i<q: one transferred consuming authority in queue or a frame ack suffix
q<=i<n: the retained operation still owns the untransferred position
```

Distinct positions remain distinct even if their RelationIds are equal.
The map record's current cursor changes; a saved ack's `(operation,index)`
does not change. Neither numeric range checks nor the interval inequalities
alone prove the authority clauses. The actual creation/queue/frame paths below
supply them. `transfer_replay_child` accepts some already-queued indexes, so
its API is not itself a linearity proof.

For F the consuming vector is `F.replay_acks[F.completed_acks..]`.
The earlier prefix contains receipts. `prepared_acks` and `terminal_prepared`
are reservation/journal state. `F.current.replay_ack`, `replay_destination`,
Running/Ready, undo copies and source receipts are aliases or return barriers,
not additional invocations of `complete_replay_child`.

The adjacent mutations after transfer and before infallible queue push, after
pop and before ack-vector append, and after completion and before frame-cursor
increment are owned by that single nonreentrant transition. There is no fallible
call or dispatch between completion and its cursor increment. In particular,
an already-consumed physical vector entry in that microphase is a receipt even
before `completed_acks` catches up. This avoids a false statement about every
individual Rust assignment.

## 3. Creation, transfer and typed-frame retention

R248's initialized-inventory base is reused. Current corroborating constructors
are GraphState::default/start_candidate_graph (scheme:5,2528–2552), context
State::default (:1005), effect State::default/initialize (effect:298,652–661),
and the fresh empty session queue (lib:10126,10158). try_new_candidate
(lib:10501–10506) constructs that session before starting its graph. The sole
non-test graph-start call does not replace a graph with outstanding handles.

`candidate_context_begin_replay` (context:4411–4499) constructs its local child
vector, then publishes it at the current checked frontier with q=c=0,
retired=false, wait=Idle, restoration=None. The successful history's later
mutators never replace task/inputs/heads/prior/incoming_use/children. Interner
sharing of child relations does not modify those vector positions.

The None adapter (context:4598–4619) reads `children[q]` through
`replay_operation_queue_next` (:2521–2526), with exact task/relation and ack
`(that ID,q)`. It calls `enqueue_item(item,false)`. That function
(lib:15328–15355) prepares evidence, queue capacity and undo before transfer;
after transfer it only logs/pushes infallibly. Transfer (context:2536–2547)
checks Idle, not retired, c<=index<=q and index<n; the actual newly selected
index is q and advances q exactly once. The next adapter reads the new q, so
it cannot produce another asynchronous queue owner for the old index.
If q=n but c<n the None adapter returns without acknowledgement.

The synchronous Idle adapter (context:4522–4539) requires q=c and an empty
queue, constructs `children[c]` and starts one typed drain. Its initial enqueue
is the one transfer q->q+1; only afterward does it set the frame destination
and exact Running pair. No extra child is transferred by writing Running.
The supported constructor does not exploit the already-queued branch to create
a second consumer. The other direct item producers in lib and effect:1439
use replay_ack=None; rewriting, canonical requeue and all current
Function/Tuple/Record/Variant pending dispatch items use None
(lib:14575,14594,14693,14755,14806,14862,14970,15080,15105,15130,15155).

`begin_typed_drain` (context:2401–2413) pushes at old stack length with an empty
ack vector and zero cursors. `start_typed_drain` (lib:14302–14341) enqueues its
actual initial item. `step_typed_drain` Transport (lib:14411–14446) reserves the
ack vector and prepares the actual front ack before `pop_worklist` (:15271–15277).
Successful pop transfers the exact queue item into current and appends its ack
to that same frame. Queue pop removes the old consuming owner. Transport can
change the item's relation for semantic work; it does not rewrite the ack or
the original operation's children. Dispatch strips the local ack before
generating work (:14461–14473). It cannot copy the consuming right to a child.

Typed frames form a stack. Nonterminal/terminal owners require their index to
be the top frame. Successful pushes and pops above an older frame leave that
older slot and identity unchanged; no successful swap/remove/compaction exists.
`prepare_typed_drain_update` (context:2415–2430) replaces a frame by an exact
field/ack copy at the same index and retains the old allocation as dormant undo.
It preserves the creation identity and cursor, rather than creating another
dispatchable frame. Error-only frame cleanup is explicitly outside this domain.
The old fallback loop at lib:14100–14287 has an earlier return through
run_candidate_typed_drain when a candidate graph exists; it is not a second
simultaneous consumer of this queue.

## 4. Terminal consumption and Running/Ready

`candidate_step_typed_drain_terminal` (lib:14986–15051) requires the top frame,
Acknowledgements/ReturnReady, and
`completed_acks<=prepared_acks<=replay_acks.len()`; ReturnReady additionally
requires completed_acks=len. It prepares the next actual uncompleted entry
and selects only `replay_acks[completed_acks]` for consumption. After
`complete_replay_child` succeeds it increments completed_acks once (:15032–15037).
Earlier vector entries are never selected again. Later entries remain unchanged.

Preparation (context:2557–2578) checks index<q and index>=c and Idle or exact
Running. Actual completion (:2596–2607) checks **c=index**, with the exact
Running ack and q=index+1 when Running. It then advances c by one and sets
retired only at c=n. Therefore an earlier successful terminal action on j<i
can move c toward i but cannot change `children[i]`, saved i, or its holder.
A repeated completion for i fails c=i after the first advance. An attempted
out-of-order completion can fail; this argument asserts no progress from FIFO
alone and no ability to consume every remaining index eventually.

Running (context:4541–4549) retains exact ack/index/drain and validates the
frame destination, occurrence and cause. Its c may be i or i+1 with q=i+1.
Thus acknowledged Running is real: it retains a return barrier after the child
right has gone. Reclamation must preserve that barrier even for the last child.
ReturnReady preflight (:2583–2590) requires the exact Running tuple and c=q=i+1.
The terminal owner publishes Ready with its actual completion receipt before
popping the now fully acknowledged frame (:15040–15047). It does not drop any
unconsumed vector suffix.

The Ready adapter (context:4551–4571) validates the same operation/index and
c=q=i+1, checks that stack length equals the removed frame's former index,
prepares undo, changes wait to Idle, and returns Delivered. It calls no child
acknowledgement. This former frame index is a return-height boundary, not an
assertion that the popped frame still exists. Ordinary synchronous consume
loops on that same parent until Delivered/NoChild (:4575–4593); test-only
retained stepping does not supply an extra production pause/retry contract.

## 5. Restoration identity and saved cursor

`candidate_begin_bound_restoration` (extrusion:966–993) reserves its ID slot,
inserts the actual bound, captures the actual emission and opposite count,
and publishes its immutable owner/polarity/bound/emission/occurrence/cause with
next_opposite=0 and replay=None (context:2465–2476).
These payload fields are not rewritten by terminal processing, Ready or commit.

The current producer/consumer expression is
`candidate_step_bound_restoration_child` (extrusion:1013–1069). At cursor n<count
with replay=None it reads the live canonical owner's bound at **that saved n**,
constructs the ordered inputs/task, creates a fresh replay and links both
directions. `set_restoration_replay` (context:2498–2501) is called only here,
on the no-active-replay branch. `validate_restoration_replay` (:2481–2486)
checks both links before driving an active child. Neither terminal completion
nor Ready delivery increments the restoration cursor or replaces its replay.

Only after drive returns Complete, or retained stepping establishes returned,
does `advance_restoration` (:2502–2509) take that replay pointer and increment
next_opposite once. Hence active replay implies n<count, and the n=count
retirement branch is reached with no active replay. A retired restoration has
no remaining saved opposite-position obligation. Saved n/count and creation
owner identity are preserved; **the selected canonical endpoint is deliberately
re-read**, not asserted equal to an immutable creation-time bound list. This
does not close R71 or a general live-index/raw-slot lineage proposition.

The actual external persistent handle is LocalUseCursor.restoration
(scheme:1259–1264). `step_candidate_local_use` (:5430–5445) stores exactly the
freshly returned restoration ID, reuses it unchanged, and clears it/increments
next_bound only when the restoration returns its emission. The route owner
(:5321–5326) moves its Local frame temporarily and pushes it back before any
fallible result propagation. The production adapter supplies pause_after=None
(:5238–5269); its loop cannot return a successful injected pause.
Module FreshUse (:4515–4518) drives one locally held restoration completely
before the next bound. The test-only retained adapter (:5396–5429) is not used
as source evidence. A raw restoration variable may remain on the Rust stack
after completion, but no production loop executes that consumed handle again.

## 6. Commit, reclamation and passive receipts

`retire_replay_candidate` (context:2347–2355) removes an operation only when
retired AND Idle AND no nonretired reciprocal restoration still points to it.
If any child i is unconsumed, c<=i<n implies c<n, so retired is false by the
constructor/mutation induction. Reclamation therefore cannot remove that owner.
If all children are consumed but Running/Ready holds, Idle is false. If a live
restoration retains a completed replay, the reciprocal pointer blocks removal.
After pointer release and Delivered, that completed operation may legitimately
be reclaimed. Reclamation of an unrelated ID cannot mutate another record.

`commit_replay_operations` (:2361–2400), called on the successful transaction
branch (lib:9567–9601), uses that same guard for created/mutated candidates.
It checks replays against restoration **final state before removing retired
restorations**. It neither advances c/q nor rewrites immutable payload/children.
For retained frames it sets prepared_acks=completed_acks and terminal_prepared=false;
it does not reset completed_acks or the vector. The next preflight starts at
that completed frontier (lib:14376–14384), skipping any passive old prefix whose
operation has already been reclaimed. Undo truncation discards dormant inverse
copies, with no forward dispatch from them. Commit preserves all live rights
and return barriers while removing only completed ownership.

`SourceDrainReceipt` (context:105–117) can retain an ack/drain number after both
owners finish. `start_typed_drain` publishes passive attribution only after
enqueue succeeds. Terminal processing records its completion, not a new child
right. The additional current consumer-owner audit found:

| Owner | Actual use |
| --- | --- |
| shadow_apply:958–969,1070–1099,2370–2375,2540–2548 | Projects ack to numeric observation; classifies replay attribution or excludes it from a direct-source consumer; never dispatches it |
| candidate_receiver:4016–4046 | Compares exact passive receipt/completion fields; does not look up or acknowledge its old operation |
| candidate_effect:1437–1440 | Constructs a direct typed item with replay_ack=None |
| candidate_scheme:4515–4518,4948–4993,5238–5338,5430–5445 | Produces, retains and consumes the restoration handle as in §5; no additional ReplayChildAck constructor |

Thus **not every stored ack must designate a live map entry**. Completed vector
prefixes, source receipts and Ready's delivered predecessor are specifically
not counterexamples. Only an unconsumed right or an undelivered Running/Ready
barrier needs retention. A frame's reused numeric stack position similarly
does not revive an old receipt. Filename-only symbol searches located the
additional owners before admission; their bodies were read only after Luna
admitted all four hashes. Tests were not used as constructor evidence.

Together §§3–6 induct from the empty state over creation, transfer, pop,
dispatch, terminal acknowledgement, barrier move/delivery, restoration advance
and commit/reclamation. Other successful operations preserve these private
fields or construct replay_ack=None work. The contract's successful-prefix
reclamation/redirect/duplicate-consumption falsifier was not established.

## 7. Exact parent application and remaining obligations

Before: R248 §6 established new local operation ownership but §8 left prior
operation/child/cursor retention conditional on later successful terminal
history. R245 §5 could describe the current final replay handoff while keeping
that historical retention premise open.

After: substitute D-OWNER249 at exactly that storage premise. Prior unconsumed
acks at either real call still designate the immutable original child position
of their same operation lifetime; a pending restoration still owns its same
active replay and saved opposite cursor until its designated advance; a pending
frame stays at its same live stack slot until all its ack entries are completed.
Earlier completions may advance c and completed_acks according to §4, but do
not redirect saved handles. Running/Ready explicitly supplies retention after
child consumption. R248 §8's prior-owner storage row can therefore be DERIVED
on this domain, independently of eventual drain progress.

Apply that substitution to R245's current C-RETURN (§§4–5), using R248's derived
entry projections. At the final provenance-None extrusion pass
(extrusion:575–593), the adapter only appends new indexed items; existing outer
queue items and the frame's pending ack suffix retain their own rights. A new
nonempty replay has q=n,c=0 after its full local drive. Neither extrusion return
nor the caller's rewritten-item enqueue (:14862) executes/acknowledges those
children. The conditional structural return conclusion stays exactly R245's;
there is no change to traversal, tuple/record/variant coverage or semantics.

No lifetime equation for the stated successful-owner component remains open
within the admitted owner set. **The full parent remains OPEN**, including:

- Authentic ordinary seed, processing antecedent, FreshUse/replay-use and
  origin-to-fiber evidence association: R248 §5's explicit coverage gaps.
- R71 raw physical slot/canonical fiber coverage and source/native semantic
  correspondence, which immutable child identity does not establish.
- `R70-DRAIN-1` actual drain/diagnostic/intrusion settlement and consumer
  progress, and independent F1/FK1/foreign-continuation obligations.
- Full inference/evaluator soundness, hygiene and generalization, with the
  original arbitrary-assignment/shared-witness quantifiers.

Mutual TODO `R249-OWNER-REVIEW-1`, owner Luna: fresh independent review of this
current source derivation and its R248/R245 application. Falsifier: an actual
accepted non-test successful prefix removes an owner with an unconsumed right,
changes its original child position/cursor without the named consuming step,
or successfully acknowledges one lifetime/index twice. Synthetic ID assignment,
passive stale receipts, and cfg(test) retained retry are insufficient.
`R248-EVIDENCE-AUTH-1`, R71 and R70-DRAIN-1 remain with their existing owners;
this TODO grants no path, code or semantic authority.

Implementation disposition **NO_SAFE_CODE_SLICE**: current context terminal/
reclamation and extrusion restoration/emitter owners were inspected, with
their actual lib consumers; no source-qualified defect supports production edits.
Next boundary is Luna's review/intake of these frozen bytes, not another
conditional restatement of the same storage equation.

## 8. Reuse, pins, checks and stop receipt

R248 author `/root/sol_r248_entry_inventories` supplies the established successful
entry/domain projections; R245 author `/root/sol_r245_entry_return` supplies
the current return simulation with its actual residual premises. R142 author
`/root/r140_action31_proof` and its credited Luna contribution supply only the
historical method: distinguish right/receipt/barrier and transaction lifetime.
Its older source hashes, private caller coverage and R143 bounded result are
not imported as current proofs. R143 was not read. No producer/coauthor can
independently certify this result.

All initial nine pins and baseline matched before substantive source claims.
An initial hash-only command used unavailable `python`; it produced no hashes
and was rerun with python3. The initial batched artifact reads preceded that
successful hash check; relied-on passages were reread after verification and
no source claim was based on unchecked bytes. Some combined read output was
truncated; producer/consumer bodies were reread in bounded chunks. The four
additional owner hashes and revised contract matched after explicit Luna
admission and before their body reads. No unadmitted source owner was read.

Checks were read-only ref observation, SHA-256, source/symbol searches,
constructor/cursor induction and final output whitespace checks. No Lean,
Rust/build/test/probe/Cargo/benchmark, production edit, Git command, external
contact, runtime/quarantined access, descendant, scratch/cache/generated output
or model switch. Governance reads included the root maps, applicable skills,
rules, README and authoritative 2026-10-11 inference principles
(`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`).

Requested model/effort: `gpt-6.1-sol/high`; observed model/effort: UNKNOWN.
Actual worker `/root/sol_r249_prior_owner`, session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Parent assignment and admission messages
supply the current launch/work receipt. Budget <=2400 active seconds; provider
active duration/CPU/RSS UNKNOWN. First explicit clock 2026-11-02 04:26:25 UTC;
the final handoff records freeze time and conservative charge including setup.
No renewal or unobserved resource refund.

All frozen input SHA-256 pairs (recomputed MATCH):

```text
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
bc8ce026a4027110ee36c35178ec129d778bad2e7274c2789fdc5dad0a142713  notes/theory/2026-11-02-extrusion-entry-inventories-r248.md
984bb9b3f878e7048efdf2aa1b75615b32b45426bad095b56674210caf6c21d3  tasks/agent-loop/inbox/extrusion-entry-inventories-r248.md
7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e  notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md
647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322  tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md
5f1715db8ccef8777f89d9b64e8625efead68974be53beb8f55a84a86a014a2c  notes/theory/2026-10-20-r142-replay-completion.md
cbaa0c7e79ca9c04b4325b8358ec17664deb51eb4dc620be0c7e242041b44c26  tasks/agent-loop/inbox/20261020-r142-proof.md
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade  crates/yu-solver/src/candidate_receiver.rs
```

All new paths are exactly this theory note and
`tasks/agent-loop/inbox/prior-replay-owner-lifetime-r249.md`; scratch NONE.
The theory hash is in that handoff; the handoff hash is returned externally to
avoid recursive self-hashing. Writer state after final hashes: **STOPPED /
WRITES_STOPPED**. No descendants or unresolved descendant leases. Revision 1
freezes both outputs for Luna intake; review/adjudication/integration remain
pending and no further work continues under this assignment.
