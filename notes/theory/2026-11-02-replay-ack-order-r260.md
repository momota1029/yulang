# R260: consuming replay rights, frame ownership and terminal order

Revision 1. **Candidate source-constructor proof and application; independent
review pending.** Author `/root/sol_r260_replay_ack_order`; no coauthors or
descendants. This is a source derivation, not a kernel-checked theorem or
production authority.

Contract: `tasks/agent-loop/sprints/replay-ack-order-r260.md`, SHA-256
`741296c13bb3af9d46580c2340f377c9da8a42dd680b2df5098a1b13ecc381cb`.
Fixed baseline `cb00f3329cd02b0049a88467945b118d1c2dec75`; Luna's assignment
receipt identifies the subsequent administrative checkpoint
`6263619b003535528ac229e3f052e40f1d754312`. No Git/ref command was run here.
All 36 inherited direct pins were revalidated before source-body inspection;
all nine separately pinned R249/R250/R259 inputs also matched.

## 1. Parent, exact result and domain

The unchanged parent is Yulang inference soundness and its Rust implementation,
with the original accepted source forms, graph modes, Simple-sub A/B,
independent satisfying assignments, shared witnesses, F1/FK1 and foreign
continuations. Immediate edge: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` /
`R70-DRAIN-1`, specifically the ordered-authoritative-ack premise of R250
SUFFIX250 at an **actually reached** Diagnostics cut. R70's conditional local
extrusion result does not execute its transferred replay children.

Use exactly R249 §1 / R250 §1's non-test, initialized successful-forward
session domain, including successful prefixes producing type diagnostics.
No suffix completion is assumed. Failed-route continuation, synthetic states
and test-only retained-resume transitions provide no source evidence. This
inherited domain does not assert that every accepted program has a successful
execution; successful helpers and eventual Diagnostics entry retain their
separate obligations. No source form or semantic rule is removed here.

The source result proved below has this informal type:

```text
ORDER260:
For every finite prefix H in that domain and every actual Replay operation O,
each transferred, unconsumed child position (O,i) has one consuming owner.
The raw operation lifetime, i, current q/c, and owning frame or queue position
are retained independently of the child's executable RelationId.

An ordinary asynchronous operation's pending rights are a prefix in one frame
followed by an increasing suffix in the shared queue, or the initial growing
queue batch while its producer is executing. No pending right of that O is
in a different frame. A restoration operation transfers at most one pending
child; its successor cannot transfer before this child's exact Ready delivery.

Consequently at any actual Diagnostics entry of top frame F, its uncompleted
ack suffix is authoritative and, projected to each operation O, begins at O.c
and is consecutive in original child-index order. No predecessor of one of
these rights is pending in a suspended outer frame. Later same-O consumption
cannot overtake that predecessor in a nested frame.
```

The terminal application in §8 removes that one premise from SUFFIX250. Valid
diagnostic references, successful helpers and actual eventual Diagnostics entry
remain explicit. Full semantic parent and A/B delta: **0→0**. There is no
whole-inference Lean declaration in the frozen parent artifacts; Lean theorem
type/axiom audit: NOT APPLICABLE, checker NOT RUN under this source-only lease.

## 2. Rights and copies are distinct

Identify O by `(initialized session, publication event, raw ReplayOperationId)`
and F by `(session, frame-push event, stack index)`, as R249 does. Successful
forward allocation never republishes a replay number. A reused frame index
after pop is a different frame lifetime. These are ghost proof names, not new
compiler fields. Let `n=O.children.len`, `q=O.queued`, `c=O.consumed`.

A consuming right is the authority for the unique future successful
`complete_replay_child(O,i)` transition. Before transfer, the operation owns
positions `[q,n)`. After transfer, the owner is an actual queue item or one
uncompleted entry of one live frame's `replay_acks`. The frame prefix before
`completed_acks` is a receipt. `current.replay_ack`, `replay_destination`,
Running/Ready, source receipts and undo snapshots may copy the bits `(O,i)`;
they are not additional terminal dispatch inventories.

Thus `0<=c<=q<=n` and exact-index completion checks are necessary but insufficient.
`transfer_replay_child` deliberately permits some already-queued indexes
(context:2536–2547). Its API alone is not a linearity theorem. The actual
constructors/calls in §§3–6 establish the stronger unique-owner and frame
placement clauses. Adjacent transfer/push, pop/ack-append and completion/cursor
increment are single nonreentrant owner transitions; temporary Rust local
copies inside them are not additional schedulable rights.

## 3. Constructor and adapter coverage

The initialized empty queue/graph base is supplied by reviewed R249, corroborated
by lib:10126–10158 and scheme:2528–2552. The only non-test Replay operation
constructor is `candidate_context_begin_replay` (context:4411–4499). It builds
an ordered finite child vector, publishes a fresh ID with `q=c=0`, Idle and
`retired=false`, and never subsequently replaces that vector. The empty vector
has no child right; its explicit retirement does not consume a nonexistent one.

| Actual owner/call | Child/ack construction and continuation |
|---|---|
| `candidate_replay_bound`, extrusion:1070–1112 | Calls `begin_replay(...,false)`, then `drive_replay(id,None)` before visiting the next opposite bound. This is the sole non-test asynchronous operation producer/driver pair. |
| Restoration, extrusion:1004–1068 | On `replay=None`, constructs `begin_replay(...,true)` and stores reciprocal restoration/replay links; on the active branch validates them and calls `drive_replay(id,Some(provenance))`. The ordinary adapter uses `retain_child_step=false`. |
| Async item constructor, context:2521–2526,4598–4620 | Reads exactly `children[q]`, saves raw `(id,q)` and sends that one item to `enqueue_item(item,false)`. |
| Sync item constructor, context:4516–4540 | Requires Idle, `q=c`, and an empty queue; reads `children[c]`, saves `(id,c)` and calls `start_typed_drain`. It installs the exact destination/Running pair after initial enqueue succeeds. |
| Module/local FreshUse, scheme:4513–4518,4948–4993,5430–5445 | Produces/restores bounds through the restoration owner above. Module use drives one restoration to its emission before the next. Local use retains that exact restoration ID and advances only after its emission. It constructs no alternate consuming ack. |
| Direct source/entry items, lib:11716–11723,11808–11816,14070–14076; effect:1437–1440 | Explicit `replay_ack=None`. Source generation can choose task/relation/provenance, but cannot create a replay consuming right through these items. |
| Structural/canonical/rewrite items, lib:14575,14593–14595,14688–14694,14750–14756,14801–14807,14861–14863,14965–14971,15080,15105,15130,15155,15319–15325 | Explicit `None`; only the four structural pending-item adapters push these at the front. |

`ReplayChildAck`'s non-test struct-literal constructors are precisely the async
queue-next and sync Idle expressions above. The extra `replay_operation_next`
constructor (context:2514–2520), closure compatibility replay harness
(:4377–4410), and retained child stepping caller (scheme:5396–5429) are
`cfg(test)` and are not premises. R249 §6's reviewed passive-consumer audit is
reused for the receiver consumer; its source owner was not newly read or
admitted here. Current admitted `shadow_apply`/source receipt consumers only
observe attribution. R249's proof is the dependency for that exhaustive
passive-consumer fact, not a new unpinned receiver-source argument.

This is a field/call-graph construction proof over all source forms using
these owners; it does not enumerate just one program or one flat drain.
Filename-only discovery of `ReplayChildAck`, replay begin/step/consume/drive,
transfer/complete and `typed_worklist` across the solver source found no other
non-test owning file beyond the admitted context/extrusion/lib/scheme paths.
The additional matches were test files, whose bodies were not read or used.
Ordinary and scoped relation payloads take the same ack constructors. If no
candidate graph is present, these replay rights/frames do not exist; the
initialized graph-present claim does not infer a theorem about the other
solver's semantics. The old loop in lib:14110–14287 is bypassed by the
graph-present return at :14107–14109, so it is not a second consumer.

## 4. Async batch invariant, including partial transfer

Fix a newly published ordinary operation O. During its `drive_replay(None)`
call the loop at context:4625–4650 calls the None adapter repeatedly. That
adapter selects q, not c, and `enqueue_item(...,false)` calls transfer before
an infallible push_back (lib:15328–15355). Starting q=0, induction on these
iterations gives the queue projection for O exactly `[0,1,...,q-1]` and no
frame entry for O. The operation continues to own `[q,n)`.

The loop contains no worklist pop, typed step, frame start, semantic dispatch,
restoration driver or commit. Evidence admission, reservation, journalling and
resource sampling in enqueue do not run semantic work. In particular ack items
already have `Some(children[q])`, so enqueue's missing-relation evidence arm
does not even run for this batch. q advances once at transfer; no intervening
call can ask for the old q again before the infallible push. This justifies
nonreentrancy rather than assuming FIFO makes it true.

On whole-call success, nonempty O has `q=n,c=0`, all children are on the queue
and the driver returns Queued only after queue-next is exhausted. At any strict
prefix with `q<n` the active producer still owns the continuation. There is
no supported successful yield at that prefix to a typed frame/other producer.
An error can interrupt transfer, but resuming such a route is not evidence in
the inherited successful-forward domain. This does not discard the prefix:
its queue prefix and retained operation suffix have the owners just specified.

After the batch returns, further None-adapter calls on the same O could read
no new child because q=n; the actual caller has already proceeded past its
local ID. Sync transfer of such a pending operation is blocked by q!=c.
The ordinary source call graph never changes this O into a restoration; the
restoration constructor creates a fresh ID. Each source invocation that emits
another operation, even with equal inputs/RelationIds, has a distinct lifetime.

Let `Q|O` denote the ack-bearing projection of the shared queue onto O. Once
semantic execution resumes, the inductive configuration for this O is:

```text
O is wholly unconsumed: one frame F holds [0,k), Q|O=[k,n), 0<=k<=n;
or k=0 and there is no frame holder yet.
Later terminal progress replaces the frame's first positions by receipts;
the remaining projection begins at the updated O.c.
No other frame contains an unconsumed right for O.
```

This statement is proved with the nesting argument in §5, not just queue order.
For an asynchronous O all its children are transferred before its first pop;
new operations may interleave in Q, but can neither add to nor reuse O's batch.

## 5. Queue moves, front work and the nested-frame exclusion

The following successful forward transitions preserve that configuration.

* Queue storage growth (`reserve_worklist`, lib:15199–15218) moves `old.drain(..)`
  into the replacement in order. The retained old allocation is empty; it is
  not another active queue. Workspace PopFront undo holds a dormant item copy.
  Rollback queue clear/inverse actions (:10044–10051,15279–15314) are outside
  this successful-forward induction; commit drops undo without replaying it.
* Back append of another batch preserves `Q|O`. Front insertion by Function,
  Tuple, Record and Variant adapters (:15060–15160) takes a pending item whose
  constructor sets `None`. Deleting ackless work from the sequence therefore
  leaves the old ack order unchanged. It may delay O, but cannot overtake or
  duplicate an O right.
* Only Transport pops live work. It reserves/prepares the exact front ack,
  uses `pop_worklist` (:15271–15277), stores the popped item as current and
  appends its unchanged ack to the same top frame (:14411–14446). Before pop
  the queue owns it; after append that frame owns it. Preparation creates
  journal capacity, not a terminal consumer. No source call occurs between
  removal and append.
* `prepare_nonterminal_drain` (:14365–14389) and the terminal owner require
  the frame to be the current top. A suspended outer frame cannot pop items
  while a nested frame is active. Frame clone-for-undo preserves identity
  and fields at the same index (context:2415–2430), not a second active frame.

Now suppose F already holds the initial O prefix `[0,k)`. A successfully
started nested G requires an empty **shared** queue at `start_typed_drain`
(lib:14291–14295); the replay Idle adapter separately checks this condition
(context:4528). There are two possibilities:

1. k<n. The unchanged projection `Q|O=[k,n)` is nonempty, so G cannot start.
   There is no successful constructor transition to a state with the later
   O child in G and its predecessor in F.
2. k=n. Every transferred O child is already owned by F. O's q=n, and no
   remaining child can be generated for that same operation. G can start but
   has no O right; fresh replay activity inside G uses fresh operation IDs.

If no frame has yet popped O, its nonempty batch similarly prevents a new
frame start. If O's whole batch is generated inside G, the same proof applies
with G as its holder; O did not exist in the older F. A finite prefix inside
batch construction cannot push G by §4. This covers all frame depths by
induction on successful push/pop events. Ordinary nested source drains have
ackless initial items and the same empty-queue gate; sync nested replay has
the additional gate in §6. Popping an unrelated G restores F; it does not
move any F acknowledgement into G or reset its cursor.

Thus a pending async O may span F plus its queue suffix, but never two frames.
This is the required obstruction to overtaking across nested frames. It is
stronger than the numeric inequality `c<=q`, and the source empty-queue
precondition is not being replaced by a new source-language restriction.
Whether accepted inputs always satisfy each required successful helper/start
condition is a different obligation and is not discharged by this argument.

## 6. Sync restoration: one child and a return barrier

The restored operation has a separate sequential protocol. In Idle, the real
adapter requires `q=c`, an empty queue and no live previous child. It enqueues
exact `(O,c)` as the new frame's initial item, transfers q to c+1, then records
Running with that ack and that frame index (context:4516–4540). The start's
seed/receipt construction supplies relation/provenance, not another ack right.
The initial queue entry must be popped into that frame before it can reach
Diagnostics. The destination and passive source receipt copy its number only.

While Running, transfer rejects further children because waiting is not Idle.
The Running adapter checks the exact `(ack,drain_index)` and frame destination,
occurrence and cause (:4541–4549); only the specified top frame can step. If
that frame starts a deeper frame, the deeper frame cannot acquire a successor
for O: O remains Running, and all new source replay operations have fresh IDs.
There is only this one O right, so there is no same-O queued suffix to steal.

Successful terminal completion consumes precisely this i, setting `c=q=i+1`.
Running intentionally survives that event: it is now an uncompleted return
barrier, not an unconsumed child. ReturnReady validates exact Running and that
cursor equality (context:2583–2590), publishes Ready and pops the fully
acknowledged frame (lib:15040–15050). Ready delivery checks the same O/i and
the restored stack height, sets Idle and returns Delivered without calling
completion (context:4551–4571). Only then can the loop start child i+1.

Restoration `advance_restoration` does not bypass that protocol. The owning
active branch advances its saved opposite cursor and releases the replay
pointer only after drive returns Complete (extrusion:1027–1041); Complete
requires retired AND Idle (context:4631–4642). Publication of the next replay
for another opposite is a new lifetime. Module/local FreshUse retain this
same ordering (§3); the production local adapter has no injected successful
retained-child pause (R249 §5). None of these claims concern arbitrary foreign
continuations or prove F1/FK1.

## 7. Rewrites, aliases, terminal consumption and commit

`union_sources`/`intern_sources` (context:3515–3535) union and canonicalize
source-set data before child publication. `relation_with_scoped`
(:3481–3513) can intern equal RelationIds. Neither operation reads/writes the
q/c/wait/frame inventories. Replay's vector appends a child only after the
actual dependency rule; ordinary duplicate dependencies may suppress an
append, while incoming uses retain their own children (:4463–4481). Index i
always means the resulting vector's actual position. Equal relations in two
positions remain two separate rights `(O,i)` and `(O,j)`; source origins and
dependency witnesses are not equated by this proof.

Transport can select a derived relation while retaining the original task and
ack (lib:14448–14458; context:4186–4204). Context execution may enqueue new
operations; its owning batch argument is §4, with new IDs. Dispatch explicitly
clears the local item's ack **before** calling semantic dispatch
(lib:14461–14473). Canonical alias work, memo duplicates, retained/new whole
Value rewrites and structural children therefore either emit ackless work or
newly constructed operations. The frame retains the original O/i even if its
raw relation is aliased, its task is already memoized, Context consumes it,
or dispatch returns early. No canonical equality converts a relation or source
receipt into an ack transfer. The proof concerns protocol completion, not
semantic adequacy/authenticity of those derived relations.

For each top frame F, terminal consumption selects only
`replay_acks[completed_acks]` (lib:15031–15037). Its per-operation projected
order follows §§4–6. Therefore that ack's index equals its retained O.c.
`complete_replay_child` (context:2596–2607) checks that equality, plus exact
Running/q=i+1 when applicable, and advances c once. The adjacent frame-cursor
increment changes that physical vector entry into a receipt. No fallible call
or semantic reentry separates those two updates. Subsequent selections skip
it. An attempted repeated successful consume for i is impossible because c
has advanced. The argument supplies the equality **before** the check; it
does not infer order by conditioning on the check having succeeded.

R249's reviewed retention result supplies continued owner identity, operation
payload, child index and cursor under these transitions. An unconsumed owner
cannot be reclaimed: retirement is possible only at c=n. Running/Ready blocks
reclamation of the exact return barrier, including for the last child.
Successful `commit_replay_operations` (context:2361–2400; lib:9568–9598)
retains the ack vector, stage, completed cursor, child vector and q/c. It
resets preparation to completed_acks and clears terminal_prepared; later
preflight skips consumed receipts and prepares only the remaining suffix.
Discarded undo snapshots never dispatch. Hence even a retained partial terminal
state cannot recreate a consuming right or reorder its remaining projection.
The actual non-test synchronous loops run through these local terminal steps;
this preservation observation does not claim a test-only pause is production.

Frame removal requires ReturnReady with completed_acks=len, so it drops no
right. Reclaimed completed operations and old source/vector receipts may
leave raw ack numbers in passive storage. They need not refer to a live map
entry and are not violations of ORDER260. Only the unconsumed suffix and
undelivered barrier have the live-retention obligation.

Together the empty initialized base, exact constructors, nonreentrant batch
iterations, queue moves, top-frame pop, ackless expansion, nested push/pop,
single-child delivery, terminal advance and commit/reclamation form an
induction over every successful transition that can affect consuming rights.
Other source work preserves these private inventories or enters through the
listed constructors; the inherited R249 passive audit covers observations.
No accepted-prefix ownership/order counterexample was established.

## 8. Application at the unchanged R70 terminal edge

Let H reach Diagnostics in actual top frame F. This transition is taken only
from Transport with no popped item after settlement and with no dirty pending
intrusion work (lib:14411–14445). In particular the actual shared queue is
empty. The frame has collected every ack it popped; before its first terminal
step completed_acks=0, and a later retained terminal state uses its exact
uncompleted suffix instead.

For every async O represented in that suffix, §5 forces its pending batch into
F alone. Its per-operation projection is the remaining consecutive sequence
beginning at O.c; no earlier same-O right is in an outer frame. For a sync O,
F holds its sole Running child at O.c and q=c+1; a later child has not yet
transferred. Other synchronous destination barriers and outer operations may
exist, but they do not supply predecessors of an F-held right. R249 retains
these exact live owners and immutable child positions. This establishes the
ordered-authoritative-ack inventory required at this actual cut, including
the destination's eventual exact ReturnReady check.

Now instantiate reviewed R250 SUFFIX250 with that inventory and R249 retention.
With its **still required** valid finite diagnostic references and successful
fallible helpers, Diagnostics adds no typed work or pending merges, so the
ack vector stops growing. Terminal steps consume its ordered suffix and
decrease R250's `(m-completed_acks)+2` rank through ReturnReady and removal.
If there is a sync destination, exact Ready delivery follows without consuming
twice. This is a source-constructor application of the premise, rather than
another conditional lemma assuming that same order.

Before R260: SUFFIX250 required ordered authoritative acknowledgements as an
unproved all-source condition; R259 supplied it for one reviewed exact-HIR
drain only. After this candidate proof: ORDER260 supplies that protocol premise
on every **actually reached** cut in the inherited initialized successful-forward
domain. No use is made of R259's route-specific finiteness/carrier argument
to obtain a universal result. R259 is context for the gap, not a substitute
for this constructor induction.

Remaining premises and owners remain separate:

* Actual eventual Diagnostics entry: dispatch/extrusion/settlement/replay
  producers, including R250's unfunded cross-invocation birth charge and later
  source investigations. ORDER260 does not bound pre-Diagnostics work.
* Diagnostic child-reference/memo validity and report coverage: diagnostic
  edge producers and `complete_diagnostic_delta`/witness replay. ORDER260
  gives no origin/fiber authenticity or diagnostic adequacy.
* Successful checked helpers and initialized successful-history admissibility:
  their original source/consumer owners. The exact empty-queue gates used above
  do not prove all accepted programs can pass those gates.
* R70's other W clauses, R71, evidence origin/fiber/antecedent/FreshUse
  authenticity, full Call/hygiene, generalization, F1/FK1, foreign continuation,
  source/evaluator soundness and A/B: original owners and independent quantifiers.

No production defect or implementation change follows. `NO_SAFE_CODE_SLICE`:
the actual context replay/restoration owners and lib queue/terminal owners
were inspected; no accepted-source approved-clause violation was demonstrated.

## 9. Reuse, checks, resources and freeze

Reused with exact premises: R249 successful-history storage/return-barrier
derivation by `/root/sol_r249_prior_owner`, independently reviewed PASS per
its pinned admission; R250 SUFFIX250 by `/root/sol_r250_drain_progress`,
independently reviewed PASS per its pinned admission. R70 author
`/root/r70_ordinary_extrusion_proof` and complementary contributor
`/root/r70_extrusion_countertrace` supplied the conditional local extrusion
result; Luna's reviewed closeout keeps operation/parent gates OPEN. R259
author `/root/sol_r259_ordinary_drain_closure` and fresh reviewer
`/root/sol_r259_independent_review` supplied one route certificate only.
No producer/coauthor here independently certifies this combined argument.

Rejected methods: flat FIFO alone; c<=q<=n alone; using the completion guard
as proof of its own progress precondition; equating RelationIds with child
positions; treating prepared/current/destination/source/undo copies as
independent rights; treating q=n as completed replay; using one local frame
to discharge foreign continuation; importing test-only pause/retry evidence;
inferring global termination or diagnostic authenticity from this protocol.

Skills applied: yulang-proofs and yulang-proof-portfolio; the sprint skill/rules
govern this leaf packet. No Lean formalization/checker audit was assigned.
Three substantive stages: constructor/transfer inventory; ownership/order
induction and R70 application; artifact/dependency validation and freeze.

Actual active-work receipt sent to Luna at the start: identity
`/root/sol_r260_replay_ack_order`; first explicit clock
2026-11-02 08:25:14 UTC, with initial startup reads shortly before. Requested
`Sol/high` per assignment; exact requested runtime model identifier UNKNOWN
to this leaf. Observed model/effort/session UUID UNKNOWN because runtime
metadata is not exposed to this leaf. No descendants.
Provider active time, CPU and RSS UNKNOWN. Hard grant 2400 active seconds;
terminal clock and conservative charged interval are in the frozen handoff.
No expansion, reset, carryover or in-place model switch.

Checks: read-only SHA-256, bounded symbol/body inspection, constructor/transfer
case proof, source-to-terminal application, and final artifact whitespace/hash
checks. An initial `python` hashing command failed before doing work because
that executable is unavailable; `python3` performed the same read-only check.
No Lean/build/test/probe/Cargo/benchmark, production/test/expectation edits,
Git, external contact, central state, runtime/quarantined access, scratch or
cache output. Only the two leased artifacts are written. No new dependency.

Next in-scope step is Luna's fresh independent review of the frozen constructor
proof and application. Mutual TODO `R260-REVIEW-1`: review §§3–8 against the
fixed pins, especially nonreentrant full async batch and empty-queue nested
frame exclusion. Falsifier: an actual non-test successful constructor lets
one O's pending rights enter two live frames, requeues an ack-bearing dispatch
child, or selects an ack above O.c at an actual Diagnostics cut. This TODO
grants no production or additional file rights. `R260-REMAINDER-1`: Luna keeps
the distinct remaining §8 premises with their original owners; do not close
R70-DRAIN-1 or promote production from a reviewed ORDER260 alone.

All new paths: this note and `tasks/agent-loop/inbox/replay-ack-order-r260.md`.
Scratch/generated/unresolved descendant paths: NONE. Revision 1 is frozen
only with the external final hash/stop receipt. After that receipt the author
is **STOPPED / WRITES_STOPPED**; review/adjudication/state/Git belong to Luna.

## 10. Frozen dependency manifest

The inherited 36-path manifest is
`tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, SHA-256
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
The exact pairs and separately admitted reviewed inputs follow; final
revalidation is recorded by the handoff. Manifest inclusion is a dependency
pin, not a claim that every inherited historical artifact was newly reread.

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf  crates/yu-solver/src/candidate_value_graph.rs
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
87e9af00bfc206fb22a29b776c634acc94e75e0283257f8bba9d513d23a90574  notes/theory/2026-11-02-ordinary-drain-progress-r250.md
8b52e40891096ca6086db636165b276a3f57630091e090e3e181f390cd178c65  tasks/agent-loop/inbox/ordinary-drain-progress-r250.md
1bc35d4749290a6a583ce079e80a95ed96c60a9ff81db06e2dfac25e74ad2af5  notes/theory/2026-11-02-ordinary-birth-charge-r251.md
8aaa7b025dd89e2f4edc0fb12ae69a9e1934ac7709c6bf719fae9a1e6c234429  tasks/agent-loop/inbox/ordinary-birth-charge-r251.md
30aea41a739866e73b6220754e05a8eb96388720046f87482714d530623cda23  tasks/agent-loop/sprints/ordinary-birth-charge-r251.md
057550871430512b1032ef166eed49f86661eb98150e462319978ffc36b19944  notes/theory/2026-11-02-source-pair-credit-r252.md
f6c9c7918a9897be243654d7f6cfc681b1428b8c1d3da0714dcd605afeba84ea  tasks/agent-loop/inbox/source-pair-credit-r252.md
af9e519531a9855cfd01b4bca2c709416bb4f1d4aa4bdcdd1eb5641749effd84  tasks/agent-loop/history/20261102-r252-admission.md
c54b7c3da6e93e358b410569d628369a4b7a6e51759e4015dd761fd65d7cd057  tasks/agent-loop/sprints/source-pair-credit-r252.md
15458a226a3949e67b747540b1279dd054f1e280418c5746610bda4ce2933655  notes/theory/2026-11-02-receiver-ancestry-renewal-r253.md
425b84efd46b590ecfddc69d24d7c75835be280cfaa7078fed66e5d0547eb680  tasks/agent-loop/inbox/receiver-ancestry-renewal-r253.md
f0ef140587ce60f7c54b534ddaaf26fd17276359d898cf829e4ef368b435d382  tasks/agent-loop/history/20261102-r253-admission.md
b5a6599eb29d3d451ca31ac621d9dd83cecfea162202ca0d9d0696d282b6e0d3  tasks/agent-loop/sprints/receiver-ancestry-renewal-r253.md
5c7d3059005dc03be58fde7528519b9d47674c80cedf48d48983c29242fe1bce  notes/theory/2026-11-02-opposite-leaf-settlement-r254.md
efb491889d367cf284281614d0212d4cd3219680cbf278008be572cccdcced8e  tasks/agent-loop/inbox/opposite-leaf-settlement-r254.md
fc14d86eb14d60212b5854e7bbbd155f8fff54cf57beaf3302af74d041a22b7e  tasks/agent-loop/history/20261102-r254-admission.md
c1a95f80e618eac5e7e674dec71aad058b6fc899ed25683e71625a4d81b09bc8  tasks/agent-loop/sprints/opposite-leaf-settlement-r254.md
b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e  crates/yu-hir/src/shadow.rs
7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1  crates/yu-hir/src/module/local_source.rs
6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646  crates/yu-hir/src/module.rs
```

Separately pinned reviewed inputs:

```text
3a1d10f09a84dc3fc35621ee0c202672009349dadf2d386b00c06a49028757b5  tasks/agent-loop/sprints/prior-replay-owner-lifetime-r249.md
615121840e60fe86b493a3e9b9236783770cc8bbd002cea6c4e41b29d60e90e9  notes/theory/2026-11-02-prior-replay-owner-lifetime-r249.md
381d7d65f8de903611e9896fc56498a4ce005b551c08d073b63e9c891657a246  tasks/agent-loop/inbox/prior-replay-owner-lifetime-r249.md
484f939f5c212e54c0efef3ab5c3496c9058be02669db1c1ab71e91757f4f95d  tasks/agent-loop/history/20261102-r249-admission.md
9772cca143817a6d2a5a803334f5b5047b9846154a57b3cd95be67cb5c837c7a  tasks/agent-loop/sprints/ordinary-drain-progress-r250.md
87e9af00bfc206fb22a29b776c634acc94e75e0283257f8bba9d513d23a90574  notes/theory/2026-11-02-ordinary-drain-progress-r250.md
8b52e40891096ca6086db636165b276a3f57630091e090e3e181f390cd178c65  tasks/agent-loop/inbox/ordinary-drain-progress-r250.md
b1e3b90b118474f2704f668cb14bcad350b5579dd0c114d31fda16f77403c2ad  tasks/agent-loop/history/20261102-r250-admission.md
940ea216758abd2721fb3d595d5258249e1553142314f7560fffad91a93db947  tasks/agent-loop/history/20261102-r259-admission.md
```
