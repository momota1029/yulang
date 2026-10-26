# Independent review: original stage work conservation

Verdict: **ACCEPT for the stated local control theorem.** No blocking finding
in the frozen source or its paired note. Original whole soundness, Effect
hygiene, principality, and inference termination remain **OPEN**. This receipt
does not certify Rust execution extraction, semantic work completion, or NQ
quiescence.

## Frozen targets and independence

I read all 785 source lines and the complete paired note, then independently
checked the source and every declaration originating in the compiled module.

| Target | SHA-256 |
| --- | --- |
| [OriginalStageWorkConservation.lean](../theory/lean/YulangClosure/OriginalStageWorkConservation.lean) | `819d0e1f4659c9027e80ba03d583f81e59dd9015b8a493e4e599d90eeb759d53` |
| [Paired theory note](../theory/2026-10-27-original-stage-work-conservation.md) | `5f22edfa77b377d971968741809f8894c5f092b04698f5e8ec67fa01efcd4259` |

The target is root-authored. I previously authored the imported
`OriginalDrainFrontier`; this review assesses the new conservation proof and
its application of that frozen import, rather than independently recertifying
my earlier module. The preparation also read `OriginalDrainStages`,
`OriginalFirstDrainBoundary`, `NativeDrainOwnership`, the native
`step_typed_drain`/dispatch/worklist definitions, and NQ sections 4, 5.1, and
5.2. Their eight frozen input hashes are retained in the review scratch
directory.

## Findings supporting acceptance

1. **The final theorem derives its control invariants.**
   `initialized_dispatch_queue_coverage` assumes an actual successful history
   from `initial`, an actual top frame at `.dispatch`, and a supplied finite
   successful suffix ending at that same owner's `EmptyBoundary`.
   `Valid`, the live working frame, the index floor, the entry poll, and
   `NoEarlier` are derived. Neither a conservation law nor a completion
   certificate is an input to this theorem. The selected prefix is nonempty
   and lies after the active Dispatch cut; it is not the empty initialization
   cut produced by `.begin`.

2. **Completion is a new transition in the exact remaining suffix.**
   `Completed work before after` requires the actual top frame's current to
   be `some work`, the changed frame to retain that head's owner, the same
   suspended tail, current to become `none`, and processed to become exactly
   `head.core.processed ++ [work]`. `CompletionIn` follows successful
   `apply` steps in the supplied event list and requires such an edge; old
   processed membership cannot satisfy it. `FutureQueueCoverage` quantifies
   every exact split of the selected prefix and every work value in that
   computed middle state's queue, with the completion in the corresponding
   remaining suffix. The earlier `Processed` result remains a separate,
   weaker historical witness.

3. **The index argument accounts for nested owners.**
   `live_top_above` obtains the floor from `Valid` and the live owner's frame,
   rather than assuming the queue is drained by one fixed stack depth.
   `advanced_flight` and `apply_flight` preserve queued work or current work
   at or above that floor, or produce the new `Completed` edge. At the owner's
   boundary, queue and top current are empty while all older suspended frames
   have lower indices, so `boundary_excludes_flight` applies. An older frame
   may retain current work. A nested frame may supply the completion witness.
   No assertion that every frame is idle, or that every completion belongs
   to the selected owner, is introduced.

4. **The preservation lemmas inspect the executable operations.**
   Structural/current/working/take cases are proved from the computed
   `structural`, `update`, `advanced`, and `apply` definitions. Active work
   cannot be removed by a ReturnReady pop because the derived shape rules
   exclude current work there. Enqueue and queue-head transfer are covered,
   and suspended frames are retained. Fallible operations are used through
   their successful result equalities. Although `NoEarlier` is trivial after
   an error, every consequential use is paired with successful execution;
   that branch cannot justify the final theorem.

5. **Bookkeeping is not a hidden conservation assumption.**
   The proof does not use replaceable `issued` or `returns` records as
   completion evidence. The allowed bookkeeping cannot modify the queue or
   frames. The full immutable admitted `Work` is retained by the invariant
   and appended by `Completed`; it is not reduced to a relation endpoint,
   a value-only predicate, or one of the four structural families.

## Acceptance boundary against the original native owner

| Boundary | What this packet establishes and what remains separate |
| --- | --- |
| Ghost identity and native mutation | `Work` is the model's immutable admitted occurrence. Native Transport mutates the current relation, and Dispatch can clear replay acknowledgement in its local item. The existing separate processing relation accounts for this modeling distinction; extracting that identity from native execution is still required. |
| Processed record | `processed` and the appended whole work are ghost records computed by the model. They do not by themselves establish a successful semantic Call, returned value membership, or a Rust-native processed field. Memoized/consumed control exits are not semantic validity proofs. |
| Nested frames and settlement | Completion may occur in a nested owner. Firstness is for this owner's boundary. The theorem neither excludes every other owner's settlement nor proves that an ordinary native route has no nested generation change. |
| Exact event order | The model uses the supplied event sequence and its actual successful `apply`/`execute` prefixes. Native extraction must still justify that sequence, its field data, and its relation to an ordinary replay continuation. Arbitrary event selection is not an extracted Rust run. |
| Membership and multiplicity | Coverage is membership of `Work` values in a queue snapshot. If identical values occur repeatedly, the statement does not require injectively distinct completion edges for those occurrences. Authenticated occurrence/serial extraction must supply any stronger native accounting claim. |
| Time interval and pending data | Coverage concerns queue snapshots from the active cut through its selected first boundary. It makes no claim about snapshots before that cut. Structural pending data becomes covered when actually enqueued; semantic production/admission of that data remains separate. |
| Existence and termination | A finite successful candidate suffix ending at the owner's boundary is an explicit premise. The result locates the first such cut and proves conservation up to it; it does not establish existence of that suffix, global drain termination, or whole inference accessibility. |

These are limits of the theorem's stated scope, not defects hidden by its
note. No `C.Run` or Rust extraction conclusion is obtained by assuming one,
and no original whole-goal credit is warranted by this packet alone.

## Independent checker and complete declaration audit

The direct source check used the pinned Lean 4.35.0/Lake toolchain with
`timeout 120`, `LEAN_NUM_THREADS=1`, `-j1 -M1024`, and no `-o`; it exited 0
with an empty log. The separate all-origin audit used the same timeout and
thread limit with `-M2048`. It printed complete types and transitive axiom
sets for **111 declarations: 32 definitions and 79 theorem constants**,
including **34 authored and 45 generated theorems**. Every origin block has
its matching end marker, every authored theorem is included, and the audit
reaches its complete total. There are no errors, warnings, elisions,
`sorryAx`, or unapproved transitive axioms.

The 34 authored axiom sets are: 2 empty; 12 `{propext}`; 18
`{propext, Quot.sound}`; and 2
`{propext, Classical.choice, Quot.sound}`. The latter are `select_first`
and `initialized_dispatch_queue_coverage`. The module-wide union is exactly
the same three approved axioms. Generated/private declarations, including
compiler-generated recursion helpers, are included in the audit rather than
excluded by namespace spelling. No authored `sorry`, `admit`, `axiom`,
`unsafe`, `native_decide`, or kernel-checker bypass occurs.

| Independent evidence in `/tmp/yulang-stage-work-conservation-review/` | SHA-256 |
| --- | --- |
| `direct-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `AuditFull.lean` | `5534c767d13ff5d8d3a4b7d5abd9c4a8092a490d7e02f5693dee0bd99b4c8ed6` |
| `audit-01.log` | `3fe2f78d8297bce608527ea136e517f87a1676c538b21199cad63909df89154a` |
| `census.json` | `48f36a691239a61355e74a4961a7f65229ed889ce6f51e5c393016344432860c` |

The paired note's ten hash receipts match their files. Its unavailable
historical check-07 exit metadata is explicitly not treated as a verification
receipt; the retained final check/build/audit and these independent checks
supply the accepted evidence.

Review budget used: one direct check and one all-origin audit; no retry.
Only this review and its leased scratch directory were written. Target
source/note and the eight preparation inputs retain their frozen hashes.
All review checker processes have stopped; review writes stop at handoff.
