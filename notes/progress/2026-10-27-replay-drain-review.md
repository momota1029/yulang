# Independent review: original Replay drain ownership

Verdict: **PASS for the stated local control and ownership bridge.** No
blocking defect was found in the frozen Lean source or its paired note. This
verdict does not establish extraction of an entire native execution into the
control model, termination of a synchronous child drain, the complete
source-specific NQ argument, or original inference accessibility.

## Frozen inputs and review scope

| Reviewed artifact | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalReplayDrain.lean` | `ab8900724f0a5ae41c3c1342e1f8024aff465fbabefcf6e68ecde8d8952ed878` |
| `notes/theory/2026-10-27-original-replay-drain.md` | `b9eed229e29c63ce5fd052bcef967084f3a72d76de3750026a257c5367a73336` |

The reviewer read the complete 1008-line Lean module and 308-line note, all
36 authored theorem statements and proofs, and the relevant original source
owners. The independent audit enumerated every declaration originating in a
fresh elaboration of the exact source, including private and generated
declarations; it did not select only public names or a namespace prefix.
All input hashes were rechecked after the audit and matched.

The native comparison covered `candidate_context.rs` operation retirement,
queue selection and transfer, acknowledgement, all synchronous wait branches,
ordinary consumption, Some cleanup, and outer `candidate_context_drive_replay`;
`candidate_extrusion.rs::candidate_replay_bound`; and `lib.rs` typed-drain
startup, stage transitions, Function construction/dispatch, and `enqueue_item`.
The unchanged `NativeDrainOwnership.Step` constructors were read in full.
The physical-port, interner, and Value-drain dependencies were inspected at
their actual producer and control-refinement interfaces. The original
source obligation is NQ §§5.2–5.3 in
`2026-10-26-native-copy-quiescence-obstruction.md`.

`OriginalReplayBoundary.lean` was read only to identify the application seam.
Independent review of the boundary pair belongs to the separately assigned
reviewer and is not certified by this receipt.

## Ordinary replay: actual finite enqueue history

`ordinaryStep` follows the None-provenance branch: it checks the operation and
Idle state, reads `children[queued]` without advancing that cursor, and places
resource or journal failures before the successful enqueue mutation. The
native enqueue reserves the worklist before transferring the Replay child;
after transfer, its relevant remaining workspace and queue writes do not
introduce a later fallible branch.

`enqueued` retains the selected child's raw relation and task, constructs the
exact ticket, increments `queued`, and appends that work occurrence to the
same shared queue. `ordinary_more_control` proves the existing
`C.Step.enqueueReplay` event. `ordinary_more_decreases` derives decrease of
`children.length - queued` from the actual successful vector lookup.
`ordinaryDrive` therefore has no caller-supplied fuel and does not postulate
a bound on all inference work or allocations.

`ordinary_return_issues_all` first computes the driver from `begin`, constructs
its shared `C.Run`, and excludes a final More result. It proves every actual
child is issued and still queued **under the explicit normal Complete/Queued
return premise**. Failed resource or guard observations remain outcomes. A
Queued result is allowed while the consumed cursor has not advanced; it is
not used as a child-completion certificate.

The production specialization keeps the fixed native task and actual ordered
`RelationId` vector. `replay_relation_processed` concludes the exact raw
relation integer and ticket fields
`(s.nextBirth, s.nextOperation, index, relation)` for each successful vector
lookup. It does not identify task indices with relation IDs or replace a
relation by an independently decoded task pair.

## Same control state and owning-frame history

`Processed` records an occurrence in a live or returned frame's processed
list. It does not assert that semantic subtyping succeeded. The immutable
work occurrence keeps its admitted relation, while Transport may update a
frame's separate processing relation. Relating that ghost issuance identity
to all native mutable frame fields remains part of the whole-state extraction
obligation explicitly retained by the note.

`step_pending_above` covers every constructor of the unchanged shared
`C.Step`. Its alternatives are the same occurrence in the queue, already
processed, or current in a frame at or above the owning position. The
frame-index invariant is preserved over every constructor, including commit.
`BeforeReturn` is a finite history of these actual control events whose source
states still contain the owning stack position.

At the final cut, the supplied empty queue, matching top-frame position, and
`frame.current = none` eliminate the remaining pending cases. An occurrence
cannot be hidden in an older suspended frame because `Indexed` gives its
strictly smaller index. Thus `queued_before_empty_transport` derives
processing from the shared queue/history, without fairness, an empty whole
stack, a diagnosed state, or a completed consumed cursor as premises.

The exact native Transport/current-none cut is still an application obligation
of this theorem. Its name does not itself establish native stage discipline.
The note also explicitly exposes the first-boundary/`BeforeReturn` seam and
assigns its composition to the boundary modules. This review does not promote
the coarse working phase into a native Transport proof.

## Some-provenance branch, return receipt, and errors

The computed `syncAction` matches all native wait selectors:

| Wait state | Guard and selected action checked |
| --- | --- |
| Idle | Equal queued/consumed cursors, empty queue, and the consumed-index child lookup select Start or NoChild. |
| Running | Checked successor bound, operation identity, queued cursor, either permitted consumed cursor, actual frame index, matching destination acknowledgement, and occurrence/cause provenance select Advance. |
| Ready | Checked successor bound, operation identity, equal successor cursors, and the exact returned stack length select Deliver. |
| Missing operation or rejected guard | Explicit failure selection. |

The `maximum` parameter represents the native bounded-integer maximum for
checked addition. It is not inference fuel. The native Idle selector does
not itself test retirement, and neither does `syncAction`; successful Start
additionally requires the live-operation transfer guard. Failures before and
after opening the child frame are represented separately.

`SyncStep` deliberately overapproximates the opaque inner drain. Advance may
carry a shared `C.Step`; silent stage writes may be represented by Tick;
`innerFailure` admits the actual partial error state without requiring a
successful `C.Run`. This is not an exact semantics for every native dispatch
body, and the note says so. `SyncConsume` describes finite executions of the
More loop; it does not prove that a Running child eventually exits.

Both normal-control theorems have the explicit premise that the final
outcome is not any Failed value. Error constructors are eliminated only
under that premise. Earlier More steps cannot hide a failure because the
inductive execution stops on the first non-More result. There is no claimed
conservation theorem across arbitrary `innerFailure` states, and no use of
these normal theorems to prove absence of native errors.

`synchronous_delivery_has_real_return` starts from the same
`C.Run C.initial s` and the computed Ready selection. `ReadyOwned` is derived
by induction over all shared events; `popReplay` supplies the new returned
frame receipt. The result identifies a real member of `s.returns`, with the
selected destination, frame index, transition count, ReturnReady phase,
diagnosed flag, no current work, and no pending acknowledgements. A returned
receipt or completed child is not supplied as an extra premise. The diagnosed
flag is not misreported as absence of a conflict.

`restorationHeld` computes the actual live-parent/back-reference test.
`release` keeps the transaction, held-restoration, retirement, and Idle tests.
These are raw resource/metadata observations, not semantic success evidence;
their whole-native readback relation remains explicit. The proof does not
claim a bisimulation for arbitrary malformed native operation records.

The Some error epilogue preserves the native order: truncate excess frames;
then look up the operation; then, if that lookup succeeds, reset the wait and
restore saved processing globals. A missing lookup returns IdentityExhausted
before the global restoration. Without excess frames the globals are restored
without an Idle rewrite. The queue is retained in every cleanup branch.
`cleanup_restores_processing` has exactly the lookup condition needed for
this early-return distinction. Error cleanup is not classified as a normal
empty drain boundary.

## Physical child relations and all Function ports

The Function specialization preserves the existing four-child builder and
its variance:

| Port | Native pair retained |
| --- | --- |
| argument | upper argument positive to lower argument negative |
| argumentEffect | upper argument Effect positive to lower argument Effect negative |
| resultEffect | lower result Effect positive to upper result Effect negative |
| result | lower result positive to upper result negative |

The native dispatcher traverses this vector in reverse and pushes each child
at the front. The final issuance/queue order in the theorem is the builder
order, not a claim of forward chronological enqueue. Both Effect ports,
length four, exact task lookup, raw relation ID, stored-key readback, and
renamed child pair remain in the result.

`physical_children_before_empty` uses the computed existing physical driver
and its native interner history to obtain the issuance list and control run
on the same `C.State`. Its later continuation starts at that computed emitted
control state. The physical driver's existing local execution fuel remains
an explicit successful-execution witness; it is not silently removed or
converted into a global inference-termination theorem.

## Claim boundary and remaining owners

The paired note accurately retains the following work:

1. Whole native execution extraction into the common control history,
   including successful Context/operand/Value/Effect/extrusion and retained
   rewrite bodies hidden by `C.Step.dispatch`.
2. Native stage discipline supplying the precise Transport/current-none cut,
   together with the separately owned first-boundary application.
3. Replay publication and producer facts about retained fiber quadrants,
   dependency-key deduplication, replay heads, physical fibers, representative
   settlement, and the fresh-endpoint chronology used by the complete NQ
   argument.
4. Complete native metadata/resource/error correspondence for the Some
   projection, and any eventual-termination theorem for its inner drain.
5. Original whole-language soundness, Effect hygiene, principality, and
   inference accessibility. This packet supplies neither a source divergence
   theorem nor exclusion of finite resource errors.

There is no source-language restriction, alternative instance order,
compiler change, or new child-completion assumption introduced by this
packet. The remaining obligations above are not relabelled as proved.

## Independent verification and transitive axioms

The pinned Lean 4.35.0 executable was used from `notes/theory/lean`, without
an output-file option. The source check was:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024 YulangClosure/OriginalReplayDrain.lean
```

It exited 0 with an empty diagnostic log at
`/tmp/yulang-replay-drain-review-20261027-source.log`.

The audit prepends only Lean inspection imports to the exact frozen source
and appends a complete current-origin declaration census, full type printing,
transitive axiom checks, and explicit checks for all 36 authored theorem
roots. Its authoritative final command was:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M2048 --root=/tmp/yulang-replay-drain-review-20261027 /tmp/yulang-replay-drain-review-20261027/Audit.lean
```

This exited 0 in 15.399 seconds. The final log contains zero errors or warnings,
515 distinct originating declarations, 224 theorem constants, and all 36
required authored roots. The complete printed types contain no elision
artifacts. Declaration kinds are 222 definitions, 224 theorems, 39
constructors, 15 inductives, and 15 recursors. There are no new axiom
declarations, `sorryAx`, or transitive dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`.

| Actual transitive axiom set | All 515 declarations | All 224 theorem constants | 36 authored theorems |
| --- | ---: | ---: | ---: |
| none | 368 | 126 | 1 |
| `propext` | 90 | 42 | 14 |
| `propext`, `Quot.sound` | 26 | 25 | 11 |
| `propext`, `Classical.choice`, `Quot.sound` | 31 | 31 | 10 |

The authored groups agree with the paired note. The audit includes the
generated and private declarations omitted from an authored-root-only list.
Complete types and axiom sets are preserved in `complete-census.json` and
`authored-theorem-types.json` in the review scratch directory.

Failed/setup checks were retained and are not counted as passes. An initial
root-discovery expression matched two documentation lines; its assertion
halted audit creation, followed by a missing-file check. That expression was
repaired and verified to identify the 36 actual declarations. The first
complete source-plus-inspection audit at 1 GiB exceeded kernel memory and
then produced cascading elaboration errors. The authorized 2 GiB audit
completed without diagnostics. Its tool completion output was truncated
during context rollover, so one final identical audit recorded an explicit
exit receipt; its parsed census matches the preceding successful-looking log
exactly. No later optional audit was run.

The successful receipt is `audit-receipt-m2048.json`; its log is
`audit-receipt-m2048.log`. Both are under
`/tmp/yulang-replay-drain-review-20261027/`. That directory also retains the
frozen input copies, input hashes, failed logs, and final checks/freeze
receipts. Parent build and audit results were corroborating evidence, not
substitutes for these independent checks.

## Handoff

No reviewed file or dependency was modified. The only repository write by
this review is this receipt. No Git operation, shared cache write, build,
`.olean` output, root-import edit, shared status edit, or child agent was
used. The reviewed source and paired-note hashes above remained unchanged at
final verification. There are no review blockers. All owned writes and
checker processes stop at the accompanying frozen receipt; the next packet
requires a separate exact lease from the parent.
