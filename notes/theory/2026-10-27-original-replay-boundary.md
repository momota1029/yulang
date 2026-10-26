# The same Replay drain at its first empty boundary

Date: 2026-10-27. Author: `/root`. Branch: `yulang3`.
Original authority: the user's whole original Yulang metatheory request,
the original inference-termination proposition in `Contracts.lean`, and
sections 4–5.2 of
[the native first-empty obstruction](2026-10-26-native-copy-quiescence-obstruction.md).

This packet removes a separate stack-depth premise from the already computed
Replay/physical-port consumers. It derives that premise along the finite
prefix to the **same owner's first empty working boundary**, then proves that
each exact enqueued child has actually been processed there. It does not
establish that such a boundary exists, that the native solver terminates,
or that every processed relation is semantically valid.

## Definitions and unchanged control relation

`OriginalDrainBoundary` imports the existing `NativeDrainOwnership.Step`.
It changes none of that relation's constructors. An `Owner` contains the
frame's `birth` and `index`; `Working` means that a frame with that identity
is present in the stack in the working phase. `EmptyBoundary` additionally
requires that it is the top frame, `current = none`, and the shared queue is
empty. An empty queue during another frame or a current dispatch is insufficient.

`birth` is ghost history identity in this common control model. Rust's
`TypedDrainFrame` carries its actual index, occurrence/cause and saved
processing state, rather than this extra birth field. A future extraction
must assign the ghost identity consistently to an actual frame lifetime.
An index reused after a pop cannot be identified with its earlier owner.

`BeforeBoundary owner start last` is a finite history of actual common
`Step` edges with `¬ EmptyBoundary owner` at every predecessor. It mentions
no processed child, consumed cursor, successful future, fairness, or empty
whole stack. The final boundary remains an explicit premise.

`step_keeps_working` examines every unchanged control constructor. The only
step able to leave this working phase begins at its own empty boundary.
Updates to work, pending acknowledgements and prepared cursors retain the
frame identity; a pop or later diagnostic step cannot pop this working owner.
Nested frames and their completed returns are included. The resulting
`before_boundary_working` preserves the exact owner throughout the prefix.

`losing_working_has_boundary` and `removal_has_boundary` also give a concrete
intermediate empty state in any finite run that loses this working owner.
These are necessary conditions for leaving or removing it, not progress or
termination assertions.

## Application to actual child producers

`OriginalReplayBoundary.first_boundary_before_return` combines preserved
working ownership with the existing `Indexed` invariant. At each real step
it derives `owner.index < frames.length`, which had previously been an
independent `BeforeReturn` premise. At the final boundary the exact stack
position follows from the same identity and index invariant.

`queued_at_first_boundary` then applies the existing queue/current/processed
conservation proof. Its conclusion `Processed` means membership in an actual
frame's `processed` list or in a real returned-frame receipt. It is stronger
than mere issue/enqueue and does not assert semantic subtyping.

The following consumers supply the queue premise from the computed producer:

| Root in `YulangClosure.OriginalReplayBoundary` | Producer and conclusion |
| --- | --- |
| `ordinary_children_at_first_boundary` | Executes the fuel-free `ordinaryDrive`; a normal complete/queued result supplies every exact child and birth/operation/index/relation ticket, which is processed at the specified first boundary. |
| `ordinary_relation_at_first_boundary` | Specializes to the native representation of one task and a raw `RelationId` vector; the selected raw ID and its occurrence ticket remain identical. |
| `physical_children_at_first_boundary` | Uses the computed physical admission/interner/enqueue run; retains the complete native key, source-port list, task matching and `AdmissionResult`, and proves processing of every issued occurrence. |
| `function_four_ports_at_first_boundary` | Retains exactly four ordered ports: argument, argument Effect, result Effect and result; preserves actual task lookup, raw relation readback and renamed pair for every port. |

Frame preservation for the ordinary loop follows from `ordinary_drive_batch`.
For physical admission it follows from the same `NativeValueDrain` invariant
and computed run. Neither is a caller-supplied equality about the final frames.
The physical driver's local fuel is only a witness for a particular successful
finite execution; it does not bound or replace the original inference machine.
The ordinary producer's normal-result premise does not erase the explicit
error cases in `OriginalReplayDrain`.

## Source correspondence and remaining parent obligations

The source owners are `candidate_context.rs` (`consume_replay_child`,
`drive_replay_operation`, frame creation/reclamation) and `lib.rs`
(`step_typed_drain`, Function admission/enqueue and shared typed worklist).
Their source hashes are unchanged from the native obstruction note and the
paired Replay handoff. The existing common control relation retains raw
task/relation/ticket identities and normal control cuts; `dispatch` still
abstracts the semantic body of Context and structured operand processing.

The native NQ cut is specifically `Stage::Transport`, `current = None` and
empty typed worklist **before settlement**. The common `working` phase is
coarser than Rust's Transport/Context/Dispatch/admission/enqueue stages.
This packet does not prove that an arbitrary common working/empty state
corresponds to that precise Rust cut. The extraction of the same native
finite history, its ghost owner and this stage cut remains necessary.
Abort, cancellation, rollback and arbitrary external mutation are not added
to the unchanged successful-control relation.

The next NQ obligations are the actual extrusion work-stack producer,
selected old bounds and relation fibers, retained graph facts before
settlement, and their composition with this processing result. No copied
path or infinite successor-production law is assumed here. Full native trace
extraction and original supported-source initialization remain open.
The original `Acc (fun next prev => p.inferStep prev next) n` goal is unchanged;
neither a no-normal-boundary statement nor finite machine identities close it.

## Verification and exact files

Pinned Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`).
All direct proof checks use `-j1 -M1024`, and parent-owned focused builds
completed successfully. `OriginalDrainBoundary` needed two local repairs:
implicit/frame inference and an unsupported tactic spelling. Its third
direct check passed. `OriginalReplayBoundary` passed its first direct check.
The actual diagnostics remain in `/tmp/yulang-drain-boundary-01.log` through
`-03.log` and `/tmp/yulang-replay-boundary-01.log`; no failed check is reported
as successful. Focused build logs are `/tmp/yulang-drain-boundary-build.log`
and `/tmp/yulang-replay-boundary-build.log`.

The reusable `AuditOriginalExecutionProgress.lean` prints all originating
theorem types and transitive axioms, including private/generated constants.
Its first complete run passed at a local 2 GiB audit limit, without changing
project or kernel-checking settings. The four-module census has 378 theorem
constants, with 25 from this pair:

| Module | All declarations | All theorem constants |
| --- | ---: | ---: |
| `OriginalDrainBoundary` | 51 | 17 (9 authored, 8 generated) |
| `OriginalReplayBoundary` | 8 | 8 |

The complete log `/tmp/yulang-original-execution-audit-01.log` has 378 matched
begin/end records, no printer ellipses or diagnostics, and only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. Its SHA-256 is
`87c09c3694569c4e57053f04951cd1916d887bfad223323a739a3f9723763821`.
No `sorry`, `admit`, project axiom or native/kernel bypass is added.

| Frozen source | SHA-256 |
| --- | --- |
| `OriginalDrainBoundary.lean` | `d11f5c4e5550702c0796c45076408b0c038e4bc204ec05354b83db8ad7b04ab9` |
| `OriginalReplayBoundary.lean` | `894f0008c7cf62a43a80c82eb75c5ae08c2a0aa84c0fbadae4dcec07529544c8` |

Independent acceptance belongs to the nonauthor review in
`notes/progress/2026-10-27-replay-boundary-review.md`. Whole-language
soundness, Effect hygiene, principality and inference termination remain OPEN.
