# Shared native owner journals and cancellation history

Date: 2026-10-26. Claim class: constructive, kernel-checked mutable-owner
projection. Independent review is recorded separately before integration.
Full native execution authentication and original inference soundness remain OPEN.

Baseline: `60e8684224a8a911a5627b845312750a192be777` on `yulang3`.
Author: `/root`; no contributing child. Module:
`YulangClosure.NativeExecutionHistory`, importing only the pinned `Std`.

## Original obligation and reduction

`SourceProblem.InferenceSoundness` in `Contracts.lean:128–130` requires the
original source judgment and one same-scoped witness for every successful
generated solution. `NativeCorrespondence` at lines 147–149 separately requires
actual native success to yield the generating constraints and a realized
solution. Neither follows merely from defining those propositions.

The accepted merge construction supplies local Effect transport and historical
Replay origins. Its application still needs one actual committed native history.
Earlier acknowledgement work proves a single operation's cursor accounting and
local journal restoration. It does not establish that independently selected
operation/restoration snapshots belong to the same execution.

This construction supplies a **shared owner table and chronological route
interpreter**, including repeated updates to multiple old owners, new owner
allocation, advance preparation, commit/cancellation and reused numeric IDs.
It proves simultaneous checkpoint restoration from the computed history. It
does not supply the complete Rust operational semantics, the frame/worklist
projection, a current recursive obligation graph, or accepted-drain semantics.

## Native bodies and exact projection

Source references below are under `crates/yu-solver/src`, at the pinned baseline.

| Native owner | Projection and required application boundary |
| --- | --- |
| `candidate_context.rs:126–150,166–170` | Replay mutable tuple `(waiting_child, queued, consumed, retired)` and restoration mutable tuple `(next_opposite, replay, retired)` are opaque payloads in separate address lanes. Immutable task/children/input metadata is outside this tuple projection. |
| `candidate_context.rs:2313–2324,4063–4069` | Both constructors use and advance the same `next_replay_operation`; `allocate` advances one shared numeric frontier and inserts the chosen lane. Native successful reservation/checked arithmetic remains a source premise for the mathematical `Nat` representation. |
| `candidate_context.rs:2336–2343,2376–2391,2405–2426` | Preparation reads the actual current owner tuple and appends it to undo storage. Atomic prepare/update is available, but is not required. |
| `lib.rs:14260–14285,14881–14933` | Several acknowledgements can be prepared before later consumption. Separate `prepare` and `mutate` events retain that order; multiple mutations can be protected by the already recorded tuple. |
| `candidate_context.rs:2044–2074,2095–2115` | Checkpoint retains the shared numeric frontier and undo lengths. Reverse restoration/replay undo precedes deletion of newly allocated IDs and rewinding the frontier. |
| `candidate_context.rs:2209–2247` | Commit discards the route's undo suffix. Native frame preparation reset and replay/restoration reclamation are additional effects, explicitly outside `commit` here. |
| `lib.rs:9498–9543` | Successful and failed routes select commit or cancellation. The interpreter's Boolean selects that storage branch only; it is not evidence of successful inference or sound typing. |

An address has an owner lane and numeric operation index. A `Cell` contains an
opaque mutable payload and a **ghost birth number**. The birth clock is proof
history metadata, not a new runtime field or implementation proposal. Native
numeric allocation rewinds on rollback; the ghost clock keeps increasing.

`State.undo` represents only entries after the chosen native checkpoint. Older
undo vector prefixes remain outside the projection. The native source keeps
retired owners until route commit, so projected transactional mutation does not
delete an old owner. Typed-drain stack pop/reinsertion has a different undo
algorithm and is not encoded as a mutable-owner table write here.

## Executable history and derived invariants

`step` computes each event's actual readback. Allocation rejects an occupied
new address. Update and preparation reject a missing owner. Preparation records
the tuple read from the table; callers cannot supply a favorable old snapshot.
A separated mutation requires a preparation for that address in this route's
current undo list and preserves the birth number. `checked_step` and
`checked_run` derive the corresponding relational histories from successful
computations.

The protection guard is deliberately about journal ownership, not semantic
permission to change a native cursor. Actual queued/consumed/Running/Ready guards
are still supplied by their native owners and the existing acknowledgement
proofs. An arbitrary payload update allowed by this projection does not prove
that the native machine can perform that update.

`WellFormed` states that occupied indices precede the allocation frontier and
that every live birth precedes the ghost clock. Both are proved from the empty
table through a checked list of routes. They are not supplied as independent
certificates at each route boundary. `executeHistory` computes one sequence of
commit/cancellation outcomes; `checked_history` proves its endpoint belongs to
the single derived history and satisfies these invariants.

`unwind_covered` proves that once an owner has a retained undo snapshot, its
final unwind result at that owner is independent of subsequent protected
payload mutations. This handles duplicate preparation snapshots taken before
several acknowledgements, rather than incorrectly requiring a new snapshot
immediately before every mutation.

`cancel_table_exact` restores **all** old owners simultaneously and removes
every newly allocated address. Its premise is one actual projected `Exec`
from the checkpoint, plus checkpoint well-formedness. The computed-history
application `history_cancel_joint` derives that premise from earlier routes
and successful `run`; no per-owner terminal model is assumed.

Native rollback uses two undo vectors rather than one global vector.
`partitioned_unwind` proves that partitioning the same chronological reverse
list by owner lane and draining the two subsequences separately produces the
identical table. Order within each owner subsequence is retained; updates to
disjoint lane addresses commute. `partitioned_cancel_exact` applies this
identity to checkpoint restoration. The source application must still show that
the actual native vectors are those projections of the same event sequence.

`cancelled_allocation_not_reused` proves that the same numeric slot after a
cancelled allocation receives a strictly later birth, including arbitrary
subsequent events in the cancelled attempt. Existing live births also precede
the retry clock. A cancelled event cannot authenticate the retry merely because
the numeric `ReplayOperationId` matches.

## Checked witnesses and cost

The first computed witness commits two owners in separate lanes, interleaves
two mutations to one old owner with a mutation to the other and a new owner,
cancels that attempt, then allocates the same numeric slot again. Both old
payloads are restored; the cancelled birth 2 is replaced by birth 3, and the
clock reaches 4. The second witness prepares the same old tuple twice before
two separate mutations and proves exact restoration. Commit clears protection,
so a subsequent route requires preparation again.

These are transparent proof-side functional tables. Lookup through accumulated
`put` closures is linear in the number of writes, and preparation membership
uses a linear undo-list scan. The construction is not a proposed production
data structure or a new solver pass. Native algorithmic costs are unchanged.

## Verification and preserved failures

The fixed task-local toolchain reports Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake `5.0.0-src+eb6cafb`.
The exact project pin/configuration is unchanged. Isolated project/cache and
all evidence are under `/workspace/scratch/f98087c7ac1a/native-history-r3`.
Every checker/audit call is bounded by 120 seconds, one thread and `-M1024`.

Nine bounded calls were used. Checks 02, 04 and 07 pass the focused build and
three named root audits; the final module has no warnings. Checks 01, 03,
05 and 06 preserve the actual source and diagnostics: structure-update layout,
indexed-case binders, Boolean normalization, a reserved identifier and an
unfolding step. These are elaboration repairs, with no weakened theorem goal.
Call 08 failed in the audit script's untyped declaration counter, before a
complete census. The script was corrected with an explicit `Nat` annotation;
call 09 passed in 1.118013 seconds. None of those failures is reported as a pass.

The complete originating-module census covers **311 declarations, 123 distinct
theorem constants and all 48 authored roots**, including private/generated
proofs. Complete types and transitive axiom lists are preserved. Distribution:
69 without axioms; 20 with `propext`; 34 with `propext, Quot.sound`. No choice,
project axiom, proof hole or native-evaluation bypass. The audit enumerates by
originating module and rejects unapproved axioms; it is not a namespace-only
sample. No Cargo/native tests or production changes were made.

| Frozen evidence | SHA-256 |
| --- | --- |
| `NativeExecutionHistory.lean` | `44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6` |
| Complete audit `check09-full-audit.log` | `13a11e35ad4e204519c5310c841641ac4bd347d4d632c866ab4fec8668690928` |
| Eleven-source review manifest `review-inputs.json` | `b3f858b08d19080261fdf2e163435cb03e43507ac3b35800db30bbee49fdcc0c` |
| Native `candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| Native `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

## Application and first remaining premise

The construction removes the need to **assume independent rollback correctness
for each chosen owner snapshot** in this projection: one checked event history
and its actual snapshot reads yield joint restoration and retry separation.
Any joint invariant of the checkpoint table is therefore preserved by a
cancelled projected route, not only separate scalar cursor bounds.

The next native-history premise is authenticating the complete chronological
projection: all relevant native preparations/mutations and creations, the
checkpoint-to-vector correspondence, immutable operation metadata, frame and
worklist ownership, commit-time reclamation/reset, nontransactional paths and
actual accepted drain. The new graph/current-disposition lane is independent of
this authentication; neither result may silently supply the other's premise.
Original contextual/source witnesses, complete Call and record-boundary meaning
remain separate OPEN obligations. No implementation defect, impossibility
theorem, source-domain restriction or production promotion is asserted.
