# Original stage execution: queued work and fresh completion

Date: 2026-10-27. Producer: `/root`.
Status: **kernel-checked conservation for the complete executable stage
projection; native extraction and full NQ remain OPEN**. Independent review
is a separate frozen-packet gate. No runtime or frozen dependency changed.

## 1. Original obligation and the result supplied

[NQ §5.2](2026-10-26-native-copy-quiescence-obstruction.md) argues that at
the first empty Transport boundary after the actual active cut, earlier
enqueued work cannot remain in the queue or an active current slot. The
previous coarse control result required a `NativeDrainOwnership.Run`.
The new [OriginalStageWorkConservation.lean](lean/YulangClosure/OriginalStageWorkConservation.lean)
derives conservation directly from the existing fourteen-stage
`OriginalDrainStages.apply` and `execute` computations. It does not assume
that the complete stage execution projects to such a coarse run.

The final theorem, `initialized_dispatch_queue_coverage`, takes only:

1. `execute history initial = .ok tau`;
2. the actual top-frame list equation at tau;
3. that frame's actual `stage = dispatch`;
4. a supplied candidate `execute events tau = .ok last`;
5. the same owner's `EmptyBoundary` at last.

It constructs a **nonempty first prefix of that very event list**, its
computed endpoint, the exact same-owner Transport/current-none/empty-queue
fields, derived poll entry and computed settlement-entry result. For every
queue observation within that prefix it also derives a **new completion
transition in the remaining suffix**. An old matching processed record is
not sufficient. Neither queue conservation, completed work, Valid, Working,
poll invariance, a coarse run, a source typing derivation nor termination is
a premise of this final theorem.

The candidate finite execution and its ending boundary remain explicit
conditional premises. The theorem creates neither such an execution nor a
boundary, and does not assert that the original NQ execution can reach one.

## 2. Owning native branches and exact projection boundary

The relevant actual Rust owners are `lib.rs::step_typed_drain`, including
Transport, Context, Dispatch, all four structural families, Diagnostics and
terminal acknowledgement/return; the four `candidate_step_*_dispatch`
functions; and `candidate_context.rs::begin_typed_drain`.

The stage model already represents all fourteen stages and four retained
structural buffers. Its shared queue retains all `Work` fields: serial,
task, admitted relation and replay ticket. It does not erase Effect work.
External calls still supply their original successful readbacks. Their
fallible outcomes, semantic correctness, and exact Rust event extraction
remain separate owners.

Two representation details are essential:

- `core.current : Option Work` is the immutable **ghost admitted occurrence**.
  Rust Transport can replace the current item's relation; the projection
  tracks that mutable relation separately in `core.processing`. Conservation
  preserves the whole admitted occurrence, not a false claim that the native
  mutable relation never changes. The native Dispatch copy's cleared replay
  acknowledgement is likewise not an erasure of the tracked admission.
- `core.processed` is **ghost tracking**, not a native Rust frame field.
  Its append is computed by the model's `completed` exactly when Dispatch
  finishes with all four structural buffers empty, or a structural
  continuation finishes. Relating those model readbacks and completion
  events to every native call is still an extraction obligation.

The proof does not use arbitrary `bookkeeping.issued`, operation or return
logs as evidence of processing. `Event.bookkeeping` may replace those fields
but cannot change frames or queue. Actual structural admission is kept
separate from enqueue; pending admitted work is not claimed to be already
in the shared queue.

## 3. Local control facts are derived from every stage

`structural_current` and `update_current` show that a successful update of
an active work occurrence either retains exactly that current work or clears
current and appends exactly `[work]` to the previous processed list.
The proof checks the actual structural completion guard, pending/enqueue
branch and reverse-vector admission branch, and every native stage case.

`returned_is_ready` derives ReturnReady from an actual successful returned
update. Together with the already-derived stage Shape, this excludes popping
a frame that holds current work. `update_take` derives the actual selected
queue head, installed current and nonreturning result whenever an update's
`take` flag is true. A take flag is not accepted as an independent queue law.

`Working owner state` means an actual frame with that birth/index owner and
working phase is present. Before the owner's first empty boundary,
`apply_working` proves that this owner remains present and working. If it is
suspended, the actual update retains the frame unchanged. If it is top,
leaving the working phase would require the excluded empty boundary. This
allows nested frames without silently assuming they cannot occur.

The tracked resource is:

```lean
def InFlight (owner : Owner) (work : Work) (state : State) : Prop :=
  work ∈ state.queue ∨ ∃ frame ∈ state.frames,
    owner.index ≤ frame.core.index ∧ frame.core.current = some work
```

The index floor matters. A boundary for one owner may leave older suspended
outer frames with active work. The proof never concludes that every current
slot in the entire stack is empty. Instead, `live_top_above` derives that a
queue pop enters a frame at or above the still-present working owner. At its
actual top boundary, the derived indexed-stack invariant excludes an active
current at or above that owner. Outer frames below it are irrelevant to this
tracked occurrence.

`advanced_flight` and `apply_flight` prove that each successful transition
either retains this exact InFlight occurrence or computes a new Completed
edge. They cover begin, birth reservation, front/back enqueue, bookkeeping,
all advance branches, settlement call/return and preparation. Errors cannot
serve as successful edges.

## 4. New completion and its exact temporal position

`Completed work before after` requires actual before/after top frames with
the same owner and tail, before-current `some work`, after-current `none`,
and the exact equation:

```lean
changed.core.processed = head.core.processed ++ [work]
```

The new append is required even if an identical Work appeared in an older
record or was enqueued again. `CompletionIn work events state` recursively
follows the actual `apply` results of that exact list and requires such a
Completed edge on it. Its empty-list and error cases are false. Thus a
processed record that predates the supplied suffix cannot by itself satisfy
the proposition.

`NoEarlier owner events state` excludes a same-owner EmptyBoundary at every
before-state of the exact event prefix, while allowing its endpoint to be
the first boundary. `select_first` constructs this list-indexed firstness
from the given finite successful execution and ending boundary. It does
not obtain an unrelated unlabeled execution and reuse its history.

`conserve_completion` iterates the local computed transition result. At the
ending boundary, `boundary_excludes_flight` eliminates its unfinished
alternative using derived Valid and the actual indexed top. Consequently
`first_boundary_completion` supplies a real fresh-completion edge in that
same prefix.

The strongest coverage statement is:

```lean
def FutureQueueCoverage (events : List Event) (state : State) : Prop :=
  ∀ leading suffix middle, events = leading ++ suffix →
    execute leading state = .ok middle →
    ∀ work ∈ middle.queue, CompletionIn work suffix middle
```

`prefix_live` derives live ownership and remaining firstness at each exact
split. `execute_suffix` derives the remaining computed execution. Therefore
`every_queue_has_new_completion` proves FutureQueueCoverage; the caller does
not supply it. This handles work added during the prefix, including actual
structural enqueues, rather than just the queue present at tau.

For consumers that only need historical membership,
`every_queued_processed` also supplies a processed-frame witness in the same
visited-state list. The final theorem includes both forms, with the stronger
fresh-transition suffix statement kept explicit.

## 5. Application at tau and remaining original obligations

The final theorem derives Valid from initialization and Working from the
actual Dispatch top frame. The frozen Frontier theorem derives nonempty
current and entry polling. The selected first prefix must be nonempty,
because tau's current is active. It then applies conservation and derives
the precise first-boundary settlement call from the **same** prefix.

This avoids the initialization trap: fresh `begin` is already
Transport/current-none/empty before seed enqueue. The theorem selects the
first boundary after the supplied active tau, not the first boundary from
empty initialization.

Nested owners remain admissible. A tracked occurrence may complete in such
a frame. The result does not claim that every completion belongs to the
original owner, that another owner never settles, or that generation and
representatives are globally unchanged. NQ's actual ordinary-route
extraction must separately exclude the intervening restoration/settlement
routes excluded by its source argument.

The original event-1229 tau still needs native prefix/readback extraction.
Four-child Function production, complete admission readbacks, source-bound
and fiber preservation, duplicate-memo history, fresh copied ordinal
production and the anchored-successor contradiction remain distinct owners.
This result supplies one control part of NQ §5.2; it is not the full native
NQ proposition or a proof/refutation of original inference accessibility.
Normal finite executions remain distinct from resource errors and runtime
program termination. All original whole-language roots remain OPEN.

## 6. Checker evidence and frozen receipt

Frozen source SHA-256:
`819d0e1f4659c9027e80ba03d583f81e59dd9015b8a493e4e599d90eeb759d53`.
The source has 785 lines and 34 authored theorems. Final focused check 11
exited 0 with no diagnostics under pinned Lean 4.35.0, `timeout 120`,
`-j1 -M1024`, no `-o`. The exact module then built successfully in seven jobs.

The full module-origin type/transitive-axiom audit exited 0 under the same
timeout and `-j1 -M2048`. It checks **111 declarations and 79 theorem
constants**, including 34 authored and 45 generated theorem constants. All
111 begin/end records match; no complete type is elided. No project axiom,
`sorryAx`, checker bypass or unapproved axiom occurs. The authored axiom sets
are: two with none; twelve with `propext`; eighteen with `propext` and
`Quot.sound`; two with all of `propext`, `Classical.choice`, `Quot.sound`.
Every originating definition/private/generated declaration is audited too.

| Evidence | SHA-256 |
| --- | --- |
| `/tmp/yulang-stage-conservation-11.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/yulang-stage-conservation-build.log` | `08d87b5797db373d54f38b0d19b0459b8d7077258f96cff0304472b3d8523b67` |
| `/tmp/yulang-stage-conservation-audit/Audit.lean` | `716b43b275272a96209c8b8c59e4237c88cef484d4dfd2953e66ec7c42a8da8e` |
| `/tmp/yulang-stage-conservation-audit/audit-01.log` | `c5987b52d42da90049d63145b920ea0aca1e685dc8b507f369f1c6ddfea98e11` |

Budget used: eleven of eighteen direct invocations and one of two audits.
All earlier numbered logs are retained. Checks 1, 3–5 and 9–10 record proof
repair failures, including record projections, queue-head substitutions,
the fresh-completion append proof and a reserved local identifier. Check 2
had one subsequently removed linter warning. Checks 6, 8 and 11 exited 0
with no diagnostics. Check 7 has an empty retained log; its exit metadata
was not retained across the tool-output handoff and is not used as a final
verification receipt. The later complete check/build/audit supply that
evidence. No limit, dependency or source semantics was changed to repair a
proof. All checker processes have exited; source and paired note freeze at
review handoff.

| Read-only owner | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalDrainStages.lean` | `9e116f95b8ed001485b2f6b699478c847a53420adb11c70b577b1c0f4e07d61d` |
| `notes/theory/lean/YulangClosure/OriginalFirstDrainBoundary.lean` | `d2c7096ff19b072fea0646b2ed12a4096e26ee03b31eb71997c64e9af43f0a1a` |
| `notes/theory/lean/YulangClosure/OriginalDrainFrontier.lean` | `ec7d4ab463858b73cd09295588833fa095a749c529d40a03cd4f5b8406fb9682` |
| `notes/theory/2026-10-26-native-copy-quiescence-obstruction.md` | `fc2676a6881ac662b2926b2f39223112dbd832e4fb44feca6e212422bbe33d75` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
