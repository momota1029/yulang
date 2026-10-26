# Original drain stages: current ownership and the pre-settlement boundary

Status: kernel-checked executable field-update projection and invariant;
independent review and whole native trace extraction remain separate. Original
soundness, Effect hygiene, principality, and inference accessibility remain
open. This packet does not establish termination of a nested drain or the
complete source-specific NQ argument.

The module is `notes/theory/lean/YulangClosure/OriginalDrainStages.lean`,
namespace `YulangClosure.OriginalDrainStages`. It closes the specific
stage/current invariant missing from the coarse working-phase boundary:
after initialization and the computed successful updates, a projected working
frame whose current item is absent must be at native **Transport**. The
same module identifies the boundary before the settlement call and preserves
the exact suspended caller frame through finite nested execution.

## 1. Original obligation and fixed inputs

The source obligation is NQ §§5.2–5.3 in
[`2026-10-26-native-copy-quiescence-obstruction.md`](2026-10-26-native-copy-quiescence-obstruction.md).
The frozen `OriginalDrainBoundary.EmptyBoundary` identifies the same birth/index
owner at the top of the shared stack, with working phase, no current item, and
an empty queue. Working phase collapses Transport, Context, Dispatch, and
eight structural stages. Consequently that predicate alone did not identify
the actual native Transport branch or the order relative to settlement.

The original parent is still `SourceProblem.InferenceTermination` in
`Contracts.lean`, with the original whole-source domain and accessibility
quantification. A finite readback execution, absence of an empty normal cut,
or preservation of a suspended frame is not that accessibility theorem.
No source language, native algorithm, test expectation, or compiler behavior
was changed.

The parent reported HEAD `f8442e8` while this packet was active. The Rust and
frozen proof inputs were hashed directly; no Git operation was used by this
leaf. The governing inference top-level principles and corrected birth-level
SCC scope remain unchanged. The only repository writes are this note and the
new leased Lean module.

## 2. Actual source owners and all fourteen stages

The native declaration is
`candidate_context.rs::TypedDrainStage` at line 59. The frame initializer at
`begin_typed_drain`, around 2249, creates `current = None` and Transport, empty
structural continuations, and zero acknowledgement cursors. The relevant
normal driver is `lib.rs::step_typed_drain`, around 14289.

`constrain_live_item_with_inferred_entry`, around 13985, immediately routes an
enabled candidate graph to `run_candidate_typed_drain`. The later legacy
synchronous loop's conditional candidate-frame writes are not another active
candidate driver on that route. The proof does not use those legacy writes
to replace the current candidate stage machine.

| Exact native stage | Computed update and current ownership |
| --- | --- |
| Transport | With a current item, transport changes its mutable relation and enters Context. Without one, the actual worklist pop installs the selected occurrence; no item plus dirty stays Transport; no item plus clean enters Diagnostics. |
| Context | A successful Context call records `context_consumed` and enters Dispatch, preserving the current item. |
| Dispatch | The actual return either installs one structural continuation or installs none. The caller tests all four continuation fields before clearing current and returning to Transport. |
| FunctionAdmission | The selected Function continuation admits a child, retains pending work, and enters FunctionEnqueue; exhausted children clear the continuation/current and return to Transport. |
| FunctionEnqueue | Pending work is enqueued at the front, pending is cleared, the cursor advances, and the stage becomes FunctionAdmission. |
| TupleAdmission | The analogous Tuple admission update, or completion to Transport. |
| TupleEnqueue | The analogous Tuple pending enqueue/cursor update. |
| RecordAdmission | The analogous Record admission update, or completion to Transport. |
| RecordEnqueue | The analogous Record pending enqueue/cursor update. |
| VariantAdmission | The analogous Variant admission update, or completion to Transport. |
| VariantEnqueue | The analogous Variant pending enqueue/cursor update. |
| Diagnostics | Successful diagnostic calls mark the projected diagnosed flag and enter Acknowledgements, preserving absent current. |
| Acknowledgements | Completing the next pending acknowledgement updates the split done/pending view; the stage becomes ReturnReady when none remain. |
| ReturnReady | The normal terminal cut removes the actual top frame and records its returned projection. |

The structural functions at `lib.rs` 14955–15055 test exhaustion before the
pending field. The projection does the same; it does not silently reorder
these tests or assume well-formed cursors in a constructor. It selects children
in reverse vector order and places pending work at the front. Function,
Tuple, Record, and Variant each retain their own fields. The active
`dispatch_live_item` installs those fields at approximately 14578, 14640,
14691, and 14849 respectively. A plain return is not treated as an extra
certificate that all four fields were empty: `finishDispatch` computes that
test from the actual retained fields.

The semantic contents of the child vectors and successful port-admission
readbacks remain explicit inputs. This packet neither drops the Effect ports
nor replaces the four-port Function proof: their exact tasks, variance,
RelationIds, and physical interning are owned by the existing Value/Replay
pipeline. Here every structural field and stage is represented, while the
stage invariant holds for every readback vector, including ones unreachable
from a semantic producer.

## 3. Computed projection and derived invariant

`Frame` contains the existing `NativeDrainOwnership.Frame` plus the exact
stage, optional Context result, four structural continuations, and a small
program counter around the settlement call. Each continuation retains its
task vector, next index, and optional pending work. `Stage.phase` computes
the existing coarse phase; `Frame.project` uses that value. No hypothesis
asserts that a supplied coarse phase already corresponds to Transport.

The current work occurrence uses the frozen ownership model's immutable
admitted identity. Transport's mutable relation is carried separately in
`core.processing`. This is the same distinction used by Replay drain
ownership; extracting that ghost occurrence from all mutable native work
items remains part of the whole-state correspondence. A selected Replay
work item also appends its actual ticket to the frame's pending list and
advances the prepared cursor, matching the existing shared take projection.
Completing current dispatch moves that occurrence to the processed list and
clears the current/processing fields.

`Frame.Shape` states the field relationship:

- Transport permits either an absent or present current item.
- Context, Dispatch, and all eight structural stages have a current item.
- Diagnostics, Acknowledgements, and ReturnReady have no current item.

This predicate is a proved invariant, not a requirement of `Event` or a
certificate accepted by an update. `fresh_shape` proves initialization.
`structural_shape` and `update_shape` analyze the actual computed branches.
`update_owner` separately proves that these writes retain the frame's birth
and index.

`State` contains the shared queue and enriched frame stack, the fresh ghost
birth counter, the dirty observation, and the remaining raw control
bookkeeping. `State.project` computes one existing `C.State` from those fields.
It does not existentially choose another state or history. Bookkeeping
readbacks cannot modify the stack, queue, stage, current, or birth counter.
They may overapproximate unrelated operation/receipt data; no theorem here
claims that arbitrary such readbacks form a `C.Run`.

`apply` executes initialization, enqueue, top-frame advancement, settlement
entry/return, preparation, and other birth reservation. A top-frame update
checks both the saved birth/index owner and the actual native-vector slot.
`execute` folds a finite event list and returns an explicit error at a rejected
cut. `Valid` combines the current shape, concrete stack indices, and bounds
on active births. `apply_valid` and `execute_valid` prove it for all computed
successful events; `initialized_valid` supplies it from the empty initial
state. The main result therefore has no supplied `Valid`, stage invariant,
child-completion fact, or complete native-run premise.

The readbacks are ordinary data: transported relation, Context's Boolean,
dispatch result/vector, transition count, and admitted work. Their semantic
correctness is not inferred merely because these field updates preserve
`Shape`. Native resource, journal, semantic, provenance, and bounded-integer
checks still need their owning implementations. Successful field-update
cuts are projected here; the entire native function is not reimplemented.

## 4. Application to the frozen EmptyBoundary

The principal theorem has the following unchanged consumer:

```lean
initialized_boundary_is_transport
  (executed : execute events initial = .ok state)
  (boundary : OriginalDrainBoundary.EmptyBoundary owner state.project) :
  ∃ frame rest, state.frames = frame :: rest ∧ frame.owner = owner ∧
    frame.core.index = rest.length ∧ frame.core.birth = owner.birth ∧
    frame.stage = .transport ∧ frame.core.current = none ∧ state.queue = []
```

The frozen predicate's working/current-none fields do not themselves imply
Transport: ten other native stages also project to working. The conclusion
uses the invariant derived from initialization and the computed writes to
exclude each of them. The witness is the actual top frame in this projected
state, with its original identity and concrete native index.

`projected_empty_boundary_iff` gives both directions for a valid state. Thus
the new projection applies directly to `OriginalDrainBoundary.EmptyBoundary`
and does not introduce a replacement boundary proposition with a stronger
stage assumption. `OriginalDrainBoundary` and `OriginalReplayBoundary` remain
frozen; their existing common-control history is not silently replaced by
this event list. The remaining extraction must identify their state cut with
this computed projection of the same native prefix.

## 5. Settlement happens after this cut

In `step_typed_drain`'s Transport/current-none arm, the empty-worklist test is
performed before `settle_candidate_intrusion`. Settlement may enqueue work
or leave the intrusion state dirty. The later pop/dirty observation decides
whether to enter Diagnostics.

`Poll.entry`, `Poll.settling`, and `Poll.returned` record these program-counter
positions inside that one Transport arm. They are not additional native
`TypedDrainStage` constructors. `apply (.settle owner)` computes the actual
entry test and preserves the frame while marking the active call. A nested
drain may run above it. `apply (.settled owner dirty)` accepts the returning
dirty observation for that same saved owner; it retains the queue produced
by the call. At the initial empty entry, `advance` cannot skip the settlement
call and perform the pop directly.

`settlement_starts_at_boundary` proves:

```lean
apply (.settle owner) state = .ok after →
  OriginalDrainBoundary.EmptyBoundary owner state.project
```

The boundary is the **before-call** state. It is independent of whether
settlement returns cleanly, produces work, remains dirty, or later fails.
`boundary_enters_settlement` computes the successful entry from the derived
boundary at `Poll.entry`. `dirty_empty_stays_transport` and
`clean_empty_enters_diagnostics` separately prove both actual outcomes of
the later empty pop. There is no empty-equals-Diagnostics identification.

This establishes the ordering of the projected native field cuts. It does
not prove that the settlement body terminates or that every coarse `C.Step`
history has a matching native stage history.

## 6. Nested calls preserve the saved frame itself

`begin_typed_drain` appends a new native frame at the previous length. The
shared list is newest first, so the model pushes a fresh birth/index frame
and retains the entire previous list. Normal terminal removal at
`candidate_step_typed_drain_terminal`, around 14880–14945, removes only that
actual top frame. Snapshot preparation around
`candidate_context.rs::prepare_typed_drain_update` preserves all current and
stage fields while retaining the undo allocation; acknowledgement preparation
does not alter the caller's current item or stage.

`apply_keeps_suspended` proves that every normal event preserves an exact
frame occurring below the top. It retains all of the saved frame, including
current, stage, structural buffers, and settlement program counter.
`resume` executes a supplied finite nested-event trace until the original
saved owner is again on top. A shorter exhausted trace is rejected; there is
no assertion that a child eventually returns.

The application theorem is:

```lean
initialized_resume_same_frame
  (initialized : execute history initial = .ok start)
  (held : saved ∈ start.frames)
  (returned : resume saved.owner events start = .ok last) :
  ∃ rest, last.frames = saved :: rest
```

The saved owner includes birth and index. `same_top_is_saved_frame` uses the
derived stack-index invariant to exclude another matching frame; no later
frame is selected merely because its final position matches. The conclusion
is equality with the entire pre-call `saved` frame. `resumed_transport_boundary`
then applies the frozen boundary predicate to that exact caller when its
preserved Transport/current-none fields and the returned empty queue hold.

## 7. Failure and extraction boundaries

Errors and panics are not normal `Event` constructors. The executable driver
returns explicit rejected-observation/current/context/frame failures, and
malformed structural unwrap/index and initial-worklist assertion cuts have
separate panic tags. `suspendedCall` also signals an incomplete or improperly
ordered event observation; it is not asserted to be a native error enum value.
Opaque native availability or semantic failures carry a separate
`FailureCut` with their partial state. No invariant or normal-control theorem
is imposed on arbitrary failure states.

`truncateFailure` projects native `Vec::truncate(savedCount)` onto the reversed
frame list and preserves the queue. Surviving frames are proved to be the
same original frames. Its conditional shape theorem requires validity of the
particular pre-truncation state and makes no claim that every native error
state is valid. This is separate from successful event execution. The
post-truncate Replay lookup and saved processing-global restoration remain
the existing `OriginalReplayDrain` owner. Transaction rollback, undo-frame
restoration, resource errors, and panics are not silently classified as normal
return or empty quiescence.

The first remaining native extraction obligation is concrete: for each
relevant successful Rust prefix, supply its actual stage-call readbacks and
queue/stack events, assign the shared monotone ghost lifetime to each new
drain, and prove that `State.project` equals the same control cut used by the
frozen boundary/Replay history. The returned semantic calls must preserve
their saved caller, with their finite internal events represented on the
same stack. Semantic dispatch, Context, extrusion, settlement, diagnostics,
port readbacks, cursor/resource guards, raw metadata, and native bounded
arithmetic remain their owners. Natural-number control data do not prove
absence of native integer overflow; an overflowing native call is a failure
cut, not a successful projected update.

The arbitrary readback surface is a deliberate overapproximation for the
stage invariant. It is not a definition of original Yulang inference or a
proof that every such readback is realizable. No assertion is made that the
event evaluator alone refines every field of `NativeDrainOwnership.Run`.
Exact producer/fiber/representative facts and the remaining full NQ argument
also remain separate. This packet closes the stage/current and saved-frame
invariants; it does not relabel those remaining bridges as established.

## 8. Actual checking and complete axiom audit

The installed toolchain was read during this packet: Lake
`5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. The project pin and empty
dependency manifest were unchanged. The parent remained the only shared
build/cache owner.

The final direct source check, from `notes/theory/lean`, was:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024 YulangClosure/OriginalDrainStages.lean
```

It exited 0 in 5.012 seconds with no diagnostics. This was proof invocation
6 of the assigned 16; every invocation had a 120-second timeout. Earlier
failed checks are retained, including initial namespace/record syntax,
dependent case-name substitutions, state-parameter transport, and reserved
local identifiers. They are not counted as proof passes.

One authorized inspection audit used the exact frozen source with Lean
inspection imports, full current-origin declaration enumeration, complete
type printing, transitive axiom guards, and explicit `#check`/`#print axioms`
for all 28 authored theorems:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M2048 --root=/tmp/yulang-drain-stages-20261027 /tmp/yulang-drain-stages-20261027/Audit.lean
```

Audit 1 of 2 exited 0 in 6.242 seconds, with zero diagnostics. The census
contains 706 distinct originating declarations: 340 definitions, 292 theorem
constants, 46 constructors, 14 inductives, and 14 recursors. All 28 authored
roots were present. Private/generated declarations were included. Printed
types contained no elision artifacts. There were no new axiom declarations,
`sorryAx`, checker bypasses, or dependencies outside the standard three
axioms below.

| Actual transitive axiom set | All declarations | Theorem constants | Authored theorems |
| --- | ---: | ---: | ---: |
| none | 587 | 210 | 1 |
| `propext` | 97 | 60 | 11 |
| `propext`, `Quot.sound` | 18 | 18 | 12 |
| `propext`, `Classical.choice`, `Quot.sound` | 4 | 4 | 4 |

Complete authored groups, all under `YulangClosure.OriginalDrainStages`:

- No axioms: `truncate_keeps_queue`.
- `propext`: `fresh_shape`, `terminal_current_empty`, `finish_dispatch_shape`,
  `structural_shape`, `structural_owner`, `dirty_empty_stays_transport`,
  `clean_empty_enters_diagnostics`, `indexed_member`, `apply_keeps_suspended`,
  `truncate_survivor_is_original`, `truncate_survivor_shape`.
- `propext`, `Quot.sound`: `working_empty_is_transport`, `update_shape`,
  `update_owner`, `initial_valid`, `advance_valid`, `apply_valid`,
  `execute_valid`, `initialized_valid`, `projected_empty_boundary_iff`,
  `initialized_boundary_is_transport`, `settlement_starts_at_boundary`,
  `boundary_enters_settlement`.
- `propext`, `Classical.choice`, `Quot.sound`: `same_top_is_saved_frame`,
  `resume_same_frame`, `initialized_resume_same_frame`,
  `resumed_transport_boundary`.

No `.olean` output, root import edit, compiler change, Git mutation, child
agent, or shared status/cache write was performed by this leaf. The pinned
binary used the already authorized escalated execution path required by this
environment.

## 9. Frozen source and handoff

| Source/input | SHA256 |
| --- | --- |
| `OriginalDrainStages.lean` | `9e116f95b8ed001485b2f6b699478c847a53420adb11c70b577b1c0f4e07d61d` |
| `OriginalDrainBoundary.lean` | `d11f5c4e5550702c0796c45076408b0c038e4bc204ec05354b83db8ad7b04ab9` |
| `NativeDrainOwnership.lean` | `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| NQ source note | `fc2676a6881ac662b2926b2f39223112dbd832e4fb44feca6e212422bbe33d75` |
| `Audit.lean` | `5aae989b067deba9e4d1431d3e292218812cb9c25cd9eff47156b85e044acdca` |

Owned scratch is `/tmp/yulang-drain-stages-20261027/`: exact source snapshots
and logs for proof checks 1–6, the successful full-origin audit and receipt,
complete declaration census, all authored theorem types and axiom groups,
input manifest, and final checks/freeze receipts. Independent review,
integration, record synchronization, commit, and push remain with the parent.
The final handoff supplies this note's hash and a writes-stopped receipt.
