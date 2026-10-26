# Original Replay: actual enqueue and first-empty drain ownership

Status: kernel-checked research control bridge; independent review and whole
native/source integration remain separate. This note does not close original
inference termination or the complete source-specific NQ argument.

The new module is
`notes/theory/lean/YulangClosure/OriginalReplayDrain.lean`, namespace
`YulangClosure.OriginalReplayDrain`. Its principal result is that the ordinary
Replay loop computes an enqueue for every child before returning normally,
and that those exact work occurrences have been processed at the same drain's
subsequent empty Transport boundary. Completion is derived from actual
worklist/frame transitions; it is not supplied in a child-completion field.

## 1. Original obligation and source scope

The immediate source claim is §§5.2–5.3 of
`2026-10-26-native-copy-quiescence-obstruction.md`: an ordinary bound Replay
returns only after all of its children have entered the shared worklist, and
an earlier ordinary child cannot remain unprocessed at the proposed first
empty Transport boundary of that same active drain. The fresh-endpoint
chronology that excludes a suspended older restoration product is a separate
input, formalized in `OriginalInferenceTerminationResolution.lean`.

The original parent remains `SourceProblem.InferenceTermination` in
`Contracts.lean`: accessibility of inference transitions for every supported
source and initial inference state, including untypable programs. Neither
execution termination of recursive Yulang programs nor the absence of a
normal empty drain boundary is that accessibility theorem. No source domain,
compiler behavior, test expectation, finite universe, or global progress
assumption was changed here.

The supplied repository baseline was
`6148fc868565617d7db6ef193a6ff164700d88f7`, branch `yulang3`. The construction
followed the inference top-level principles, the birth-level SCC correction,
and the existing source-qualified NQ note rather than reinstating an older
cross-level intrusion rule.

## 2. Exact operational correspondence

The new module imports the existing physical Value relation execution pipeline.
It reuses the *same* `NativeDrainOwnership.State`, `Work`, `Ticket`, `Frame`,
`Operation`, `Step`, and `Run`. Work keeps its admitted relation ID even when
Transport changes a frame's separate mutable processing relation.

| Native owner | New definitions and result |
| --- | --- |
| `candidate_context.rs::replay_operation_queue_next`, around 2363 | `ordinaryStep` reads `children[queued]`; reading does not advance the cursor. |
| `candidate_context.rs::transfer_replay_child`, around 2385; `lib.rs::enqueue_item`, around 15223 | `enqueued` performs the exact ticket transfer, `queued + 1`, append-back, and immutable issuance. Queue/undo failures precede these changes. `ordinary_more_control` constructs the corresponding existing `Step.enqueueReplay`. |
| `candidate_context.rs::candidate_context_consume_replay_child(None)`, around 4163 | Missing operation, non-Idle wait, unavailable resources, all-queued-but-unconsumed, and empty-child acknowledgement are represented by `ordinaryStep` and `noChild`. |
| `candidate_context.rs::candidate_context_drive_replay`, around 4208 | `ordinaryDrive` is a total executable recursive function. Its measure is this operation's actual `children.length - queued`; no caller fuel or bound on all inference allocations is used. `driveReturn` also retains the distinct Some/None return tests. |
| `candidate_extrusion.rs::candidate_replay_bound`, around 1070–1110 | `replayChildren task relations` uses one fixed native task and the actual ordered RelationId vector; `replay_relation_processed` preserves every selected raw integer and exact Replay ticket. |
| `candidate_context.rs::candidate_context_step_replay_child(Some)`, around 4097 | `syncAction`, `started`, `delivered`, `SyncStep`, and `SyncConsume` represent Idle, Running, Ready, NoChild, normal finite iterations, and error exits. Running advances a shared drain control event, not an assumed returned child. |
| `candidate_context.rs::retire_replay_candidate`, around 2195 | `restorationHeld` computes the live parent and matching back-reference test. `restoration_held_exact` proves its exact meaning. `release` retains the transactional, retired, Idle, and held-restoration tests. |
| `candidate_context.rs::candidate_context_consume_replay_child(Some)` error epilogue, around 4163–4189 | `cleanup` performs conditional stack truncation, conditional Idle restoration, and saved processing restoration, including the intervening failed operation lookup. |
| `lib.rs::step_typed_drain`, around 14286; existing `NativeDrainOwnership.Step` | `step_pending_above` covers every existing constructor. It derives the queue/current/processed conservation needed before the owning drain returns. |
| `lib.rs::candidate_step_function_dispatch`, around 14955; `NativeValueRelationExecution.drive` | `physical_children_before_empty` joins computed physical allocation, admission, exact task naming, actual enqueue, and later processing on the same control history. `function_four_ports_before_empty` specializes the existing four-child function builder, retaining both Effect ports. |

`NativeReplayCurrent` was inspected as well. Its `unfinished` frontier includes
retained and active graph vertices and explicitly is not the native worklist.
Consequently its frontier result was not substituted for drain emptiness.

### Ordinary loop and error behavior

`Resources` records queue reservation and undo outcomes, transactional state,
and the raw restoration-held test. The last field is a raw owner lookup,
whose implementation is `restorationHeld`; it is not a completion certificate.
Capacity and journal-storage effects erased by the existing control model
are not asserted to be impossible.

For a newly published operation, `begin_at` establishes the zero-queued
invariant. Each successful iteration adds one exact child to both `issued`
and the same `queue`; the remaining-child measure decreases. An availability
failure returns `failed`. A normal return establishes that every index in the
actual child vector has a work occurrence still in that queue. A nonempty
ordinary operation can return `queued` while `consumed` remains zero. The
proof never identifies that result with completed children.

Operation publication itself is a successful constructor cut. This packet
does not claim to execute the whole preceding fiber-quadrant producer or to
eliminate its fallible relation, recipe, dependency, and sampling operations.

### Some-provenance restoration and cleanup

`syncAction` computes all raw wait branches. Idle requires `queued = consumed`
and an empty worklist. Running checks bounded integer addition, operation
identity, the queued cursor, both allowed consumed cursor values, actual
frame lookup, destination acknowledgement, and occurrence/cause equality.
Ready checks the same bounded successor and owner, `queued = consumed =
ack.index + 1`, and the exact returned stack length. `maximum` is the native
integer maximum for checked addition, not inference fuel.

`SyncStep` includes failed guards, failed wait preparation, failure before
and after opening a child frame, inner failure, start, a shared control
event, a silent control cut, NoChild, and delivery. Inner failure deliberately
allows its partial state without requiring a successful `C.Run`; this
overapproximates errors, including nested cleanup. Normal conservation
theorems are not applied through an error edge. The exact successful semantic
body of `step_typed_drain` remains with its existing native owners.

`SyncConsume` describes finite executions of the actual More loop. There is
no theorem that every Running child terminates. Its normal-control theorem
constructs a common `C.Run` from the represented successful events.

The non-circular Ready result is `synchronous_delivery_has_real_return`.
Starting from `C.Run C.initial s`, the exact Ready selection yields an
actual member of `s.returns` with the selected destination ticket, frame index,
transition count, ReturnReady phase, diagnosed flag, no current item, and no
pending acknowledgements. `ReadyOwned` is derived by induction over every
existing `C.Step`; `popReplay` constructs the new receipt. No terminal-frame
or child-completion witness is an input to this result. A diagnosed return
does not assert that diagnostics found no conflict.

The error epilogue has a small but material ordering detail. When extra child
frames exist, Rust truncates them and then looks up the Replay operation with
`?`. If this lookup fails, the function returns before restoring the saved
processing globals. `cleanup` retains that branch. Otherwise it restores the
saved globals, and resets the wait to Idle only when it truncated extra
frames. The cleanup does not clear the worklist; `cleanup_keeps_worklist`
checks that fact. The error route is therefore not silently promoted to a
normal quiescent state.

## 3. Main theorem interfaces

All names below are under `YulangClosure.OriginalReplayDrain`; `C` denotes the
existing `NativeDrainOwnership` types.

`ordinary_return_issues_all` takes a state, fixed task, actual child vector,
resource observations, and the actual active working-frame guard. It computes
`ordinaryDrive resources id (begin s task children)` and proves:

```lean
C.Run s result.1 ∧ result.2 ≠ .more ∧
  (result.2 = .complete ∨ result.2 = .queued →
    ∀ index, index < children.length → Issued batch result.1 index)
```

`Issued` includes both `work ∈ state.issued` and `work ∈ state.queue`, exact
task/relation equality, and ticket
`⟨operationBirth, operationId, childIndex, childRelation⟩`.

The processing bridge has the exact interface:

```lean
queued_before_empty_transport
  (run : BeforeReturn floor s t)
  (indexed : Indexed s.frames)
  (queued : work ∈ s.queue)
  (empty : t.queue = [])
  (top : t.frames = frame :: rest)
  (sameFrame : rest.length = floor)
  (noCurrent : frame.current = none) : Processed t work
```

`Processed` means membership in an actual frame's `processed` list or in an
actual returned frame's processed list. It is not semantic subtyping success.
`BeforeReturn` contains the actual existing `C.Step`s and requires the owning
stack position to remain present at each step source. It allows nested drains,
their returns, preparation, commit, acknowledgement, and all other existing
normal control constructors. No constructor of the frozen owner model was
removed or given a stronger guard.

`Indexed` is the concrete native frame-index invariant. `step_indexed` covers
all constructors, including commit; `run_indexed` derives it from the initial
empty stack rather than requiring an unexplained native invariant.

`ordinary_children_processed` composes the computed ordinary loop with that
bridge. `replay_relation_processed` specializes it to the actual production
vector of RelationIds. The latter concludes, for every successful raw vector
lookup `relations[index]? = some relation`:

```lean
∃ work, work.task = task ∧ work.relation = relation ∧
  work.ticket = some ⟨s.nextBirth, s.nextOperation, index, relation⟩ ∧
  Processed last work
```

The premises are the actual normal ordinary return, the shared continuation,
the frame-index fact, and the final empty queue/current cut. There is no
fairness, diagnosed-empty-stack, consumed-cursor completion, semantic child
success, or future-success premise.

`physical_children_before_empty` starts from a physical interner history, an
indexed active control state, and the computed existing physical port drive.
It constructs its shared control run and complete issuance list. Each job
has its exact task lookup, native `AdmissionResult`, physical stored-key
readback, actual relation ID, and membership in the same queue. The theorem
then proves processing at any matching empty-Transport continuation.
`function_four_ports_before_empty` retains the exact full builder equation,
length four, port order, readbacks, and renamed child pairs. The four ports are
argument, argumentEffect, resultEffect, and result, with the existing native
variance. The existing physical port driver's local execution fuel remains
an explicit execution witness; it is not a proof that global inference is
bounded or terminating.

## 4. Application and remaining owners

For NQ §5.2, a normal ordinary Replay return now yields the actual finite
enqueue history, and the proposed empty Transport cut yields real dispatch
events for every previously queued child. For §5.3, once the separately proved
fresh-endpoint chronology identifies an earlier matching Replay as ordinary
and owned by this drain, the same result applies to its raw child relation.
The Function port result supplies the exact physical argument relation
alongside the two Effect children, without choosing an independent control
history or replacing the actual task with a decoded pair.

The following boundaries remain explicit:

1. This module exposes `BeforeReturn`. The parent-owned
   `OriginalDrainBoundary.lean` establishes that a specific birth/index working
   owner cannot disappear or leave working phase before its own empty
   boundary, over every unchanged `C.Step`. Its application-side composition
   with this module is owned by the parent in `OriginalReplayBoundary.lean`.
   This leaf has not altered either file or claimed that a stack-depth premise
   alone is a source first-boundary proof.
2. Extracting the common control trace from the entire Rust execution remains
   an operational/source owner. In particular, `C.Step.dispatch` records the
   actual end of dispatch but does not interpret its full Context, operand,
   Value/Effect, extrusion, and retained-rewrite semantic body. The local
   physical drive is computed, but its occurrence in every relevant whole
   normal source dispatch still needs that extraction.
3. The Replay producer's exact retained fiber quadrants, dependency-key
   deduplication, `replay_heads`, append-only physical fibers, and the
   pre-settlement level/representative facts remain the owners of NQ §§5.1,
   5.3–5.4. This packet does not assume a successor-row production law to
   manufacture the missing proof.
4. The Some branch is a guard-exact control projection with explicit errors,
   not a complete Rust semantics or a proof of child-drain termination.
   Raw metadata/resource readbacks and opaque native error values still need
   the whole-state correspondence. Error states are not required to preserve
   the normal control invariant.
5. The original whole-language soundness, Effect hygiene, principality, and
   inference-accessibility propositions remain open. There is no source-level
   divergence theorem in this packet and no assertion that a finite native
   implementation cannot stop with an error or resource exhaustion.

## 5. Actual verification and axiom audit

Installed versions were read during this packet:

- Lake `5.0.0-src+eb6cafb`, reporting Lean `4.35.0`.
- Lean `4.35.0`, `x86_64-unknown-linux-gnu`, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
- Project pin: `leanprover/lean4:v4.35.0`; no external packages in the existing
  manifest. The parent remained the sole shared `.lake`/build owner.

From `notes/theory/lean`, the direct check was:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024 YulangClosure/OriginalReplayDrain.lean
```

The final direct check exited 0. A temporary exact source copy followed by
`#check @...` and `#print axioms ...` for every one of the 36 authored theorems
was then checked with:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024 --root=/tmp /tmp/yulang-replay-audit.lean > /tmp/yulang-replay-audit.log 2>&1
```

That complete audit exited 0. The direct invocations produced no `.olean`
files. The pinned binary needed the already authorized `require_escalated`
execution path in this environment; no toolchain, manifest, cache, root
imports, compiler, or Git mutations were made by this leaf.

Complete axiom groups (all names have the namespace prefix above):

| Actual dependency set | Every theorem in this group |
| --- | --- |
| none | `noChild_not_more` |
| `propext` | `issued_mono`, `indexed_commit`, `step_indexed`, `run_indexed`, `before_return_control`, `sync_start_exact`, `sync_deliver_exact`, `release_control`, `sync_no_child_exact`, `synchronous_normal_control`, `synchronous_consume_normal_control`, `cleanup_keeps_worklist`, `cleanup_restores_processing`, `replay_child_exact` |
| `propext`, `Quot.sound` | `ordinary_more_exact`, `ordinary_more_decreases`, `ordinary_more_control`, `enqueued_at`, `ordinary_step_batch`, `ordinary_drive_batch`, `begin_at`, `ordinary_return_issues_all`, `indexed_member`, `restoration_held_exact`, `initial_ready_owned` |
| `propext`, `Classical.choice`, `Quot.sound` | `step_pending_above`, `before_return_pending`, `queued_before_empty_transport`, `ordinary_children_processed`, `step_ready_owned`, `run_ready_owned`, `synchronous_delivery_has_real_return`, `physical_children_before_empty`, `function_four_ports_before_empty`, `replay_relation_processed` |

The module contains no `sorry`, `admit`, project axiom, `sorryAx`, checker
bypass, or native-evaluation proof shortcut. Exact printed theorem types and
all axiom results are retained in the audit log.

Material failed checks were repaired rather than counted as passes: an
executor disconnect destroyed an earlier session handle, so it was rechecked;
Lean rejected raw List-membership pattern matching, reserved local names,
the unavailable `tauto` tactic, a dependent match simplification, constructor
argument patterns, incorrect guessed port constructor names, and a missing
induction-hypothesis argument. The final check and full audit above are the
successful receipts after those repairs.

## 6. Frozen hashes and handoff

| Artifact/input | SHA256 |
| --- | --- |
| `OriginalReplayDrain.lean` | `ab8900724f0a5ae41c3c1342e1f8024aff465fbabefcf6e68ecde8d8952ed878` |
| `NativeValueDrain.lean` | `826fa025241835aad606434b3d0fee2406b694d72ca1dbf03a618f3e61d1b095` |
| `NativeDrainOwnership.lean` | `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18` |
| `NativeReplayCurrent.lean` | `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` |
| `NativeValueRelationExecution.lean` | `118138bd45cef3db837a0742010944cdd0c513e9d352302d23889e497a89c4ea` |
| `NativeRelationInterner.lean` | `1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a` |
| `candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `/tmp/yulang-replay-audit.lean` | `d1bc89e8758636063e44bdc1c775e711dbfeda12483cc36b05cba166b472d841` |
| `/tmp/yulang-replay-audit.log` | `ce8b2c616b2b7daeb1f86b13b8e035ad96ee3f02d8b3003ac8528aa27033c863` |

Only this note and the leased new Lean module were written in the repository.
Owned scratch: `/tmp/yulang-replay-check.lean` (signature probe),
`/tmp/yulang-replay-theorems.txt`, `/tmp/yulang-replay-audit.lean`, and
`/tmp/yulang-replay-audit.log`. Earlier termination-packet scratch and frozen
artifacts were not altered. Integration, fresh independent review, record
synchronization, commit, and push remain with the parent.
