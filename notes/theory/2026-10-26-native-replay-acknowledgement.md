# Native replay acknowledgement: checked cursor and terminal projections

Date: 2026-10-26. Status: kernel-checked component; fresh independent review
pending. Primary-reported baseline: `yulang3`,
`b1a769800c609db77ed7ee5614af9906fd57ed0d`.

## 1. Result and exact scope

`YulangClosure.NativeReplayAcknowledgement` constructs a finite execution
projection of the actual replay cursor and typed terminal-owner operations.
Its root derives the cursor bounds and the ordered acknowledgement prefix
from zero initialization and the transcribed field-writing transitions. It
does not take a conservation law, valid acknowledgement list, `Covered`,
`CurrentTransport`, or a semantic model as an input.

The result is deliberately a **projection theorem**, not an authenticated
execution of the entire native solver. The full operation map, worklist,
typed-drain stack, restoration map, source occurrence/cause, representative
forest, dependency graph and route journal are not simultaneously modeled.
Section 6 names the exact remaining readback obligations. In particular,
`ready_owner_exact` establishes consistency of the retained operation fields;
it does not establish that a real native stack frame exists. `Returned` is the
readback predicate `retired && waiting_child == Idle`, not a semantic child
derivation. These limitations apply to every theorem in this note.

The unchanged original parent is `SourceProblem.InferenceSoundness`
(`Contracts.lean:128`): every supported original source, original scope,
generated constraint and successful solution must yield an original source
judgment with the same scoped witness. Its full scope, including sharing,
generalization, Call, effects and optional records, remains OPEN. This packet
does not replace that scope with a scalar or exact-record fragment.

## 2. Construction from the native owners

`NativeState` contains exactly the four mutable cursor fields saved by
`ReplayOperationUndo`: `queued`, `consumed`, `retired` and `waiting`.
`Wait` retains the actual `Idle`, `Running(ack, drain_index)` and
`Ready(ack, drain_index, transitions)` alternatives. The operation's immutable
`children : List Nat` is an arbitrary list of relation IDs, including repeated
IDs. The operation ID is a separate parameter.

The ghost `Projection` adds finite transfer and acknowledgement histories,
successful preparation indices, and whether the runtime operation is still
present. `readback` erases the histories, returning the cursor tuple while
present and `none` after reclamation. The histories are constructed by events;
they are not initially supplied certificates.

| Native owner | Transcribed projection and qualification |
| --- | --- |
| `candidate_context_begin_replay`, `candidate_context.rs:4065–4069` | `initial`: both cursors zero, unretired, Idle; all ghost lists empty. This is also the initialization for an empty child vector. Construction of the child vector itself remains in the lifecycle bridge. |
| `transfer_replay_child`, `:2384–2395`; `enqueue_item`, `lib.rs:15223–15249` | `Step.transferNew` increments `queued` and records that exact index. `transferOld` permits an already queued index between `consumed` and `queued-1`, with no second transfer. Both require Idle, live storage and an unretired operation. The new-index lower guard follows from the derived cursor bound. |
| Synchronous child start, `:4102–4120`; `start_typed_drain`, `lib.rs:14186–14232` | `Step.start` combines the successful initial enqueue transfer and the subsequent Running assignment, starting from `queued=consumed`. The outer worklist-empty and actual frame/source metadata checks remain readback obligations. |
| `prepare_replay_child_completion`, `:2405–2427` | `Step.prepare` records a successful native preflight: `consumed ≤ index < queued`; Idle or exact Running ack with `queued=index+1`. It does not advance `consumed`. |
| `complete_replay_child`, `:2444–2452` | `Step.acknowledge` requires that earlier prepared occurrence, `consumed=index`, and the native waiting guard. Its proof derives `index<queued≤children.length`, so the actual increment branch of `acknowledge_replay` is justified. Native completion alone does not recheck the whole preflight guard. |
| No-child branches, `:4111–4116,4188–4198` | `Step.noChild` retires only at the exhausted child vector with matching cursors. Empty initialization is not itself retirement. |
| `prepare_replay_return` / `retain_replay_return`, `:2431–2442` | `Step.returnReady` carries the exact ack and drain index from Running, with `consumed=queued=index+1`; it retains the same completion count in Ready. `returnReady_exact_event` exposes these precise equalities. |
| Ready release, `:4133–4153` | `Step.delivered` sets Idle without incrementing `consumed` or acknowledging again. Its stack-length readback is explicit external data, not an internally authenticated native stack. |
| Error wrapper, `:4174–4181` | `cancelOwnedDrain` projects the Running-to-Idle reset. The wrapper's actual truncation guard, previous processing state and frame removal are not proved by this cursor reset. |
| Retirement, `:2195–2202` | `Reclaimable` and `RestorationHeld` retain the retired/Idle requirement and the exact live-restoration pointer test. The supplied parent and map still require native authentication. `reclaim` erases runtime presence while preserving ghost history. |
| Commit, `:2209–2245` | Cursor commit preserves all four native fields and invalidates preparation history for the next route. Reclamation is a separate eligible event, not completion of pending children. |

`FrameProjection` contains the terminally relevant frame fields: the ack vector,
completed/prepared counters, terminal preparation bit, destination ack, index,
stack-length readback and transition count. It begins with the empty frame at
the successful owner-assignment point; a synchronous destination may therefore
already be `Some ack`. `working` erases the distinct nonterminal stage tags;
it is not a proof of their dispatch behavior.

`FrameStep.takeAck` records the actual Transport append and prepared-counter
increment (`lib.rs:14320–14335`). `dispatchReturn` retains the actual returned
transition-count assignment (`:14355–14362`); its value is a dispatch readback,
not a newly supplied semantic law. This event is essential because successful
native receipts need not have a zero transition count. `enterDiagnostics` and
`diagnostics` retain the stage order (`:14405–14416`). Terminal preflight,
completion, empty-vector ReturnReady and pop transcribe `:14881–14947`.
Frame commit resets `prepared=completed` and `terminalPrepared=false`, exactly
as `candidate_context.rs:2212–2216` does.

The terminal frame projection allows the acknowledged vector to contain any
acks. Its result is exact ordered **vector-prefix** consumption, including
repeated entries if present; excluding an impossible repeated operation/index
across the actual worklist requires the cursor/frame linkage in section 6.

## 3. What the kernel-checked roots establish

All names below have prefix `YulangClosure.NativeReplayAcknowledgement`.
The complete fully qualified types of all 35 named theorems are retained in
the audit evidence; the public roots have the following exact input boundary.

`cursor_projection_accounting` has type

```lean
Reachable operation children s → Accounting operation children.length s
```

`Reachable` is a finite sequence of `Step`s from `initial`. `Accounting` is
proved by induction and contains all seven fields below:

1. `consumed ≤ queued`;
2. `queued ≤ children.length`;
3. `retired=true → consumed=children.length`;
4. the exact Running/Ready operation/index/cursor conditions;
5. every retained preparation index is below `queued`;
6. the transfer history is exactly `List.range queued`;
7. the acknowledgement history is exactly `List.range consumed`.

Consequently `acknowledgement_position_exact` identifies position `i` with
acknowledgement index `i`, and `acknowledgements_unique` proves the occurrence
indices have no duplicates. `acknowledged_child_readback` obtains the actual
relation at that index in the same child vector. No injectivity assumption on
relation IDs is used.

`running_before_or_after_ack` proves that Running may have either
`consumed=index` or `consumed=index+1`, always with `queued=index+1`.
`ready_owner_exact` proves `consumed=queued=index+1` for Ready while retaining
the same operation/index identity. These are operation-field facts, not proofs
of structural child-graph closure.

`terminal_projection_accounting` derives
`completed ≤ prepared ≤ acks.length` and
`done = acks.take completed` from frame initialization and transitions.
ReturnReady implies all acks have completed; terminal stages require the
diagnostics event first. `terminal_projection_pop_all` proves that an erased
popped frame has acknowledged its entire exact vector, passed Diagnostics,
and has stack-length readback equal to its index. The stack projection is
observed at the selected active frame; nested native frames are not modeled.

`terminal_cursor_projection_return` is the explicit joint consumer. Its inputs
are reachable cursor/frame projections, both present, the frame's exact
destination `Some ack`, its ReturnReady stage, and the native return guard:
Running with that ack and that frame index, and both cursors `ack.index+1`.
It constructs the paired Ready and pop transitions, preserving both derived
accounting invariants, and returns the completed exact ack vector, diagnostics
completion and matching popped index. It does not take either invariant as a
premise. It still requires the two histories to be readbacks of the SAME native
operation/frame execution; merely choosing independently reachable records
does not establish that source correspondence.

The finite checked witnesses distinguish the misleading alternatives:

- `Witness.retired_running_reachable` constructs a one-child successful start,
  preflight and acknowledgement. The operation is retired and still Running,
  and `Returned` is false. Retirement therefore precedes the Ready/parent-release
  barrier in a legitimate projection trace.
- `Witness.repeated_relation_distinct_occurrences` uses `[7,7]`: relation
  equality coexists with different ghost child identities.
- `Witness.empty_initial_not_retired` proves the actual empty initialization
  remains unretired until the guarded no-child step.
- `queued_is_not_returned` derives that the no-provenance Queued frontier,
  with every child transferred but some unconsumed, is not Returned.

The memo/current-generation pair map is deliberately absent from these proof
states. `record_typed_pair_admission` / `mark_candidate_pair` execute before
structured children finish (`lib.rs:15295–15340`,
`candidate_intrusion.rs:423–456`). No current mark is treated as an ack,
returned child, or semantic certificate.

## 4. Transactions, cancellation and reused numeric IDs

`restoreCursor` transcribes the newest-first traversal of saved four-field
tuples, corresponding to the native reverse iteration over undo entries
(`candidate_context.rs:2101–2107`). `Journaled` constructs separate save and
write events. A modifying write needs a saved snapshot; an unchanged write
needs none. Commit and reclamation are excluded from the rollback suffix.
This is a projected journal trace, not a proof that arbitrary native histories
have already been mapped to it.

`journal_restores_exact_cursor` proves its rollback fold returns the starting
tuple, without assuming the result of rollback. `journal_cancel_projection_exact`
then cancels the erased suffix histories to the same saved projection, and
`cancelled_prefix_accounting` applies the root to that restored prefix.
This includes modifications of **older** operation owners; deleting newly
allocated nodes alone would not suffice.

`rollback_existing_exact` and `rollback_new_absent` reflect the native saved
allocation frontier (`:2108–2115`): existing IDs restore, newly allocated IDs
are removed. The latter is a statement about a supplied newly numbered
operation, not an assertion that every possible numeric ID was allocated.

`AllocationClock` retains an erased monotonically advancing birth count while
`rollbackAllocation` resets only the native numeric frontier.
`rollback_reuses_id_with_fresh_birth` constructs equal reused numeric IDs with
different child identities. Older retained operations keep their original
birth. This is proof history, not a proposal for a new runtime identifier.
Full replay-map restoration, restoration-owner undo, typed-frame stack undo,
physical/worklist journals and restored dependency/incidence graphs remain
separate obligations. This packet makes no general abnormal-path restoration
requirement beyond describing the current native mechanism.

## 5. Verification and preserved failures

Pinned installed toolchain:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual reports: Lake `5.0.0-src+eb6cafb` (Lean `4.35.0`), Lean
`4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The isolated project copies the three unchanged project configuration files,
imports only pinned `Std`, and has no external packages. Each focused process
used `LEAN_NUM_THREADS=1`, project `-j1 -M1024`, and a 120-second subprocess
limit. Task-bounded escalation was used for the already known sandbox native
self-location limitation; no toolchain/default/SYSROOT/dependency change was
made.

Final build `check11.log`: exit 0, selected module built, 2 jobs.
Final audit `audit12.log`: exit 0; **628 originating declarations, 245 theorem
constants, all 35 named theorem roots**, including private/generated constants.
Every declaration has its complete printed type and axiom report. The audit
enumerates by actual originating module, rejects project axioms and rejects
dependencies outside the three standard allowed axioms.

| Actual axiom set | Originating declarations |
| --- | ---: |
| none | 539 |
| `propext` | 51 |
| `propext`, `Quot.sound` | 22 |
| `propext`, `Classical.choice`, `Quot.sound` | 16 |

The principal cursor and composed roots use the last set; the exact journal
fold theorem uses no axioms. No project axiom, `sorry`, `admit`, `native_decide`
or kernel bypass occurs. A complete source search of this single changed
project module has no forbidden-token matches. Standard axiom acceptance is
not independent review or native-source authentication.

Evidence directory:
`/workspace/scratch/f98087c7ac1a/inference-native-replay-acknowledgement/`.
`manifest.json` fixes the module, source owners, governing inputs, three
configs, all logs, audit program and named-root evidence. `check01.log` through
`check08.log` preserve failed attempts: record-update layout, constructor-case
binding, reserved identifiers, arithmetic normalization and an implicit
parameter. These failures were repaired rather than hidden. `check09.log` and
`audit10.log` accepted a provisional version; before final submission, source
rereading found the absent Dispatch count-write event. That provisional freeze
was explicitly withdrawn. Its exact bytes and manifest are preserved as
`NativeReplayAcknowledgement-provisional-audit10.lean` and
`manifest-provisional-audit10.json`. The final source correction was checked
by `check11.log` and `audit12.log`. Twelve focused checker invocations were used
of fourteen granted; no Rust tests, native probes, new dependencies, Git
operations or shared-status/import edits were performed.

| Final evidence | SHA-256 |
| --- | --- |
| `NativeReplayAcknowledgement.lean` | `fd39f67d2a170b5d603238d48ea4facce2d9a085f4c302155b3aa1b10026cb52` |
| `check11.log` | `f807f70ff51a59a16011822afb9088deb4b2c867cdf86d45a07a1411c50f3e6c` |
| `audit12.log` | `7b65ca327b8bf2a2cefbff1c9f2c9c3011d52b1db5acb54ea5170c5b0ef920b7` |
| `manifest.json` | `54162df68fe238d64f32bb656aad07c43256435dfd3702104b6d70df77a74619` |

## 6. Application to the native lifecycle and remaining bridge

This component supplies the acknowledgement arithmetic and exact local
return-consumption result needed by the lifecycle paper §7. Once that paper's
successful native execution is mapped into these projections, its retained
replay owners have an exact finite occurrence prefix, and the terminal owner
consumes the corresponding frame vector after Diagnostics before pop. The
mapping cannot infer completion from admission or replace a Queued return by
Complete. A reclaimed runtime object may be absent while its erased history
continues to justify its already constructed events.

The exact remaining source obligations are:

1. Construct both projections from the SAME real operation/worklist/frame
   maps. Authenticate each ghost preparation against the correct frame's
   actual preflight and prepared/completed prefix, including commit invalidation
   and cancellation. Preserve the source occurrence/cause checks and actual
   stack length/destination, rather than choosing matching numbers afterward.
2. Authenticate immutable child vectors, the current restoration parent/map,
   allocation frontier and each save/write journal event against their owners.
   Compose cursor and frame rollback with the native physical/worklist,
   dependency/incidence and representative/generation restoration.
3. Construct the old-Replay suppression disposition and transport its whole
   constructor graph. The lifecycle frontier's discharged Effect
   filter/residual expansion square remains open, as do general dispatch and
   third-owner recursive dependency transport. Ordered acknowledgements do
   not discharge any of these graph obligations.
4. Apply genuine native coverage to the regular/record consumers and prove
   original source correspondence. The original record boundary `j`, full
   Call evidence, and contextual-effect meaning remain OPEN.

No production semantics, runtime storage mechanism or compiler behavior is
changed. The primary owns the complete native history bridge, fresh M3 review
and integration; this author does not independently certify this component.
