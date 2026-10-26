# Shared native drain ownership and diagnosed quiescence

Date: 2026-10-26. Baseline: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`.
Construction owner: `/root`. Status: constructive control projection; final
checks and fresh independent review are recorded in the accompanying handoff.
Original accepted-native correspondence and full inference soundness remain OPEN.

## 1. The original application

`SourceProblem.InferenceSoundness` still requires an original source derivation
with the same complete scoped witness for every supported generated solution.
Native acceptance additionally needs a faithful native-to-solution construction.
The earlier Replay cursor and frame-rollback results do not by themselves join
a queued child, the frame that processes it, diagnostics and its ordered
acknowledgement. Independently selected histories could not supply that join.

`NativeDrainOwnership.lean` constructs one forward event history containing the
operation table, worklist, frame stack, cursor updates and terminal receipts.
Its conservation predicates are proved from the initial state. They are not
premises supplied by the caller. The result is a control-ownership component,
not semantic validity of the processed relation or absence of diagnostics.

## 2. Exact represented state

A `Child` retains its own task and relation identity. Different children of an
operation are not forced to have one task. A `Ticket` retains operation birth,
operation identity, child index and admitted relation. A `Work` additionally
has an immutable occurrence serial. Native Transport can change the frame's
separate `processing` relation while that admitted occurrence stays identifiable.
No equality of the original and canonical processing relations is assumed.

Frames retain current work, the completed-dispatch occurrence history, exact
acknowledgement vector, prepared/completed cursors, stage, diagnostic-completion
marker, synchronous destination and transition count. The native vector is
represented exactly as `done ++ pending`; completed is `done.length`.
`frame_split_exact` recovers both native vector slices. This split does not
discard duplicate vector entries or equate different frame lifetimes.

The issued, transferred, acknowledged and returned lists are proof history.
They record real event cuts and are not extra runtime success certificates.
The operation's origin task and allocation birth are retained provenance;
each child's actual payload determines the queued work. All complete task,
relation and source-key interpretations still belong to the common native
readback, not to an identification of arbitrary equal natural numbers.

## 3. Native transition inventory

Line locators refer to the frozen baseline source bytes.

| Native owner | Represented event and guards |
| --- | --- |
| `candidate_context.rs:3992–4076` | Allocate the exact indexed child sequence with zero cursors and Idle wait; reserve unrelated allocation identities separately. |
| `lib.rs:14185–14258` | Begin a drain with an empty worklist, enqueue its initial occurrence, and retain the new frame. |
| `lib.rs:15223–15250`; `candidate_context.rs:2385–2396` | Front/back enqueue and exact Replay transfer guards. The selected child supplies its own task/relation; an already queued child does not increment the queued cursor again. |
| `candidate_context.rs:4090–4155` | Synchronous start with equal cursors and empty worklist, exact Running destination, Ready retention and later delivery. Delivery changes the wait state and performs no additional acknowledgement. |
| `lib.rs:14260–14343,15166–15171` | Prepare all prior acknowledgement slots, prepare the actual next Replay owner, then pop and attach the same ticket to the current frame. Reservation precedes the native worklist mutation. |
| `lib.rs:14344–14420` | Transport changes the processing relation; successful Context/ordinary/structured Dispatch eventually clears current work. The completed occurrence is recorded at that actual clearing cut. |
| `lib.rs:14395–14420` | Enter and finish diagnostics before the acknowledgement phase. Completion of diagnostics can retain conflicts; it is not error-free acceptance. |
| `candidate_context.rs:2405–2453`; `lib.rs:14881–14945` | Prepare the exact operation/child, require ordered consumption and the exact synchronous wait, consume the acknowledgement, enter ReturnReady, retain the Ready receipt and pop the top frame. |
| `candidate_context.rs:2397–2404,4160–4228` | Saturating completion, empty-child retirement and Idle retired-operation reclamation. Saturation is represented literally rather than assuming an unavailable child bound. |
| Existing transaction commit owner | Re-arm every surviving frame by resetting prepared to completed. This does not acknowledge pending slots. |

These events are successful control cuts. Fallible preflight details that do
not change the represented state may stutter. `dispatch` is the end of the
whole actual dispatch, including a structured continuation when present; it
is not the earlier publication of `discharged` during Context. The native
Context body and its child emissions still need their actual callback and
Derived-edge map. No supplied child typing or semantic coverage occurs in a
`Step` constructor.

The phase/current/diagnostic guards at return are also derived from the earlier
stage transitions by `ready_frame_readback`. They are not independent terminal
assumptions needed by the public run theorems. Native capacity, dirty-work
settlement and top-index checks remain required for projecting real execution.

## 4. Constructed consequences

`step_invariant` and `run_invariant` prove that every issued occurrence is still
queued, held by a live frame, or in a returned frame's processed history. Every
transferred ticket is still queued, held in a live acknowledgement vector, or
has a diagnostic-completed acknowledgement receipt. Completed live-frame slots
have real receipts. Returned frames have no current work or pending slots and
have reached ReturnReady after diagnostics.

`step_coherent` proves the actual stage implications and prepared-cursor
interval. At ReturnReady, `ready_frame_readback` derives all of:

```text
current = None; diagnosed = true; pending = [];
completed = prepared = replay_acks.length.
```

The two quiescence theorems start with `Run initial state` and an empty
worklist/frame stack. They conclude respectively:

1. Every issued occurrence belongs to an actual returned frame, with the
   diagnosed/ReturnReady/empty-current/empty-pending fields intact.
2. Every transferred child ticket has an exact ticket receipt recorded after
   diagnostics. This is child-ticket membership, not a claim of a new
   acknowledgement for every repeated enqueue of an already queued child.

`outstanding_ticket_has_owner` gives the contrapositive frontier: before its
receipt, a transferred ticket must still be in the queue or a live frame.
`frame_prefix_has_real_receipts` exposes the consumed prefix. None of these
theorems takes a separately chosen cursor run or a frame-success theorem.

The explicit `Witness.synchronous_transport_run` constructs allocation,
synchronous start, dequeue, a changed processing relation, Dispatch,
diagnostics, acknowledgement, return and delivery. Its computed readback
retains the original admitted relation and exact ticket, both final cursors
equal one, and one acknowledgement unchanged by delivery. It is a kernel
checked control example, not an accepted source program or native regression.

## 5. Exact remaining connection

This module does not finish the original native theorem. Its remaining use
requires the following concrete original suppliers:

* **One native committed-history projection.** Map actual allocations, complete
  payload identities, queue operations, frame indices and callback cuts into
  this run. Include failure/cancellation and identity reuse through the same
  journal history. The R3 cancellation results are available, but no theorem
  here identifies a separately erased operation history with a separately
  erased frame history. `Run` itself describes successful forward events;
  cancellation is not silently treated as forward allocation.
* **Context/Transport/Dispatch readback.** Join the admitted key, actual
  Transport Derived edge, early Context publication and completed Dispatch
  body in that same history. For duplicate/discharged branches, retain the
  prior same complete owner or active dependency. `processed` is not by itself
  an installed Context or Value body. The complete local Context construction
  supplies that body once its actual callbacks and owner path are connected.
* **Diagnostic acceptance.** Interpret every conflict leaf and establish that
  the accepted compiler result has none of the rejected diagnostics. The
  `diagnosed` bit only records that the diagnostic stage ran.
* **Semantic and source interpretation.** Interpret every retained row/Value/
  Context obligation, all actual record and Call children, and the original
  complete `nu,K,D`/world/scope witness. Neither empty queues nor acknowledged
  children establish those meanings.

All original optional records, method selection, Call, effects, scopes and
supported inputs remain in the parent. No altered language semantics, narrowed
challenge domain, new project axiom or assumed whole soundness law is adopted.

## 6. Verification ownership

The isolated project and all failed/successful source snapshots, exact commands,
resource receipts and complete originating-declaration census are retained in
`native-drain-r4`. Lean remains pinned to 4.35.0, one thread and `-M1024`.
An early successful module build reached a 1-GiB aggregate wrapper threshold
during the named audit. The wrapper-plus-Lake-plus-Lean allowance was therefore
raised locally to 1.25 GiB; the Lean/project bound was not changed. Later checks
use a separate single CPU to avoid contending with the other isolated proofs.
No source/compiler/configuration/expected-output change is part of this packet.

The exact final roots, complete axiom sets, retained failures and frozen hashes
are recorded in `tasks/agent-loop/inbox/20261026-native-drain-ownership-r4.md`.
Fresh independent review and default integration remain separate evidence.
