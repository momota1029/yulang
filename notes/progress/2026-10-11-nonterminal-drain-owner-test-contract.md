# Retained nonterminal typed-drain owner: bounded test contract

Date: 2026-10-11
Status: unreviewed research-only proposed test contract and static obstruction; no implementation or suspension gate closure.
Primary-pinned baseline: `2dbd86d0f`.
Lease: this note only. Static reads only; no compiler/test edits, test execution, Git command, delegation, or shared-record writes.

## Objective, authority, and stopping premise

Specify discriminating failure fixtures for an actual retained nonterminal typed-drain owner. The method is a static correspondence audit of the assigned fixtures and transaction owners, followed by a bounded proposed test matrix. This complements the acknowledgement-prefix falsifier and source audit; it does not rerun their model or produce the constructive theorem assigned to the prover.

The governing Authoritative suspension contract is `notes/design/2026-10-11-private-candidate-suspension-contract.md` §3 items 7–8 and §6. Typed drain must own its current item, remaining worklist, processing scope, transitions, diagnostics and replay continuation; Function dispatch must retain admitted children through enqueue. Failure restores the exact pre-route state, while a successful pause retains unfinished obligations. The contract records user approval, “承認して実装を進めて”, on 2026-10-11. No alternate language meaning, supported-input restriction, or public API decision is selected here.

**Stop condition reached:** the inspected source has no actual retained nonterminal drain resume owner. `constrain_live_item_with_inferred_entry` always constructs a new frame and runs the synchronous loop (`lib.rs:11875`). `candidate_step_typed_drain_terminal` accepts only `Acknowledgements`/`ReturnReady` (`12289`). The Function helper is separately callable, but its production caller drains synchronously from that new frame. Consequently the matrix below is conditional on separately authorized owner construction; no current fixture can substantiate its full claim. This note freezes the missing premise instead of replacing the owner with another toy driver.

## Exact missing source responsibilities

Locators refer to `crates/yu-solver/src/` in the inspected working snapshot.

| Source owner | Required bridge for the proposed fixture |
|---|---|
| `lib.rs:11875–11918`, fresh typed drain | A retained-index entry must resume the saved stage, not run the initial constructor again. The constructor asserts an empty worklist, clears diagnostics, seeds/enqueues initial work, then clears `current`, `function`, and `context_consumed` at its loop header. |
| `lib.rs:8968`, route begin | It currently asserts an empty worklist and diagnostic delta. The actual owner must retain/journal pre-existing queue and diagnostic state before accepting a route with unfinished work. Deleting the assertions supplies no rollback ownership. |
| `lib.rs:9310`, route rollback, especially `9637–9642` | Rollback currently clears the typed worklist and diagnostic scratch. The owning transaction must restore a committed queue and pending diagnostics, including order and diagnostic indices. |
| `candidate_context.rs:1727`, frame undo | `prepare_typed_drain_update` can preserve an old frame and its ack allocation. The retained owner must call it before nonterminal frame mutations. Terminal-only use does not protect nonterminal re-entry. |
| `candidate_context.rs:1674`, commit | Commit resets `prepared_acks=completed_acks` and `terminal_prepared=false` on retained frames. Next-route entry must reacquire applicable undo for every pending ack before work. |
| `lib.rs:11928–11961`, pre-pop transfer | The existing pre-pop owner prepares only the new front acknowledgement. Full retained-prefix preparation must precede pop/append; reservation through append must remain atomic or retain an explicit resumable preparation stage. |
| `lib.rs:12351`, Function step | Both direct Function entry and owner dispatch must enforce frame/prefix preparation before admission or enqueue. Admission retains `pending`; enqueue advances `next` only after insertion. |
| `lib.rs:12227–12259`, diagnostics | The owner must identify completed diagnostic work and retain unfinished diagnostic inputs/stage. A single `Diagnostics` enum value does not by itself make interruption inside diagnostic completion resumable. |

`TypedDrainFrame` (`candidate_context.rs:28`) retains current item, Function stage, transition count and acknowledgements, but contains no remaining queue or diagnostic scratch. Session ownership can satisfy the contract if its transaction explicitly restores that session state; this note does not prescribe moving storage into the frame.

## Minimized fixture family, after the missing owner exists

Use actual compiler operations and the actual retained owner. All setup occurs before one successful private pause/route commit; capture the oracle **after** commit. An empty-queue adapter that manually prepares a frame is only a helper control.

The base valid repeated-operation fixture needs two real operation IDs and three acknowledgement occurrences:

```text
R: children=[r0,r1], queued=2, consumed=0, retired=false
S: children=[s0],    queued=1, consumed=0, retired=false
frame.replay_acks=[(R,0),(R,1)]
frame.completed_acks=frame.prepared_acks=0 after commit
queue=[TypedWorkItem(s0, relation=S.children[0], replay_ack=(S,0))]
diagnostic_delta=[d], diagnostic_delta_indices={d:0}
typed_pairs[d].completion=Pending
```

Distinct relation/provenance identities should be retained even when endpoint pairs coincide. Consecutive `(R,0),(R,1)` are valid different children of the same operation. Repeating the exact `(R,0)` is an invalid-input control and must not be presented as successful duplicate consumption. Where synthetic repeated relations are needed, the existing terminal fixture's accounted child-vector extension is an available private control, not source authorization.

One queued item is enough to discriminate clear-on-rollback from restore; add a two-item unequal queue permutation control to discriminate exact order from reconstruction. One diagnostic root with a real pending memo is enough to expose lost diagnostic delta/index ownership. Prefer `candidate_reopen_root` (`lib.rs:11401`) after forming a real memo to retain the pending root; hand-inserting a diagnostic key without its memo is a narrower storage control.

Use separate saved-stage variants, preserving the same pending prefix:

- **Before pop:** `current=None`, no Function dispatch; queue nonempty.
- **Retained current item:** after actual pop/append, `current` retains the exact task/relation/ack, including provenance; saved `Context` or `Dispatch` resumes that item before any next pop. The ack retained in `current` and in the list denotes one occurrence, not two completions.
- **FunctionAdmission:** current parent retained, four named children retained, `next=0`, `pending=None`. The semantic four-port array is not minimized to a different language operation.
- **FunctionEnqueue:** after actual admission, `next=0`, exact admitted relation in `pending`; the queue does not yet contain this child.

For a completed-prefix control, extend R to three children, complete R0 through the actual terminal owner, commit that success, then retain pending R1/R2. Capture `consumed=1` as the rollback baseline. Do not assume a zero cursor is an adequate oracle.

## Failure and success matrix

Every failure ends the current route and compares with its independent post-commit snapshot. Intermediate assertions distinguish mutation-before-preflight from a later successfully restored mutation.

| Cut / injection | Discriminating requirement |
|---|---|
| Before frame-update reservation | Failure leaves old frame, queue, pending diagnostic inputs, processing, operations and their membership unchanged. |
| First pending completion reservation | No pop, transport, context execution, Function admission/enqueue or diagnostic completion occurs. |
| **Second** pending completion reservation, after R0 preparation succeeds | No semantic side effect occurs; rollback restores both frame and operation state. This rejects first-only prefix preparation. The existing boolean fail hook fails the next reservation; it cannot target the second call of an uninterrupted prefix loop. A separately authorized counted failpoint is needed for genuine later allocation-reservation coverage. An invalid second ack tests validation failure only. |
| After actual pop/append of S0 | Inject failure before its next fallible stage. Restore the exact pre-route queue and frame/current state; R and S must have their saved queued/consumed/retired states. Appending S must not falsely certify preparation of R. |
| After actual Function admission | Pending relation/dependency and stage are retained on success/commit. Failed route restores saved relation/dependency/lifecycle state and frame. Cursor stays at its old port until enqueue succeeds. |
| After actual Function enqueue | Failed route restores queue contents/order, pending item, stage and `next`; success enqueues the admitted item exactly once and advances the cursor exactly once. Re-entry must not admit a replacement relation. |
| After diagnostic completion, before acknowledgements | Failure restores pending/completed memo state, diagnostic inputs/scratch and errors. Successful commit resumes without replaying completed diagnostic output. If the owner exposes no pause inside completion, keep that subroutine atomic and test only its boundaries. |
| After first terminal completion, then after final completion/frame removal | Failure restores the saved operation maps and retired state, frame plus ack capacity, processing scopes, queue/diagnostics and parent restoration pointer. Removal of a pre-existing frame must be undone rather than treated as truncation of a newly created frame. |

Also run deterministic success controls: unchanged private pause twice performs no queue/cursor/diagnostic work; a relevant resume completes children in original order; commit releases preparation and next route reacquires it; same-route repeated entry does not duplicate completion undo; empty pending prefix and nonzero completed prefix are preserved. The bounded planned envelope is one retained topmost drain, two operation IDs, up to four acknowledgement occurrences, one or two queued items, one pending diagnostic root, four Function ports, and at most two commits. No seeds or enumeration range were executed.

Do not insert a successful commit between new-item completion reservation and pop/append unless the actual owner retains and revalidates that reserved-item stage. The earlier falsifier already covers that conditional split; this packet uses it as an existing failure condition rather than repeating its attack.

## Independent state oracle and mutation discrimination

Save complete cloned replay operations for R/S and map membership, plus each live parent restoration. Compare `children`, task/inputs/heads/prior/incoming-use, `queued`, `consumed`, `retired` and restoration ownership directly after rollback. Save exact whole frames, ack capacities, current item, all Function data and processing scopes. Save queue contents in order; save diagnostic delta/index and all completion scratch, typed memos, errors and reported-error keys. `RouteCheckpoint::capture/assert_restored` (`lib.rs:8276,8397,8585`) already clones/compares queue and diagnostic state and is a useful session-level oracle. Add direct context operation/frame snapshots because the context checkpoint primarily records frontiers, not full old operation contents.

`prepared_acks`/`completed_acks` are additional assertions, **never the definition of restored operation state or applicable undo**. The oracle must not invoke the preparation helper to construct its expected result. It must detect wrong R/S identity, skipped pending R1, loss/duplication of the current occurrence, cursor advancement before enqueue, replay of admission, queue clearing/permutation, diagnostic clearing/replay, and lost terminal removal undo. Wrong reverse replay-undo order needs snapshots with actually different saved states: retain the existing just-in-time terminal test pattern or introduce a real transfer between snapshots. Merely preflighting two R children at the same consumed state does not discriminate undo order.

For accounting, compare `bytes()` with `enumerated_bytes()` throughout and inspect event-time resource sampling before cleanup. Warm journal capacities for exact retained-byte rollback comparisons. Separately exercise cold frame/ack/undo allocation and failure peaks; allocator/journal capacity growth and monotone resource peak observations are not automatically exact logical rollback obligations. This distinction follows the existing accounting fixtures rather than silently weakening logical state equality.

Oracle independence is bounded: direct saved state is independent of acknowledgement preparation and its scalar counters, but shares the compiler's operation constructors, fixture validity and equality implementations. It is not a second source semantics oracle. Synthetic fixtures establish only actual helper/owner transaction behavior; genuine source reachability and §7 readiness/withdrawal/recomputation remain separate.

## Current fixture availability

All paths below are `crates/yu-solver/src/candidate_context_tests.rs`. Static availability is established; no result from running them is claimed.

| Locator / fixture | Existing evidence / missing extension |
|---|---|
| `3947`, `owned_function_dispatch_retains_admitted_child_until_enqueue_and_rolls_back` | Both admission and enqueue calls, four named ports, current parent, queue order and failure. Frame is created in the failing route; no committed prior nonterminal owner, old queue/diagnostics or pending ack prefix. |
| `4305`, `terminal_drain_fixture` | Real replay/restoration handles; synthetic two ordered occurrences or empty batch; accounted child storage; warm undo. Stage is terminal only, one operation ID. |
| `4348`, `typed_drain_terminal_partial_ack_failure_resume_and_exact_rollback` | Committed partial terminal cursor, direct replay/frame/restoration snapshots, reservation failure, removal rollback, capacity/bytes and diagnostics nonrepetition. No nonterminal queue/current/Function continuation. |
| `4409`, `typed_drain_terminal_final_child_handoff_and_empty_batch_keep_parent_handle_usable` | Parent handle remains usable through final/empty child handoff; transactional rollback and reclamation. No nonterminal suspension. |
| `4457`, `typed_drain_terminal_cold_undo_samples_active_and_rollback_peak_before_cleanup` | Cold allocations, failure sample, active/undo ack accounting and reuse. Its second-ack preparation is manual; it is not later-prefix-owner coverage. |
| `4527`, `parsed_local_use_retains_one_fresh_parent_across_committed_pause_and_failed_resume` | Parsed Local, retained fresh parent/restoration, committed pause and failed resume; compared facts/errors/use count against separate parsed session. Its adapter explicitly has no production `Suspended` outcome; no retained nonterminal drain seam. |
| `4630`, `internal_restoration_owner_steps_keep_multiple_live_products_and_return_ownership` | Three sequential products, child handle retention, failed owner step, diagnostics before advancement. Successful steps finish typed drain; no committed nonempty typed queue. |
| `1641`, queued replay child fixture | Queued versus consumed distinction through real enqueue/drain and rollback. Starts next route with empty queue and consumes it synchronously inside that route. |

## Evidence, dependencies, limits, and next action

Checks performed: narrow `rg` inventories; `sed`/`cat` static reads of the rules, governing contract, acknowledgement research and assigned source/fixtures; working-input SHA-256 capture. No test/build/probe, random seed, mutation execution, formatter, Git command or child launch ran. One sequential lightweight shell inspection stream; no heavyweight process. CPU/RSS and exact reasoning wall time were not measured; work stayed within the assigned 25-minute ceiling. Search was limited to the named drain/route/diagnostic owners and fixtures, not an exhaustive whole-compiler caller proof.

| Inspected dependency | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `77a3c4bdb48d438f7e5678c35302ad2aa1f6665ca9cbb8f3fdc0a48e730a30f4` |
| `crates/yu-solver/src/candidate_context.rs` | `24909fb9a09e6f9d383e5b1f8f4f8db9d5f7e587a1ed5bbb6a47ead77e140831` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `3a63e52796fcc568e50f59462691ccde77acac5a0bcc0d02d550402811e31ba3` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Ack-prefix source audit | `70616b915b5d10532251e3e442e96fc973102755af2937a5bf26ad236b1896cc` |
| Ack-prefix falsifiers | `903c4b76b080c58c404dc4d310cd43620b8b01ea444979c1bcb8d86c0e239746` |

The baseline SHA was supplied by the primary; this no-Git lane did not compare committed blobs. Inspected compiler hashes match those recorded by the earlier source audit, but the primary must revalidate snapshot equality before integration. No dependency changes were authored.

Recommended next action: assign a separately authorized implementation packet for the actual retained nonterminal owner and queue/diagnostic transaction ownership, then instantiate this matrix through that owner with a counted second-prefix reservation failpoint. Prefix-helper tests alone leave the stopped premise open. Nested drains, lifecycle invalidation, representative changes, source/SCC publication, exact recognizer/readiness, full §7 and production certificates remain unverified.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-nonterminal-drain-owner-test-contract.md`.
- Baseline: `2dbd86d0f` (primary-supplied); committed dependency equality requires primary revalidation.
- Changed dependency hashes: none authored; inspected hashes above, end-of-lane recheck reported to primary.
- Review status: producer-only, unreviewed proposed bounded test contract/static obstruction; not independent certification, executed regression, or theorem closure.
- Checks already run: static rules/source/fixture inventories and dependency hashing only; no executable verification.
- Proposed checkpoint message: `Record bounded retained nonterminal drain owner test contract`.
- Shared-record deltas intentionally left for primary/curator: retain missing actual nonterminal resume owner and committed queue/diagnostic restoration as open obligations; link the bounded matrix and counted failpoint requirement; preserve the reviewed synchronous terminal slice and all full suspension/source/lifecycle gates without promotion.
