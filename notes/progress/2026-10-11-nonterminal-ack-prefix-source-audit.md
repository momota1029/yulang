# Nonterminal acknowledgement prefix: source-owner audit

Date: 2026-10-11
Status: unreviewed research-only static source correspondence; no gate closure.
Baseline: `6a962826ab46d7f58529f7162aa016997ed5418d` (primary-pinned).
Authority: private candidate suspension contract §§3 and 6, approved by the user
on 2026-10-11. This note preserves the selected execution order and transaction
meaning. It does not select another suspension meaning or establish §7 readiness.
Lease: this note only. Static inspection only; no compiler/test edits, Cargo,
executable experiment, child delegation, or Git mutation.

## Objective, method, and claim boundary

Identify the owners of typed-drain and replay acknowledgement mutations and the
earliest seam where a retained nonterminal frame can prepare all outstanding
completion undo before semantic work. The evidence is a finite inventory of
real producers, consumers, and direct callers, with source-derived conditional
failure traces. It is neither a constructive theorem nor an executed failure.

At this baseline there is **no production retained nonterminal typed-drain resume
entry**. `constrain_live_item_with_inferred_entry` (`lib.rs:11875`) always creates
a fresh frame and runs its entire loop, diagnostics, and terminal handoff.
Availability failure pops that new frame (`12263`). The separately callable
terminal step (`12289`) accepts only `Acknowledgements` or `ReturnReady`.
Function steps are callable privately (`12351`), but production only drives
them synchronously from a fresh drain (`12203`). Test code calls the Function
step directly on a synthetic frame; that is a real private helper call, not
evidence of a source-generated nonterminal suspension route.

The scoped safety premise for the next gate is: before mutating an existing
nonterminal frame or running its next side effect, all entries in
`replay_acks[prepared_acks..len]` have applicable current-route completion undo,
and frame rollback ownership has been prepared. The counters must satisfy
`completed_acks <= prepared_acks <= len`; append additionally requires
`prepared_acks == len`. This is a proposed source-integration obligation under
§6, not a premise already enforced for retained nonterminal re-entry.

## Typed-drain transition inventory

Locators refer to `crates/yu-solver/src/` at the pinned baseline. Table entries
include allocation/replacement and whole-frame restoration, which also mutate
the listed fields.

| Owner / locator | Frame mutation | Preparation and reachability |
|---|---|---|
| `candidate_context.rs:1714` `begin_typed_drain` | Push frame; `current=None`, `function=None`, `stage=Transport`; empty acks, both cursors zero, `terminal_prepared=false` | Stack capacity reserved first. One production creator: `lib.rs:11888`. New frame is removed on failure or truncated by route rollback. |
| `candidate_context.rs:1727` `prepare_typed_drain_update` | Replace entire frame with equivalent state and copied ack vector; move original allocation into undo | Fallibly reserve undo and replacement ack allocation first. Saves at most one frame per index in active undo. Only baseline production caller is the terminal step. |
| `lib.rs:11912` loop header | Clear `current`, `function`, `context_consumed`; store transitions; `stage=Transport` | No frame undo/prefix preflight here; safe present use begins a new synchronous drain. This would overwrite a retained interrupted item/Function state if naively reused. |
| `lib.rs:11928` pre-pop owner | Grow `replay_acks` capacity | Reserve one ack slot and call `prepare_replay_child_completion` for the **new front item** before pop; event sample precedes completion-reservation failure if capacity grew. Does not prepare previously retained acks. |
| `lib.rs:11951` popped owner | `current=Some(item)`; append item ack; increment `prepared_acks` | `current` retains original item including ack; local item loses ack after transfer. `debug_assert_eq!(prepared_acks,len)` assumes all earlier entries prepared. `completed_acks` remains unchanged. |
| `lib.rs:11978` transport completion | Replace current relation; `stage=Context` | Real transport may mutate evidence before this assignment. No nonterminal frame journal here. |
| `lib.rs:11986` context completion | Store `context_consumed`; `stage=Dispatch` | `candidate_context_execute` has already run. No retained-state preflight. |
| `lib.rs:12200` Function initialization | `function=Some(children,next=0,pending=None)`; `stage=FunctionAdmission` | Parent memo/diagnostic edges already admitted. Production immediately invokes synchronous Function driver. |
| `lib.rs:12351` Function step | Admission: retain `pending` relation; `stage=FunctionEnqueue`. Enqueue: clear pending, increment next, `stage=FunctionAdmission` | Admission calls `candidate_function_port_admit` before storing pending. Enqueue calls `enqueue_item` before advancing cursor. No frame update or ack-prefix preflight; direct synthetic test caller exists. |
| `lib.rs:12227`, `12258` | Clear current/function; store transitions; `stage=Diagnostics`, then `Acknowledgements` after successful diagnostics | Diagnostic helpers and witness replay occur between these stages. Existing synchronous path only. |
| `lib.rs:12289` terminal step | Prepare frame undo once; prepare next missing ack; increment `prepared_acks`; set `terminal_prepared=transactional`; complete next ack, increment `completed_acks`; set `ReturnReady` when all done | Validates topmost frame, stage, and cursor bounds. Prepares one outstanding ack per step when `completed==prepared`. Reuses prior pre-pop undo. Sampling of new retained storage occurs before completion/removal. |
| `lib.rs:12338`, `12265` | Pop whole frame | Terminal pop restores previous processing pair/relation. Error pop belongs only to the newly created synchronous drain; outer wrapper also restores processing. |
| `candidate_context.rs:1674` commit | Every retained frame: `prepared_acks=completed_acks`, `terminal_prepared=false`; discard frame undo | Called by route transaction success at `lib.rs:9186`. Preparation is route-owned and is deliberately released at commit, including retained ancestor frames. Ack vector/current/stage/function/completed cursor remain. |
| `candidate_context.rs:1569` rollback | Restore old whole frames in reverse undo order, reinsert removed old top frame if needed, truncate frames created after checkpoint | Restores original ack allocation/capacity as well as all frame fields. Entries for newly created frames are skipped; checkpoint length truncation owns them. |

The only direct test mutations of these fields are the synthetic Function
fixture (`candidate_context_tests.rs:3968–3971`), terminal fixture (`4332–4338`),
and manually modeled pre-pop preparation cursor (`4492–4494`). All other test
matches found for these fields are reads/assertions. No other production writer
of `typed_drains` was found in `crates/yu-solver`.

## Replay operation and undo inventory

| Owner / locator in `candidate_context.rs` | Replay mutation or completion | Undo/removal condition |
|---|---|---|
| `candidate_context_begin_replay:2862–2935` | Generate exact children; record generation heads; insert operation with `queued=consumed=0`, `retired=false`, no restoration | Reserve map/ID and child storage; generation evidence and child consumption are distinct. Children allocation moves from scratch to retained owner. New operation frontier is removed by rollback. |
| `prepare_replay_ack:1816` | Append snapshot `(id,queued,consumed,retired)` | Transactional calls reserve/push one undo record each; there is no deduplication by ID. Nontransactional call still checks owner existence. |
| `transfer_replay_child:1823` | Increment `queued` only when `ack.index==queued` | Validate nonretired operation, child bounds and `consumed<=index<=queued`; prepare before increment. Already queued initial items cause no second transfer. |
| `prepare_replay_child_completion:1844` | Validate `consumed<=ack.index<queued`; append undo via `prepare_replay_ack` | Can preflight later child indices without consuming earlier children. It does not require `index==consumed` and does not prove ack-list order. Test failure injection occurs before undo reservation. |
| `complete_replay_child:1860` / `acknowledge_replay:1837` | Require `consumed==ack.index`, increment consumed, mark retired at final child | Caller owns prior reservation. Transactional retirement retains operation until commit; nontransactional retirement still honors active restoration pointer. |
| `candidate_context_consume_replay_child:2939` | `Some(provenance)` enters fresh synchronous drain; `None` queues item. Empty/already-consumed batch prepares and acknowledges directly | With provenance require `queued==consumed`. If all queued but some unconsumed, return false without acknowledgement. Terminal completion of a drain owns those queued children's consumed cursor. |
| `candidate_context_replay_impl:2818` | Test-only compatibility closure loop increments queued then acknowledges | Each iteration calls prepare first. No production caller; closure-based harness is not retained child ownership evidence. |
| `set_restoration_replay:1786` | Link replay to restoration and restoration to replay | Replay backlink is attached to a newly created replay; restoration caller prepares its own undo first. Backlink is not in replay cursor undo; new replay is removed on rollback. |
| `advance_restoration:1790` | Take active replay pointer, increment opposite cursor | Prepared restoration undo. Nontransactional advance can reclaim replay; transactional reclamation waits for commit. |
| `retire_restoration:1798` | Mark restoration retired | Prepared restoration undo. Nontransactional remove immediately; transactional remove at commit. |
| `rollback:1579–1602` | Restore restoration cursors/pointers/retired, then replay cursor/retired snapshots in reverse order; remove operations created after checkpoint | Frame restoration happens first. Operation records still exist because transactional retirement delayed reclamation. New-operation removal follows undo replay. |
| `commit_replay_operations:1684–1712` | Reclaim retired replay candidates, then retired restorations; truncate replay/restoration undo | Visit only new IDs and mutated candidates. Keep retired replay if live restoration still points to it. Examine restorations' final state and old/current replay pointers before reclaiming restorations. Repeated visits to same ID are idempotent. |

`enqueue_item` (`lib.rs:12387`) admits evidence, reserves queue capacity, and
transfers replay queued ownership before infallible insertion. Its drain-front
consumer reserves completion undo before `pop_front`. Production replay driver
callers are physical restoration (`candidate_extrusion.rs:708`, provenance
present) and ordinary bound replay (`780`, provenance absent). Restoration
prepares its journal before driving replay and advances only after the
synchronous child driver returns successfully (`687–711`). The local-use parent
calls this owner step (`candidate_scheme.rs:1471`).

### Repeated IDs and exact rollback order

Two valid acks `(R,0),(R,1)` in one frame are two ordered child occurrences,
including when their child relations are identical. The terminal fixture
explicitly constructs this case (`candidate_context_tests.rs:4320–4338`).
Preflighting both while `R.queued=2,R.consumed=0` pushes two identical snapshots;
it is legal because completion preparation permits later indices. Completion
then requires consumed 0 for the first and consumed 1 for the second. Reverse
undo restores the same pre-completion state twice. If a later transfer or other
update of R adds another snapshot, reverse traversal unwinds that later state
first. ID equality does not justify skipping acks or replacing cursor-order
checks with deduplication.

Exact baseline context rollback sequence is: support undo; frame undo and
new-frame truncation; restoration undo; replay-operation undo; deletion of new
replay/restoration IDs; evidence/bundle/weight/replay-head/discharge/context/
relation/dependency/bound/origin/processing/edge restoration. Outer route
rollback first restores the store, calls intrusion rollback
(`lib.rs:9345` → `candidate_intrusion.rs:104` → `candidate_effect.rs:182` →
context rollback), restores source/local publication state and other journaled
route state, then clears worklist/diagnostic scratch (`lib.rs:9637`). This order
must remain distinguishable from successful commit's reclamation order.

## Earliest safe seam and uncovered bypasses

The first safe resumed-frame seam is entry into a retained nonterminal driver,
after obtaining its index/topmost ownership and active route, **before**:

1. the loop-header frame reset (`lib.rs:11912`);
2. task scope and empty-worklist intrusion settlement (`11920`);
3. front-item ack capacity growth/reservation (`11928`), pop (`11944`), and
   append (`11957`);
4. transport (`11975`), context execution (`11983`), typed dispatch beginning
   `11994`, diagnostics (`12233`), or Function admission/enqueue (`12351`).

A helper covering the nonterminal driver alone leaves the direct Function-step
entry exposed. That step must itself prepare/validate the prefix, or its callers
must be restricted to a source-enforced already-prepared route; a test adapter's
promise does not enforce the production seam. The terminal step is a separate
owner and already prepares its next ack. The pre-pop owner is responsible for
the new item only; it cannot stand in for full prefix preparation. Re-entering
the synchronous constructor also cannot stand in for resume: it makes another
frame, seeds/enqueues initial work, and clears interrupted state.

Smallest conditional append failure: retain one incomplete ack `(A,0)` across
commit, yielding `completed=prepared=0,len=1`; resume incorrectly prepares only
a new front item `(B,0)` and then uses the baseline append code. The debug
assertion fails immediately. Without the assertion, append yields
`prepared=1,len=2`, although undo covers B rather than the prefix entry A.
Terminal completion can then trust the false scalar prefix and consume A
without applicable current-route replay undo. This trace is conditional on an
incorrect future retained-frame entry; the baseline constructor does not reach
it. A single unprepared retained ack is already sufficient to expose the append
premise; two pending acks are needed to discriminate full-prefix preparation
from preparing only the first.

One separate future-resume omission is concrete: `TypedDrainFrame` does not own
the remaining worklist. The session owns it; route begin requires it empty
(`lib.rs:8970`) and rollback clears it (`9637`) rather than restoring a prior
queue. Likewise route begin expects empty diagnostic scratch (`8971`). An
empty-queue synthetic adapter can test ack prefix ordering without violating
these invariants, but it does not demonstrate rollback of a committed nonempty
queue or diagnostic continuation. This is an uncovered continuation ownership
path under §§3/6, outside implementation authority of this audit. It must remain
explicit before claiming general nonterminal suspension.

## Focused proposed test contract

No tests were edited or run. The next implementation test should enter the
actual protected helper/Function seam, rather than independently simulate its
transitions, and state its synthetic reachability:

- Start with a retained nonterminal frame, empty session queue, at least two
  outstanding acks with successive indices for the same R; also cover distinct
  operation IDs. Commit to reset preparation, then resume on another route.
- Inject completion-preflight failure before Function admission and before
  Function enqueue. Verify no relation/dependency/lifecycle-generation advance,
  enqueue, new pop, or append occurs; route rollback restores original frame
  fields, ack allocation, replay cursors, processing, and retained accounting.
- Fail on the second pending preparation to discriminate full prefix from
  first-only preparation. Check partial preparation belongs to the active
  journal and rollback restores it. The baseline boolean failure hook fails the
  next completion reservation only; targeting a later reservation needs an
  explicitly authorized test mechanism or an invalid later-ack fixture with
  its narrower coverage stated.
- After successful preflight, append another ack through the real owner; assert
  `prepared==len`, complete original occurrences in order, and fail later so
  reverse undo covers all cursor changes. Repeated preparation in one route
  must not duplicate already-prepared completion undo; commit must release that
  preparation and the next route must reacquire it.
- Cover already-completed prefix, zero outstanding acks, both Function stages,
  and cold frame/ack/undo allocations with event-time retained-byte sampling
  before any failure or cleanup. Do not require exact cold post-rollback journal
  capacity equality unless that is separately guaranteed.
- Retain terminal tests at `4348`, `4409`, `4458`, queued-child rollback tests
  around `1640`, and restoration-pointer rollback around `1740` as distinct
  existing contracts. Synthetic terminal and Function fixtures do not prove
  source suspension, exact recognizer authorization, or §7 lifecycle coverage.

Oracle independence: source inspection grounds ownership; the authoritative
contract grounds required ordering. The proposed test uses actual source
helpers and exact pre/post state, while sharing the compiler's constructed
synthetic operation/frame assumptions. A hand-coded transition model would
only check that model. Source-generated nonterminal suspension, external
incidence changes, diagnostics restart, withdrawal/recomputation, and production
certificates remain unverified. No seeds/ranges, mutations, timing samples, or
enumeration were used.

## Commands, resources, and dependencies

Checks performed: bounded `rg` inventories across `crates/yu-solver/src/*.rs`,
`sed`/`cat` reads of the owners, direct callers, typed-drain fixtures, governing
contract and previous terminal note; `sha256sum` for the following dependency
snapshot. All reads/hash commands completed successfully. A startup read-only
`git rev-parse HEAD` reported the primary-pinned SHA; no Git mutation occurred.
No build, test, formatter, executable probe, or broad repository scan ran.
One worker, sequential lightweight shell inspection; CPU/RSS and exact elapsed
time were not measured. Assignment wall-time ceiling: 25 minutes.

| Dependency | SHA-256 inspected |
|---|---|
| `candidate_context.rs` | `24909fb9a09e6f9d383e5b1f8f4f8db9d5f7e587a1ed5bbb6a47ead77e140831` |
| `lib.rs` | `77a3c4bdb48d438f7e5678c35302ad2aa1f6665ca9cbb8f3fdc0a48e730a30f4` |
| `candidate_context_tests.rs` | `3a63e52796fcc568e50f59462691ccde77acac5a0bcc0d02d550402811e31ba3` |
| `candidate_extrusion.rs` | `08e3121924696232bdc75b1eaa3110e2fdc008b948d1c58f6758965b25e0d85d` |
| `candidate_scheme.rs` | `ad3208eea2b348f1e87f1c6958b1d13b2d625ba38a42f5eac22959edd371a825` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |

Recommended next action: implement the authorized prefix helper at the retained
nonterminal/Function entry boundary with a focused synthetic rollback test;
record remaining queue and diagnostic ownership separately before source
suspension integration. Production and §7 authorization stay open.

## Commit packet

- Exact lease/change: `notes/progress/2026-10-11-nonterminal-ack-prefix-source-audit.md`.
- Baseline: `6a962826ab46d7f58529f7162aa016997ed5418d`.
- Dependency changes: none authored; hashes above identify inspected inputs.
  Primary must revalidate them against its frozen implementation snapshot.
- Claim/review status: research-only static ownership characterization and
  conditional failure trace; unreviewed, not independent certification.
- Checks already run: source/caller/mutation inventories and dependency hashes;
  no runtime checks.
- Proposed commit message: `research: audit nonterminal acknowledgement prefix ownership`.
- Shared-record deltas intentionally left to primary/curator: record the absence
  of a real nonterminal resume entry; bind prefix preparation to all exposed
  nonterminal/Function seams; retain worklist/diagnostic rollback ownership and
  authentic §7 source reachability as open. No task/index/authority edit made.

Artifact frozen for primary review; this worker will make no further writes.
