# First empty field boundary: derived settlement program counter

## Scope and original obligation

This module derives the settlement-entry program counter at the first empty
field boundary of an initialized fourteen-stage event execution. It supplies
a necessary control lemma for NQ §§4–5 in
[`2026-10-26-native-copy-quiescence-obstruction.md`](2026-10-26-native-copy-quiescence-obstruction.md).
It does not establish the native NQ proposition or original inference
accessibility. All four whole-language roots remain OPEN.

The Lean module is `YulangClosure.OriginalFirstDrainBoundary`; the source is
`lean/YulangClosure/OriginalFirstDrainBoundary.lean`. Its SHA-256 is
`d2c7096ff19b072fea0646b2ed12a4096e26ee03b31eb71997c64e9af43f0a1a`.
It contains 13 authored theorems. It imports the frozen computed stage
machine and changes none of its definitions or events.

The actual native `step_typed_drain` at `lib.rs` 14289–14420 enters settlement
only in Transport with no current item and an empty worklist, before trying
to pop another item. `begin_typed_drain` at `candidate_context.rs` 2249
initializes Transport and no current item. The source pins are:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| Original NQ note | `fc2676a6881ac662b2926b2f39223112dbd832e4fb44feca6e212422bbe33d75` |
| `OriginalDrainBoundary.lean` | `d11f5c4e5550702c0796c45076408b0c038e4bc204ec05354b83db8ad7b04ab9` |
| `OriginalDrainStages.lean` | `9e116f95b8ed001485b2f6b699478c847a53420adb11c70b577b1c0f4e07d61d` |

## Why the earlier stage invariant is insufficient

`OriginalDrainBoundary.EmptyBoundary` identifies the actual top owner by
birth and index, a working phase, absent current and an empty queue.
`OriginalDrainStages` derives Transport from those fields, but the predicate
also holds while the same frame's `Poll` is `settling` or `returned` if no
queue entry has appeared. A final-frame `poll = entry` premise would leave
the before-settlement timing unproved.

`EntryOnly owner frames` states that every retained frame with that exact
birth/index owner still has `Poll.entry`. It is initially true because the
frame stack is empty. It is a derived invariant strictly before that owner's
first empty field cut, not a field of an input certificate.

`structural_entry` covers all four structural families and every exhaustion,
pending, admission and enqueue branch. `update_entry` covers all fourteen
stages. `advanced_entry` also covers the terminal pop. `apply_entry` then
covers every existing event constructor:

- Begin creates an entry frame; birth reservation, enqueue and bookkeeping
  preserve the existing stack; preparation preserves its poll.
- A successful computed advance preserves entry for the retained owner or
  removes a frame. It cannot introduce a nonentry poll for that owner.
- Settlement of this owner would require an empty boundary in the before
  state, contradicting the strict-before hypothesis. Settlement of another
  owner retains the tracked frames.
- Settlement return of this owner would require a settling poll, contradicting
  the already-derived entry property. Other owners remain permitted.

Neither the statement nor the proof excludes nested frames or conflates
later reuse of a vector index with this owner's identity.

## Executed prefixes and the constructed first cut

`BeforeFirst owner first last` is the finite snoc closure of the existing
computed `apply` operation, recording that every before-state lacks that
owner's empty boundary. It supplies neither a final boundary nor future
termination. `before_entry` propagates the entry property and `before_valid`
propagates the stage machine's derived field/stack validity.

`finite_first_boundary` starts with an actual successful `execute events
start` and an empty boundary at its endpoint. By induction on that same
event list it constructs a decomposition `events = earlier ++ later`, a
computed execution of `earlier`, a `BeforeFirst` derivation for that prefix,
and the empty cut. It does not invent an execution or assume a caller-picked
prefix already has the firstness property.

The main settlement lemma has this complete application type (inside the
module's namespace with the original stage and boundary names open):

```lean
theorem first_empty_enters_settlement {owner : Owner} {last : State}
    (run : BeforeFirst owner initial last)
    (boundary : EmptyBoundary owner last.project) :
    ∃ frame rest,
      last.frames = frame :: rest ∧ frame.owner = owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ last.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle owner) last =
        .ok {last with frames := {frame with poll := .settling} :: rest}
```

`initialized_first_settlement` combines this result with the constructed
first prefix of a supplied initialized execution. Its premises are only
the actual execution equality and the candidate final empty boundary. The
conclusion retains the original list decomposition, prefix execution,
firstness derivation, same owner, actual stack slot, Transport/current/queue
fields, derived entry poll and exact computed settlement result.

This is a conditional control theorem: it proves where settlement can enter
if the supplied finite execution reaches such a boundary. It is not an
existence or termination theorem for the complete inference computation.

## Initialization versus the native active cut

There is a material application boundary. The projected `.begin` event
creates a Transport/None frame while the queue is still empty; enqueueing
the initial seed is a separate event. Thus the first empty **field** boundary
from global initialization can occur before native `start_typed_drain` has
returned to the polling loop. This module does not identify that intermediate
initialization cut with NQ's first active polling boundary after tau.

For the original NQ application, the later active cut must supply its entry
frontier from the actual initialized event history, then apply the first-cut
construction to the suffix after that cut. The existing `before_entry` and
`before_valid` already support arbitrary initial states, but they do not
themselves supply that active-cut invariant. Its construction is assigned to
the separate `OriginalDrainFrontier` packet; no theorem from that unfinished
packet is assumed here.

Authentic Rust event extraction, matching the event cut to the native next
instruction, the same Replay/physical-store history, source tau extraction,
normal/error/rollback separation and the NQ successor argument remain open.
Arbitrary successful readback events do not prove a `NativeDrainOwnership.Run`.
No language restriction, semantic change, finite identity cap or global fuel
argument is introduced.

## Actual verification

The pinned environment is Lean 4.35.0, Lake 5.0.0-src+eb6cafb, no external
packages. Direct checks used the exact task-local Lake, `timeout 120`,
`env lean -j1 -M1024`, without `-o`. Six of the allocated twelve proof checks
were used:

| Check | Actual outcome |
| --- | --- |
| 1 | Base entry helpers accepted; one unused simp argument warning retained. |
| 2 | Actual errors in preparation-head inference, reserved binder syntax and the downstream unfinished derivations. |
| 3 | Preparation-head inference remained a real error. |
| 4 | Complete first-entry proof accepted, empty diagnostics. |
| 5 | Added original-list first-cut construction; nil-case substitution exposed an unavailable local name. |
| 6 | Final complete source accepted, exit 0, empty diagnostics. |

Logs are `/tmp/yulang-first-drain-boundary-01.log` through `-06.log`.
The real focused import build completed successfully, **5 jobs, zero
warnings/errors**, in `/tmp/yulang-first-drain-boundary-build.log`.

`lean/AuditOriginalFirstDrainBoundary.lean` selects declarations by their
actual module origin and requires all 13 authored roots to be theorem
constants. The first full-origin audit used the same 1 GiB/120-second bounds
and exited 0. It printed complete types and transitive axiom lists for
**all 57 originating declarations, including 35 theorem constants**. There
are 57 matching begin/end records, no elided types and no extra axiom.
The log `/tmp/yulang-first-drain-boundary-audit-01.log` has SHA-256
`2d0a211e1fc135f47dd6f7b43966351e16efef29e4b38f9322b2fc773b8eb7c5`.

The authored axiom inventory is exact:

| Dependencies | Authored declarations |
| --- | --- |
| None | `initial_entry`, `tail_entry` |
| `propext` | `structural_entry`, `replace_entry`, `before_trans` |
| `propext`, `Quot.sound` | `update_entry`, `advanced_entry`, `apply_entry`, `before_entry`, `before_valid`, `first_empty_enters_settlement` |
| `propext`, `Classical.choice`, `Quot.sound` | `finite_first_boundary`, `initialized_first_settlement` |

No `sorry`, `admit`, project axiom, `native_decide`, kernel bypass or assumed
semantic preservation law occurs. Independent review and default integration
are recorded in the separate review receipt and parent ledger.
