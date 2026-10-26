# Original drain frontier after an active cut

Date: 2026-10-27. Producer: `/root/principality`, bounded `lean_prover` leaf.
Status: **checked initialized polling invariant and first post-active
settlement boundary; native extraction and full NQ remain OPEN**.
Independent review: not yet performed. No compiler, original transition
function or frozen proof was modified.

## 1. Result and the initialization trap

[OriginalDrainFrontier.lean](lean/YulangClosure/OriginalDrainFrontier.lean)
constructs the missing bridge from an **initialized active cut tau** to the
first later empty boundary of that same drain owner. It derives the polling
invariant from the existing executable updates and initializes the frozen
first-boundary argument at tau, rather than at fresh-frame initialization.

This distinction is necessary. The original `.begin` event creates a
Transport frame with `current = none`, an empty queue and `poll = entry`.
That frame exists before the seed enqueue. Therefore
`OriginalFirstDrainBoundary.initialized_first_settlement` can select an
initialization cut earlier than the active NQ cut. It does not by itself
identify NQ's first boundary **after tau**.

The new theorem returns a **nonempty** event prefix beginning at the supplied
active tau, the first same-owner EmptyBoundary along that prefix, the derived
entry poll counter, and the exact successful settlement-entry result. Its
existence premise is only the stated candidate finite successful suffix
ending at that owner's boundary. It proves neither existence of such a suffix
nor termination of the drain.

## 2. Original target and source correspondence

The owner is [NQ §§3–5.2](2026-10-26-native-copy-quiescence-obstruction.md),
particularly the concrete tau immediately before the body of
`dispatch_live_item` at observer event **1229**. The NQ boundary is the same
active drain's Transport/current-none/empty-worklist cut immediately before
the conditional call to `settle_candidate_intrusion`.

The current native definitions were read directly:

| Native owner | Relevant actual behavior |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs::begin_typed_drain` | Initializes Transport and no current item before later seed enqueue. |
| `crates/yu-solver/src/lib.rs::step_typed_drain`, Transport/current-none arm | Tests empty worklist before settlement, then performs the worklist pop. The later pop either installs a current item or may enter Diagnostics if clean. |
| The same function's Dispatch arm | Requires `current.ok_or(...)` before calling `dispatch_live_item`; after a successful dispatch it clears current only when all four retained structural continuations are empty. |

The frozen [stage projection](lean/YulangClosure/OriginalDrainStages.lean)
already represents all fourteen native stages and the separate `Poll`
control positions around settlement. Its errors and suspension guards remain
unchanged. The new module imports that implementation through
[OriginalFirstDrainBoundary](lean/YulangClosure/OriginalFirstDrainBoundary.lean).

The new Dispatch corollary matches NQ's stated control location: initialized
stage validity derives a nonempty current slot from an actual Dispatch-stage
readback. Extracting observer event 1229 and its native prefix into those
specific model inputs remains a separate obligation. No `C.Run` or complete
Rust trace correspondence is assumed as a conclusion of this packet.

## 3. Polling invariant derived from computed updates

The frame invariant is exactly:

```lean
def FramePoll (frame : Frame) : Prop :=
  frame.poll = .entry ∨
    (frame.stage = .transport ∧ frame.core.current = none)

def Polls (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, FramePoll frame
```

It says that a nonentry poll counter can occur only on an idle Transport
frame. It is not an extra executable guard or a caller-supplied law.

`update_returns_entry` proves a stronger local result: every successful
computed `update` starting from this invariant returns a frame at entry. If
the input is already entry, the frozen full-stage preservation theorem
applies. Otherwise the invariant selects the **actual Transport/current-none
branch**, and both actual queue-pop outcomes reset entry. No assumed summary
of structural dispatch, completion or settlement supplies this fact.

The preservation proof then covers every original Event constructor:

| Event | Derived preservation |
| --- | --- |
| `begin` | The new frame is entry; all prior frames are retained. |
| `reserveBirth`, `enqueue`, `bookkeeping` | These constructors leave frame polling fields unchanged. The complete queue/bookkeeping updates remain present. |
| `advance` | Its actual guards and successful `update` yield entry; a returned frame is popped and its existing tail remains valid. |
| `settle` | The actual guard supplies Transport and current-none, so setting `poll = settling` establishes the idle alternative directly. |
| `settled` | Its required `poll = settling` excludes the entry alternative of the previously derived invariant. Hence the frame is idle, and changing the counter to returned preserves that fact. |
| `prepare` | Only the original preparation count changes; poll, stage and current remain unchanged. |

`apply_polls` is induction over those computed event cases. `execute_polls`
iterates it over the actual finite list, and `initialized_polls` supplies the
invariant from the empty initial stack. Failed computations are not silently
converted into successful steps. None of these proofs invokes another state
machine or an assumed transition-preservation certificate.

## 4. Deriving entry at the actual active owner

For any frame present in an initialized execution,
`initialized_active_entry` derives `frame.poll = entry` from the raw condition
`frame.core.current ≠ none`. The idle alternative of FramePoll contradicts
that condition.

For a supplied actual top frame, `initialized_active_entry_only` derives the
frozen `First.EntryOnly frame.owner state.frames`. It obtains `Valid` from
the initialized execution, then uses `same_top_is_saved_frame`: a member
with the same owner cannot be a different suspended frame at another index.
The owner retains **both ghost birth and actual frame index**. No index-only
identification or assumption of unique owners is supplied by the caller.

`initialized_active_not_boundary` separately proves that tau cannot already
be the target EmptyBoundary. Its current slot is nonempty. This fact is used
to prove the returned event prefix is nonempty, rather than relying on the
name of a first-boundary predicate.

The main theorem's complete parameter and conclusion shape is:

```lean
initialized_active_first_settlement
    {history events : List Event} {tau last : State}
    {activeFrame : Frame} {activeTail : List Frame}
    (initialized : execute history initial = .ok tau)
    (activeTop : tau.frames = activeFrame :: activeTail)
    (activeCurrent : activeFrame.core.current ≠ none)
    (candidate : execute events tau = .ok last)
    (ends : EmptyBoundary activeFrame.owner last.project) :
  ∃ earlier later cut frame rest,
    events = earlier ++ later ∧ earlier ≠ [] ∧
    execute earlier tau = .ok cut ∧
    First.BeforeFirst activeFrame.owner tau cut ∧
    EmptyBoundary activeFrame.owner cut.project ∧
    cut.frames = frame :: rest ∧ frame.owner = activeFrame.owner ∧
    frame.core.index = rest.length ∧ frame.stage = .transport ∧
    frame.core.current = none ∧ cut.queue = [] ∧ frame.poll = .entry ∧
    apply (.settle activeFrame.owner) cut =
      .ok {cut with frames := {frame with poll := .settling} :: rest}
```

The proof calls `First.finite_first_boundary` on **`execute events tau`**.
It transports the derived owner EntryOnly and initialized Valid along that
prefix using `First.before_entry` and `First.before_valid`. The frozen
`projected_empty_boundary_iff` then supplies the exact stage/current/queue
fields, and `boundary_enters_settlement` computes the final successful step.

There is no caller premise `Valid`, `EntryOnly`, FramePoll, final-frame poll
entry, completed drain or global termination. The conditional final-boundary
premise is the candidate boundary being analyzed; the theorem does not create
one or assert that it is reachable in the original NQ execution.

## 5. Direct Dispatch-cut application and the current-none limit

`initialized_dispatch_current` derives `current ≠ none` from initialized
stage Shape plus the supplied actual `frame.stage = dispatch` readback.
`initialized_dispatch_first_settlement` applies the main result using that
derived fact. Thus the direct NQ-shaped application has these inputs only:

1. the computed initialized prefix ending at tau;
2. its actual top frame;
3. that frame's Dispatch-stage readback;
4. the candidate successful finite suffix and same-owner ending boundary.

If a proposed tau has **no current item** and no Dispatch-stage witness,
the new invariant alone cannot derive entry. It permits both `settling` and
`returned` while the frame remains Transport/current-none. A different
control cut therefore needs an authentic program-counter/entry supplier and,
for a strictly later first boundary, proof that the cut is not already that
owner's EmptyBoundary. Merely knowing Transport/current-none/empty does not
supply the missing program-counter fact. No application to such a cut is
advertised here.

## 6. Exact NQ and native extraction boundary

The result concerns the **same owner's** first post-tau boundary. BeforeFirst
therefore excludes an earlier successful settlement entry for that owner:
the frozen `settlement_starts_at_boundary` theorem would contradict its
pre-boundary condition. Nested frames and events for other owners are still
allowed by the executable model.

Consequently this packet does not by itself establish NQ §5.1's broader
absence of any intervening settlement or representative/generation change.
The ordinary-route extraction must still exclude the inappropriate nested
restoration/settlement histories where the original source argument excludes
them. Keeping another owner's events admissible in the local stage theorem
does not prove that NQ's native continuation executes them, or that its
generation is unchanged.

The remaining owners must also supply:

- extraction of the actual native initialization, seed enqueue, tau frame and
  successful event/readback prefix, including the genuine birth/index mapping;
- correspondence of the complete shared Value/Effect queue and stage events
  to Rust calls, including all fallible guards and nested-return points;
- the separate prior-work, replay/fiber, memo and successor-production facts
  required for NQ's contradiction at a candidate first boundary.

No Work item or Effect port is removed by this proof, no error becomes a
normal return, and no finite run or final bound existence is asserted beyond
the supplied candidate. Full `SourceProblem.InferenceTermination`, the full
native NQ proposition, source soundness, Effect hygiene and principality are
not discharged here.

## 7. Verification and frozen receipt

Frozen source:
`ec7d4ab463858b73cd09295588833fa095a749c529d40a03cd4f5b8406fb9682`.
The first direct check exits 0 with no warnings or errors. It used pinned Lean
4.35.0, `timeout 120`, `LEAN_NUM_THREADS=1`, `-j1 -M1024`, without `-o`.
No failed checker run occurred in this packet; `check-01.log` is retained.

The parent built this exact frozen source successfully: six jobs, no
diagnostics, receipt `/tmp/yulang-drain-frontier-build.log`. The subsequent
full originating-module census also exits 0. It uses the same pinned
checker with `-j1 -M2048` and no output object file. The audit prints the
complete type and transitive axioms of **all 33 originating declarations**,
including generated/private constants: seven definitions and 26 theorem
constants, of which 16 are authored and ten generated. No diagnostics,
ellipses, `sorryAx` or unapproved axioms occur.

All 16 authored theorems have these exact transitive axiom sets:

| Axiom set | Authored theorems |
| --- | --- |
| None | `fresh_poll`, `initial_polls`, `nonentry_idle`, `tail_polls` |
| `propext` | `replace_polls` |
| `propext`, `Quot.sound` | `update_returns_entry`, `advanced_polls`, `apply_polls`, `execute_polls`, `initialized_polls`, `initialized_active_entry`, `initialized_active_not_boundary`, `initialized_dispatch_current` |
| `propext`, `Classical.choice`, `Quot.sound` | `initialized_active_entry_only`, `initialized_active_first_settlement`, `initialized_dispatch_first_settlement` |

Every generated declaration was also audited. The union over all originating
declarations is exactly the three approved logical axioms above; there is no
new project axiom or assumed semantic preservation law.

| Retained audit artifact | SHA-256 |
| --- | --- |
| `/tmp/yulang-drain-frontier/AuditFull.lean` | `c025158014023992823ca4af35ed7fe669b7c87d6f7fd011acc3a34358443bfa` |
| `/tmp/yulang-drain-frontier/audit-01.log` | `5600966816c8a52704714e0055ef3f114728a114fc132ba7d6bcf07f06f87f8e` |
| `/tmp/yulang-drain-frontier/census.json` | `89429013f47f22ef920987f548d32a7b99916829b44f71390c7d14be1bf5db3b` |

Used budget: **one of 18 proof invocations and one of two all-origin audit
invocations**. All checker processes have exited. The source remains frozen
at the hash above; the paired note is frozen at final handoff.

Read-only owner hashes:

| Path relative to the repository | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalDrainStages.lean` | `9e116f95b8ed001485b2f6b699478c847a53420adb11c70b577b1c0f4e07d61d` |
| `notes/theory/lean/YulangClosure/OriginalFirstDrainBoundary.lean` | `d2c7096ff19b072fea0646b2ed12a4096e26ee03b31eb71997c64e9af43f0a1a` |
| `notes/theory/lean/YulangClosure/OriginalDrainBoundary.lean` | `d11f5c4e5550702c0796c45076408b0c038e4bc204ec05354b83db8ad7b04ab9` |
| `notes/theory/2026-10-26-native-copy-quiescence-obstruction.md` | `fc2676a6881ac662b2926b2f39223112dbd832e4fb44feca6e212422bbe33d75` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |

The only repository writes are this note and its paired Lean module. All
dependency builds, Git operations and shared records remain parent-owned.
