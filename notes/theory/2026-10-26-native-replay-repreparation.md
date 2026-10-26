# Native retained-acknowledgement re-preparation

Date: 2026-10-26. Status: kernel-checked constructive delta; independent delta
review pending. Accepted baseline: `9fe10fd65bc8eac14ac1a9ef0560ea11c36756b1`.

## 1. Exact change and unchanged parent

This delta extends `YulangClosure.NativeReplayAcknowledgement` to represent
the retained-acknowledgement loop in `prepare_nonterminal_drain`. It constructs
the exact native cursor guard, computes the successful suffix prefix, and
proves finite completion **or the exact first guard failure**. The result
preserves all other frame fields, remains reachable and accounted, and applies
after commit in both working and Diagnostics stages.

The accepted predecessor paper, handoff and review remain byte-preserved. Its
review explicitly left nonterminal re-preparation as a concrete OPEN readback
case; this delta addresses that case without changing the old terminal
preflight. All 35 earlier authored theorem statements remain unchanged. Their
proofs are rechecked over the extended transition relation.

The unchanged original parent is `SourceProblem.InferenceSoundness`
(`Contracts.lean:128`), over every supported original source, scope, generated
constraint and successful solution with the SAME scoped witness. Full shared
native-map authentication, original record boundary `j`, full Call, contextual
meaning, semantic child closure and `MERGE-EXPANSION-COVER-1` remain OPEN.

## 2. Actual native loop and the necessary distinction

`lib.rs:14261–14288` first checks that the frame exists and is the top frame,
and that `completed_acks ≤ prepared_acks ≤ replay_acks.len()`. It prepares the
frame undo record, then repeats:

```text
while prepared_acks < replay_acks.len():
    ack := replay_acks[prepared_acks]
    prepare_replay_child_completion(ack)?
    prepared_acks += 1
```

The helper has **no stage test**. `step_typed_drain` calls it for every stage
other than Acknowledgements and ReturnReady (`:14290–14300`), including
Diagnostics. The Function, Tuple, Record and Variant dispatch helpers also
call it (`:14955–15035`). Repeated calls with a fully prepared vector have an
empty suffix and perform no acknowledgement-preparation iteration.

This differs from terminal preflight (`:14881–14947`), which selects
`replay_acks[completed_acks]` only when `completed_acks == prepared_acks`.
The accepted `FrameStep.preflight` keeps that exact definition. A new
stage-free `FrameStep.reprepare` reads the **prepared** index instead. Merely
relaxing the old stage check would still select the wrong index and would
incorrectly exclude the second iteration after `prepared` advances.

The new frame constructor carries presence, top-frame identity,
`completed ≤ prepared`, `prepared < acks.length`, and the exact indexed ack
readback. Its event is `FrameEvent.reprepare oldPrepared ack`; its only frame
write is `prepared := prepared+1`. In particular, it preserves stage,
`terminalPrepared`, `completed`, the acknowledged prefix, destination,
transition count and all other frame fields. The constructor describes the
helper body; the caller's stage qualification remains a source-call fact.

Commit resets `prepared_acks := completed_acks` and
`terminal_prepared := false` (`candidate_context.rs:2212–2216`). The new loop
restores the prepared frontier. It does not acknowledge children or establish
semantic completion.

## 3. Independently stated native cursor guard

All new definitions and theorem names in this section have prefix
`YulangClosure.NativeReplayAcknowledgement.Repreparation`.

`prepareGuard : Option NativeState → Ack → Bool` transcribes
`prepare_replay_child_completion` (`candidate_context.rs:2405–2427`):

- a missing operation fails;
- `consumed ≤ ack.index < queued` is required;
- Idle succeeds after those bounds;
- Running requires the same entire ack and `queued = ack.index+1`;
- Ready fails.

There is no added retired-bit check: the native function does not have one.
`prepareGuard_some_exact` proves this Boolean is equivalent to the independently
stated cursor inequalities and `CompletionWait`. `prepareGuard_readback_exact`
additionally derives presence when checking an existing projection's erased
readback. Machine-number validity remains part of authentic native readback;
the Lean counters are natural numbers. For a genuine native Running readback,
`ack.index < queued` also ensures that the checked increment of that index is
within its native unsigned range.

The owner input to the scan is `Owners := Nat → Option NativeState`.
`guard owners ack` reads exactly `owners ack.operation`. During the native
helper's loop, successful preparation journals the tuple but does not mutate
those native cursor fields. The frame's ack vector also stays fixed during
that loop. Thus one helper invocation can use fixed cursor readbacks while
advancing the frame frontier. Authenticating those readbacks against the
actual shared operation map remains an explicit obligation.

## 4. Computed finite prefix and constructed execution

`scanCount owners xs` recursively checks the head ack and continues only if
its native cursor guard succeeds. `scanSteps owners f` applies it to
`f.acks.drop f.prepared`. `scanFrame owners f` sets only
`prepared := f.prepared + scanSteps owners f`.

The scan receives no supplied valid-ack list or completed-frontier invariant.
Its properties are derived from its definition:

- `scanCount_bound` bounds the successful count by the suffix length.
- `scanCount_prefix` / `scan_successful_prefix` identify every successful
  position and its actual successful native guard.
- `scanCount_finish_or_failure` / `scan_exact_first_failure` return either
  the exhausted vector or the exact next selected ack whose guard is false.
- `scan_complete_exact_steps` identifies a complete scan's successful iteration
  count with the initial deficit `acks.length-prepared`.
- `reprepare_deficit_decreases` proves each successful new frame step reduces
  that deficit by exactly one.

`Trace owners f n g` records the selected successful guards and their actual
`FrameStep.reprepare` writes. `scan_constructs_trace` builds this trace by
induction on the retained suffix, deriving each selected-index bound and
readback. It does not assume the output history. `trace_reachable` feeds the
constructed steps back into the existing `FrameReachable` relation, and the
existing accounting induction derives the output accounting.

The combined root is **`nonterminal_reprepare`**. Its inputs are only the
owner readbacks, a reachable initial frame projection and its presence.
Writing `n := scanSteps owners f` and `g := scanFrame owners f`, it proves:

```text
Trace owners f n g
and FrameReachable index destination g
and FrameAccounting g
and { g with prepared := f.prepared } = f
and n ≤ f.acks.length - f.prepared
and every position before n selects its actual ack and passes its guard
and (g.prepared = f.acks.length
     or the exact next selected ack has a false native guard).
```

The record equality is deliberate: it preserves **every** other frame field,
rather than a selected list of convenient fields. The predecessor accounting
root remains responsible for the exact acknowledged prefix and diagnostics
order. Re-preparation changes neither of them.

`paired_cursor_frame_step` constructs the existing cursor `Step.prepare`
together with the new frame write for the same selected ack.
`paired_owner_lookup_step` exposes the further exact equation
`owners ack.operation = readback cursorProjection`, so the guard checked by
the scan is the one used to build that cursor step. Both resulting accounting
facts are derived from reachable inputs. This is a local pairing; it does not
construct a global mutable owner map or identify independently chosen
projections with an actual native execution.

## 5. Commit, resource failures and the caller application

`committed` transcribes the two frame writes at commit.
`committed_reachable` constructs that transition. `commit_scan_outcome` then
derives a reachable/accounted output whose terminal-preparation bit is false
and whose stage, consumed prefix and completed counter are preserved. The
same computed completion-or-first-guard-failure alternative remains explicit.

In the completion branch, `commit_scan_complete_frame` gives the exact whole
record equation:

```lean
scanFrame owners (committed f) =
  { f with prepared := f.acks.length, terminalPrepared := false }
```

Its successful-frontier equation is the selected conclusion of the scan
alternative, not an assumed initial invariant. `complete_scan_then_append`
applies that result to the subsequent working-stage Transport append and
derives `prepared = acks.length` again after the append. This matches the
assertion before native `replay_acks.push` at `lib.rs:14331–14334`; it does not
claim that the appended work item's native ownership was independently proved.

The checked witnesses construct two retained acks for one Idle operation with
two queued children. They include commit and a two-step scan in both working
and Diagnostics stages. `second_reprepare_uses_prepared_not_completed`
exhibits the decisive intermediate state: `completed=0`, `prepared=1`, and the
selected ack is the second vector entry. A separate missing-owner witness
stops before any prepared-counter write.

**A completed guard scan is not a native `Ok`.** The native helper can fail
while preparing the frame snapshot, reserving a replay undo entry, through
the test failure injection, or during the resource observation after the loop.
The latter can fail after `prepared == acks.length`. Guard failure and storage
failure are different events; this scan computes only the former.

`trace_prefix` constructs every successful prefix of the computed trace.
`resource_stop_prefix` proves that any such prefix—including the full prefix
before a failing final observation—is reachable and accounted, with exact
whole-frame readback except the advanced prepared counter. It does not invent
a successful allocation result, identify which resource event actually
occurred, or prove the global rollback journal. Mapping a real resource-stopped
execution to this prefix is part of the remaining native correspondence.

## 6. Verification, frozen evidence and application boundary

The isolated project is
`/workspace/scratch/f98087c7ac1a/inference-native-replay-repreparation/project/`.
It copies the three unchanged project configurations and imports only pinned
`Std`. The installed Lake reports `5.0.0-src+eb6cafb` with Lean `4.35.0`; Lean
reports `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
All focused invocations use `LEAN_NUM_THREADS=1`, `-j1`, `-M1024` and a
120-second process-group timeout. The known sandbox native self-location
limitation uses the authorized task-bounded escalation. No dependencies,
global toolchain/defaults, SYSROOT, Rust, tests or probes were changed.

`check01.log` preserves a simplifier recursion/guard-unfolding repair and two
lint warnings; `check02.log` preserves an equality-normalization and witness
frame-inference repair. The corresponding exact source snapshots are in
`sources/`. The warnings were removed rather than suppressed.
`check03.log` is the final successful two-job module build, with **zero
warnings**. `audit04.log` is the successful complete originating-module audit,
also with **zero warnings**. Four focused calls were used of ten granted.

The final audit covers **723 originating declarations, 306 theorem constants,
and all 67 authored roots: the 35 earlier roots plus 32 new roots**. It includes
private/generated constants and rejects project axiom declarations and all
axiom dependencies outside the three allowed standard axioms. Every constant
has its full printed type and complete axiom list.

| Actual axiom set | Originating declarations |
| --- | ---: |
| none | 585 |
| `propext` | 72 |
| `propext`, `Quot.sound` | 38 |
| `propext`, `Classical.choice`, `Quot.sound` | 28 |

The complete evidence directory retains `named-roots.txt`, separate
`old-authored-roots.txt` and `new-authored-roots.txt`, all 67 exact named theorem
types/axioms, the 32 new types/axioms, the accepted source snapshot,
`module-delta.diff`, configuration/source hashes, failed and successful logs,
and the all-origin audit program. The entire accepted module text is retained
as an ordered subsequence of the new source: this delta adds the new event,
constructor, preservation case and new section, without editing prior theorem
statements or the terminal preflight. The old paper, handoff, review and
lifecycle paper were rehashed and match their frozen identities.

| Final evidence | SHA-256 |
| --- | --- |
| Extended Lean module | `5264c6b6d9904a43ec0b50c3ac0100a05612b724f52a8601e3a93c771f8204df` |
| `check03.log` | `892032aec1f6cf18f2fd353a5d5324f8b94f1f0cbbacfd8bcafb3e4ff32137d5` |
| `audit04.log` | `31a971b68216fc44a9cca9e4be423bc11e94798d58365dae43b0f0b31dde2523` |
| `manifest.json` | `366bec659fa56a20b8c4f73e3b4495adda40ef1e583171613f0f1c5e5a57ae46` |

The predecessor's concrete nonterminal re-preparation omission is removed at
the projection level. The next owner must still authenticate the selected
frame, owner lookups, cursor preparation tokens, actual worklist and undo
storage against one shared native history. The complete native lifecycle
root, semantic child closure, discharged Effect expansion transport and the
unchanged original source/Call/context obligations are not closed here.
The primary owns independent delta review, integration, status and Git.
