# Native typed-drain frame rollback from first snapshots

Date: 2026-10-26. Status: constructed and kernel checked projection; fresh
independent review pending. Full native-history authentication and original
whole-source inference soundness remain OPEN.

Baseline: `60e8684224a8a911a5627b845312750a192be777`, branch `yulang3`.
Author: `/root/native_frame_r3`, bounded generic `lean_prover` leaf, no children.
Module: `YulangClosure.NativeFrameRollback`; its only import is pinned `Std`.
It does not depend on the concurrent `NativeExecutionHistory.lean` artifact.

## Original obligation and precise reduction

`SourceProblem.InferenceSoundness` in `Contracts.lean:128–130` requires an
original source derivation and the same scoped witness for every successful
generated solution. `NativeCorrespondence`, lines 147–149, separately requires
actual native success to supply generated constraints and a realized solution.
The whole-source obligation includes the original source domain and accepted
semantics; neither proposition is established by this component.

The local missing owner fact was whether one actual typed-drain stack can be
restored after top-frame mutation, removal, and reuse of its numeric indices.
An independently chosen correct final snapshot would merely assume that fact.
This module instead computes preparations from the current stack and proves
restoration for every successful projected event prefix. The decisive native
mechanism is deduplication by numeric index across the entire frame undo list:
only the first snapshot for an index survives, including after that index is
reused by a later frame.

The checked results derive both the native no-gap assertion and exact logical
frame-stack restoration. They do not make unconditional abnormal restoration a
new inference requirement. The top-level principles of 2026-10-11 continue to
govern whether a particular restoration is needed for a semantic invariant.

## Inspected native owner and boundaries

All source references below are under `crates/yu-solver/src` at the pinned
baseline. Exact native files are copied and hashed in the frozen input bundle.

| Source owner | Projection and boundary |
| --- | --- |
| `candidate_context.rs:85–123` | A frame contains its initial/current tasks, occurrence, cause, prior processing/relation, stage, context flag, transition count, acknowledgement vector and counters, terminal flag, all four dispatch payloads, replay destination, and source-drain receipt. The Lean type parameter represents the complete logical payload. Allocation identity, vector capacity and allocator failure are outside this projection. |
| `candidate_context.rs:2249–2261` | `begin_typed_drain` obtains the current length and appends one frame. `Event.begin` pushes at precisely that native numeric index. |
| `candidate_context.rs:2263–2278` | Transactional preparation first scans every existing undo entry for the same numeric index. It reads the actual frame, constructs a content-preserving replacement, moves the original allocation into undo, and appends one undo entry. `Event.prepare` reads its own top-frame payload and retains only the first snapshot. It never accepts a caller-supplied old snapshot. |
| `lib.rs:14260–14285` | The first direct preparation caller, `prepare_nonterminal_drain`, checks the selected frame is the top and validates acknowledgement counters before preparing. It may prepare several acknowledgement owners before later mutation. |
| `lib.rs:14881–14945` | The other direct preparation caller checks the top frame and terminal stage/counters, conditionally prepares according to `terminal_prepared`, advances acknowledgement/terminal state, and finally pops. The source application must derive protection when a later call skips preparation because the flag is already true. |
| `lib.rs:14288–14420,14955–15055` | `step_typed_drain` prepares before nonterminal mutations. Function, tuple, record and variant dispatch steps each call `prepare_nonterminal_drain` before their payload changes. These are the five nonterminal preparation call sites. No arbitrary non-top write is admitted by the Lean interpreter. |
| `lib.rs:14185–14258`; `candidate_context.rs:4097–4120` | Newly started frames receive source attribution and replay destinations, and the synchronous driver may remove its newly started frame on failure. Such initial writes/removals are allowed for a new numeric slot or a reused old slot whose first snapshot is still retained. |
| `candidate_context.rs:4160–4182` | Replay-child failure cleanup truncates the stack back to the helper's saved frame count. Its projection is a sequence of top pops; authentication must establish that this removes only frames owned above that helper boundary. |
| `candidate_context.rs:2044–2074,2085–2094` | The checkpoint saves stack and undo lengths. Rollback traverses the route's undo suffix in reverse, skips indices at or above the checkpoint stack length, replaces an existing index or asserts equality with the current length and pushes, then truncates. `nativeUnwind`, `restoreAt` and `rollback` implement exactly these logical branches. |
| `candidate_context.rs:2211–2217` | Commit truncates frame undo to its checkpoint and resets preparation counters/flags on retained frames. These bulk changes are outside an active route's top-write events; their resulting logical frames form the next route's arbitrary checkpoint stack. |
| `lib.rs:9271–9273,9424,9498–9543,9664–9681` | Route begin rejects nesting, records the intrusion checkpoint, and successful/failed completion selects commit/rollback. `candidate_intrusion.rs:177–202` and `candidate_effect.rs:278–279,313–339` connect that checkpoint to the context owner. |

The source search found exactly two direct calls to
`prepare_typed_drain_update`, both listed above. The synchronous legacy body at
`lib.rs:13999–14180` was also inspected: with the candidate feature enabled,
its early `candidate_graph.is_some()` branch returns through
`run_candidate_typed_drain` before the later conditional drain body. This is
not used as permission for unprepared old-frame writes.

`State` is `Default` at `candidate_context.rs:913–914`, so the original frame
undo vector is empty. The only frame-undo mutations found are first preparation,
route-suffix draining, and commit truncation. Nonnested route boundaries provide
the intended source route to an empty journal at each checkpoint. The Lean
interpreter starts explicitly with that empty journal. It does **not** claim
correctness for an arbitrary checkpoint embedded in an older nonempty frame
journal: native deduplication would then observe the older entries too.

## Computed events and derived structural invariant

`State.frames` is top first, the reverse of the native vector. `State.undo` is
newest first, the reverse of native append order. Numeric indices still count
from the native bottom, so the top frame's index is the length of its tail.
This representation change introduces no new source operation.

`step` computes `begin`, `prepare`, `write`, and `pop`. It rejects preparation or
mutation of an empty stack. A write/pop at an old numeric index requires that
index in the current undo list; a new index at or above the checkpoint length
needs no snapshot. This is a storage-protection check, not an assertion that
every arbitrary payload change satisfies the native stage/acknowledgement
guards. Actual native successful operations must be projected into this checked
history, including the fact that previously prepared old frames remain protected.

`run` recursively computes a whole event list. `step_preserves` and
`run_preserves` derive the invariant from `initial base`, which has `base` and
an empty journal. The invariant's witnesses are produced by induction, not
supplied to the main theorem:

- An untouched portion of the old stack remains at the bottom of the current
  stack; every current frame above it may have changed or been recreated.
- The filtered old journal is generated by successively exposing the original
  top frame. Its payloads reconstruct the removed original portion exactly.
- Its numeric indices are the increasing contiguous range from the untouched
  length to the original checkpoint length.

`checked_snapshot_structure` gives the concrete conclusion. If `u` is the
untouched top-first list and `j = oldUndo base.length s.undo`, then

```text
s.frames = live ++ u
u.length ≤ s.frames.length
base = j.reverse.map Prod.snd ++ u
j.map Prod.fst = List.range' u.length (base.length - u.length)
```

When preparation reaches a still-untouched old frame, that frame must be the
next original top, and its index has no earlier snapshot. Preparation moves the
cut by one and records that exact frame. When a later frame reuses an old slot,
the contiguous range already contains its index; deduplication preserves the
original snapshot. A new index is filtered out of old-frame restoration.

## Exact reconstruction and every prefix

`restoreAt` recursively implements native bottom-indexed replacement or append.
It returns `none` precisely when the index is greater than the current length.
`restoreAt_success_iff` proves this characterization. `NoGaps` records that each
unskipped reverse-journal entry satisfies the native index guard at its own
intermediate restoration state.

`Saved.reconstruct` fills the original frames in increasing numeric-index order.
It preserves any current surplus above the original checkpoint, which native
final truncation removes. `nativeUnwind_filter` proves that skipping new indices
is equivalent to processing the filtered journal without changing its order.

The main roots, all in `YulangClosure.NativeFrameRollback`, are:

| Declaration | Exact independent input and conclusion |
| --- | --- |
| `checked_snapshot_structure` | For every payload type, checkpoint list, event list and computed endpoint, `run base.length (initial base) events = some s` yields the untouched/live split and exact contiguous old-snapshot order above. |
| `checked_no_gaps` | The same computed-execution input yields `NoGaps base.length s.undo s.frames.reverse`. No intermediate restoration success or index inequality is supplied separately. |
| `checked_rollback` | The same input yields an `extra` such that `nativeUnwind ... = some (base.reverse ++ extra)`, and `rollback base.length s = some base`. |
| `checked_all_prefixes` | For every natural `count`, the same successful whole event list yields a computed endpoint for `events.take count`, its derived invariant, non-failing reverse restoration and exact original-stack rollback. Counts beyond the list length denote the full list. |

The hypotheses contain no final well-formed journal, original-frame equality,
rollback success, or chosen restored model. A successful shorter prefix can
also be supplied directly to `checked_rollback`, including the prefix before a
native allocation or resource failure. The component does not assert that
those failures are impossible or prove native `usize`/capacity bounds.

The computed `Witness.events` starts from native bottom-first `[10,20]`, pops
both original frames, reuses both numeric slots, updates them, and additionally
creates/prepares/updates/pops a new slot. Its final top-first stack is `[51,31]`
and newest-first undo is `[(2,60),(0,10),(1,20)]`. Filtering old indices yields
`[(0,10),(1,20)]`; the original stack is restored. The every-prefix theorem also
covers the intermediate empty stack after both old frames were removed.

`Witness.duplicated_reuse_gap` separately checks that the fabricated
snapshot-every-reuse journal `[(1,40),(0,30),(0,10),(1,20)]` would fail on an
empty current stack. It is explicitly a counterexample to that erroneous model,
not a native execution or a compiler defect.

## Verification, resources, and frozen evidence

The installed toolchain is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake reports
`5.0.0-src+eb6cafb`. The pinned copied project has no external dependencies and
retains `-j1 -M1024`. No manifest, toolchain, root import, compiler source, test
expectation, shared state, or Git ref/index was changed.

Seven bounded checker/audit calls were used, each with a 120-second total
limit, one Lean thread and a 1-GiB Lean limit. Their measured aggregate process
wall time is 15.736938 seconds; the longest is 3.528327 seconds. Calls 01 and 02
preserve actual elaboration failures and sources. Calls 03, 04 and 06 pass the
focused build and named-root audits. Call 05 emitted a census but exited 1 for
two unsupported pretty-printer option names; it is a failed audit, preserved
with its exact audit source. Call 07 corrects those option names and passes the
complete audit. There are no warnings in the final changed module.

The complete audit enumerates by originating module, including private and
generated theorem constants: **110 distinct theorem constants across 205
declarations and all 24 authored roots**. It prints complete types and transitive
axiom lists, checks every required root is a theorem, and rejects project axioms
or dependencies outside the standard whitelist. No type truncation marker
appears. Axiom distribution is 61 without axioms, 10 using `propext`, 28 using
`propext` and `Quot.sound`, and 11 additionally using `Classical.choice`. No
`sorryAx`, custom axiom, native-evaluation assumption or kernel bypass occurs.

All retained scratch evidence is under
`/workspace/scratch/f98087c7ac1a/native-frame-r3`. It includes the isolated
project/cache, copied native inputs and checker, complete audit source/log,
all seven command/exit/time receipts, failed sources, authored-root inventory,
and a hash manifest for 7,294 imported interface/source/runtime-input files
covering all 1,459 audit-import modules. That manifest includes the standard
library and audit-only Lean metaprogram dependencies as a deliberate superset.

The first setup command had incorrect relative copy paths and encountered Lake
sandbox-detection failure; both are retained in the setup receipt. Native Lake
then ran successfully in the authorized process environment. The unmodified
helper's calls 03–04 briefly used automatically removed `/tmp/yulang-lean-audit-*`
directories, outside the exact scratch lease. The primary was informed;
subsequent helper call 06 sets `TMPDIR` inside the owned scratch subtree, and
the complete audit always used the owned project. No repository write escaped
the three exact leased output paths. This temporary-path mistake is not hidden
as an authorization expansion.

| Frozen artifact | SHA-256 |
| --- | --- |
| `NativeFrameRollback.lean` | `274e9a9ac1c43bc81d3b962edb6846dd5e4fa2adb2b645ebd92d6d5f38bd9964` |
| `logs/check07-full-audit.log` | `69c21f480a9036aad5fb7006befebad70545d6a17c9cc39ea29d37c81f2bee0c` |
| `dependency-hashes.json` | `cf341a623fc66983436b29c102bed10de73e86dda25b2fea6481e88c816aa76c` |
| `candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

## Parent application and first remaining premise

This component removes a separate assumed frame-stack reconstruction law from
the projected history: authenticating one event list now yields all old-frame
snapshots, their correct order, every no-gap guard, and simultaneous exact
logical restoration. It covers popping and reusing the same old numeric index,
not only updating a fixed stack in place.

The next owner obligation is to authenticate the actual route's stack and
entire frame journal against this same event sequence and the operation/worklist
history. It must establish the empty route-journal boundary, successful-prefix
payload readbacks, protection on every old write/pop including terminal skip
and exception cleanup, and the native top-frame guards throughout recursive
calls. Commit resets, nontransactional phases, allocation/capacity behavior,
fixed-width bounds, and all other owner tables retain their own source evidence.

Accepted-drain semantics, recursive current dispositions, original source/Call
evidence, record-boundary meaning and one same-scoped source witness remain
separate OPEN obligations. No source restriction, production inference change,
whole-source closure, native defect, or independent certification is claimed.
The primary owns fresh review, integration, public imports, commits and pushes.
