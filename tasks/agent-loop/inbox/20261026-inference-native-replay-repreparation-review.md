# Native retained-acknowledgement re-preparation — independent M3 delta review

Date: 2026-10-26. Reviewer: `/root/native_lifecycle_review`, generic fresh
nonauthor leaf for this extension; no descendants. Requested/observed model
and effort: UNKNOWN from runtime metadata. Primary-reported accepted baseline:
`9fe10fd65bc8eac14ac1a9ef0560ea11c36756b1` on `yulang3`.

## Verdict and exact review scope

**ACCEPT the frozen constructive projection delta. Mandatory findings: NONE.**

The extension represents the concrete retained-acknowledgement re-preparation
transition left OPEN by the preceding review. It correctly selects the
prepared index, covers the stage-free helper including working and Diagnostics
after commit, constructs the finite successful guard prefix, and identifies
completion or the exact first false guard. It also constructs the local
same-ack cursor/frame preparation pair and accounts for every successful
resource-stopped prefix. These claims match the frozen source and theorem
types. Acceptance is confined to this projection and its explicit application
boundary.

The original joint lifecycle review and its scratch record remain frozen.
This receipt does not replace that review, authenticate the full shared native
execution, or close `SourceProblem.InferenceSoundness`. The existing
`MERGE-EXPANSION-COVER-1` frontier remains OPEN. No native defect, impossibility,
runtime repair, or semantic child-closure result is inferred.

The review used the repository authority, pre-sprint rules, the
`yulang-lean-proofs` skill and its source/execution references, the top-level
inference principles, the original selected source-boundary assignment, and
the predecessor review's source scope. The reviewer did not construct this
extension. The only new written paths are this receipt and the new review
scratch directory identified below. Producer files were frozen before review;
primary integration records and subsequent primary edits are outside this
receipt's certification.

## Frozen identities and baseline comparison

SHA-256 identities independently recomputed from the reviewed files:

| Reviewed artifact | SHA-256 |
| --- | --- |
| Extended `notes/theory/lean/YulangClosure/NativeReplayAcknowledgement.lean` | `5264c6b6d9904a43ec0b50c3ac0100a05612b724f52a8601e3a93c771f8204df` |
| `notes/theory/2026-10-26-native-replay-repreparation.md` | `08c8e2d19cc36bb1572bfeba569bfb5e7b382098e2ec2201e8edfaa116f7fb2b` |
| Producer handoff `20261026-inference-native-replay-repreparation.md`, revision 1 | `efd9f69636c87e2eb3d3f487ab0f7f0e9ce1bfd557d959260f7b8bdd2aff4fb4` |
| Producer `manifest.json` | `366bec659fa56a20b8c4f73e3b4495adda40ef1e583171613f0f1c5e5a57ae46` |
| Final focused build `check03.log` | `892032aec1f6cf18f2fd353a5d5324f8b94f1f0cbbacfd8bcafb3e4ff32137d5` |
| Final complete audit `audit04.log` | `31a971b68216fc44a9cca9e4be423bc11e94798d58365dae43b0f0b31dde2523` |
| Exact `module-delta.diff` | `b8a7cb7bd85d0b7f38b6854ceca5869ecd57fc39e8e5b9fcf620c27b423e3c54` |
| Accepted module preserved in both isolated projects | `fd39f67d2a170b5d603238d48ea4facce2d9a085f4c302155b3aa1b10026cb52` |
| Original joint review receipt | `282c71236c79ea848e9e87e4e489640f3f09c7564cdbaed306389a6b75c197c7` |

The evidence directory is
`/workspace/scratch/f98087c7ac1a/inference-native-replay-repreparation/`.
All **37 producer manifest entries** match, including isolated/repository
source equality, native owners, configurations, audit program, invocation
wrapper, version receipt, failed source snapshots/logs, and root/type extracts.
All four separately listed immutable predecessor artifacts also match.
The original review scratch hash remains
`1dbf2e1f8744195a8e85b2518eae50875622d6294e7d3f81c740dcccebea0228`.

The supplied accepted-source snapshot is byte-identical to the independently
reviewed original isolated module. Recomputing the patch reproduces the exact
supplied diff: **350 added lines, zero deleted lines**, from 632 to 982 lines.
Every old source line remains in order. In particular, the old terminal
preflight and all 35 earlier authored theorem statements are preserved. Their
entire printed type/axiom blocks match the original `audit12.log` byte for
byte. Their proofs have been rechecked over the extended transition relation;
the extension does enlarge that relation.

All old originating declaration blocks were compared as well. There are 603
unchanged blocks, 23 changed generated blocks under the same names, and two
generated FrameEvent hygiene names moving from suffix 42 to 48. The changes
are the new constructor's recursors/matchers, shifted constructor indices,
derived equality proof numbering, and generated preservation proof helpers.
They are audited in the new environment. This is not a claim that all generated
declaration types or names remain unchanged.

## Native source and semantic checks

The unchanged native owner hashes are `lib.rs`
`ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
and `candidate_context.rs`
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`.
The prior intrusion owner was also rehashed without change.

### Prepared-index transition and stage scope

At `crates/yu-solver/src/lib.rs:14261–14288`, the helper checks frame
existence, the top-frame equation, and
`completed_acks ≤ prepared_acks ≤ replay_acks.len()`. Each successful loop
iteration selects `replay_acks[prepared_acks]`, prepares that exact ack, and
increments only `prepared_acks` among the projected frame fields.

`FrameStep.reprepare` carries those relevant body guards: presence, top-frame
identity, the lower frontier bound, the strict selected-index bound and its
indexed readback. Its event records the old prepared slot and the same ack.
Its record update changes only `prepared`. The strict loop bound implies the
helper's non-strict upper bound whenever a body step occurs; initial accounting
supplies the upper bound for empty or stopped scans.

The helper has no stage check. `step_typed_drain` dispatches Acknowledgements
and ReturnReady separately and calls the helper otherwise
(`lib.rs:14290–14300`), which includes Diagnostics. The Function, Tuple,
Record and Variant dispatch helpers also call it (`:14955–15035`). The new
stage-free transition correctly models the helper body; actual caller-stage
authentication is still part of the native-history bridge. The old terminal
preflight remains restricted to Acknowledgements, selects `completed`, and
requires `completed=prepared`. Merely relaxing its stage guard would have
missed the next prepared slot.

### Actual cursor guard and local same-ack pairing

`Repreparation.prepareGuard` matches
`candidate_context.rs:2405–2427`: absent owner fails; the ack index must lie
in `[consumed, queued)`; Idle is allowed; Running requires the entire expected
ack and `queued=ack.index+1`; Ready fails. No retired-bit test is added. The
native preflight itself has none. On authentic machine-valued input, the strict
upper bound also makes the checked Running index increment representable.
The Lean natural-number input alone does not establish native authentication.

`prepareGuard_some_exact` and `prepareGuard_readback_exact` establish the exact
equivalence with cursor inequalities, `CompletionWait`, and presence where
appropriate. The source helper `prepare_replay_ack`
(`candidate_context.rs:2376–2382`) journals the tuple without mutating its
queued/consumed/wait/retired fields. The ack vector is fixed throughout this
loop. A fixed `Owners` readback therefore suits one projected invocation.

`paired_cursor_frame_step` constructs both the existing `Step.prepare` and
the new frame write using the same selected ack. `paired_owner_lookup_step`
also requires the explicit equation
`owners ack.operation = readback cursorProjection`. Thus it does not silently
join different owner readbacks. Both accounting conclusions derive from the
reachable inputs. This is a local pair of projected steps; no global mutable
owner map or actual event history is constructed by these roots.

### Computed prefix, commit and append

`scanCount` computes the consecutive guard-success prefix of the retained
suffix. The proofs construct its `Trace`, derive reachability/accounting,
identify every successful selected position, and conclude exhaustion or the
exact next ack with false guard. The combined `nonterminal_reprepare` root
takes owner readbacks, reachable frame history and presence. It does not take
a supplied valid-ack list or an already-completed output frontier.

The bound is the initial deficit `acks.length-prepared`, each new step reduces
that deficit by one, and a complete scan takes exactly that many steps.
The whole-record equation `{ scanFrame owners f with prepared := f.prepared }
= f` preserves every other projected field, including stage, terminal bit,
acknowledged prefix, destination, transition count and vector. Repeated calls
with no retained suffix perform zero iterations.

`committed` matches the two frame writes at
`candidate_context.rs:2212–2216`. `commit_scan_outcome` preserves
`terminalPrepared=false` while deriving the same completion-or-first-failure
alternative, with stage/completed/done unchanged. Its completion corollary is
the exact frame `{ f with prepared := f.acks.length, terminalPrepared := false }`.
The completion premise in that corollary selects the computed scan's success
branch; it is not disguised as an initial invariant.

`complete_scan_then_append` requires working stage and the computed complete
frontier, constructs the existing append transition, and derives full
preparation of the enlarged vector. This matches the pre-push assertion and
counter increment at `lib.rs:14331–14334`. It does not prove the appended
native work item's ownership or its preceding resource/preflight operations.

The two-ack witnesses cover commit/re-preparation in both working and
Diagnostics stages. The decisive intermediate witness has `completed=0`,
`prepared=1` and selects the second ack. The missing-owner witness performs
zero writes. These are constructive projection witnesses, not native test runs.

### Resource-stopped prefixes and exact remaining boundary

The source can fail at the initial frame snapshot, a replay undo reservation,
the test failure injection, or a resource observation after the loop. The
last case can occur after full preparation. The paper and handoff correctly
state that a complete guard scan does **not** establish a native `Ok`.

`resource_stop_prefix` constructs any successful prefix up to the computed
guard-success count, including zero and the full count, and derives its
accounting and exact frame equation. It does not assert which failure occurred,
allocation success, or a native execution-to-prefix theorem. Authenticating
an actual resource-stopped history remains OPEN. The extra undo records and
global rollback storage are outside the projected frame equality.

Actual shared owner/worklist/frame/restoration/journal authentication,
prepared-token provenance, authentic stack/readback equations, full global
rollback, semantic child completion and the earlier lifecycle expansion
frontier remain OPEN. The original source judgment with the SAME scoped
witness, record boundary `j`, full Call and contextual meaning are unchanged
obligations of `SourceProblem.InferenceSoundness` (`Contracts.lean:128`).

## Complete type/axiom evidence and review budget

The final isolated build reports success for two jobs with zero warnings.
The complete final audit reports success with zero warnings. The wrapper,
unchanged copied configuration, and version receipts establish pinned Lean
4.35.0 / Lake 5.0.0-src+eb6cafb, one thread, 1 GiB checker bound and 120-second
process-group timeout for the focused producer invocations. The two failed
iterations and their exact sources remain preserved; they are not treated as
successful evidence. The producer used four focused calls of ten granted.

The inspected audit program selects declarations by their originating module,
rejects project axiom declarations, checks all required authored theorem roots,
prints each declaration's type and axiom dependencies, and rejects every
dependency outside `propext`, `Classical.choice`, and `Quot.sound`.

Independent log parsing finds **723 unique complete declaration blocks,
306 theorem constants, and all 67 authored roots (35 old plus 32 new)**.
All 32 new printed root types were inspected against their source statements;
the 67-root and 32-root extracts exactly reproduce the complete audit. Coverage
includes six private names, 113 generated proof-helper names, and four hygiene
names. There are no unpaired blocks, duplicate declarations, missing roots,
unapproved axiom sets, holes or proof-bypass tokens in the frozen module.

| Actual axiom dependencies | Originating declarations |
| --- | ---: |
| none | 585 |
| `propext` | 72 |
| `propext`, `Quot.sound` | 38 |
| `propext`, `Classical.choice`, `Quot.sound` | 28 |

`Classical.choice` occurs in generic scan, pairing, accounting and combined
roots, including `nonterminal_reprepare`. It is an allowed standard axiom,
not an examples-only dependency. The preceding 35 authored axiom blocks are
unchanged. The complete census and per-declaration printed-block hashes are in
`/workspace/scratch/f98087c7ac1a/inference-native-replay-repreparation-review/review-audit.json`,
SHA-256 `31fb092379bf9c1bfaa429577ca3935343c66ff91570c3f34ba01998836016df`.
That record also preserves 44 checked file identities and the full baseline
declaration comparison.

The review's first clock was `2026-10-26 05:25:08 UTC`; the granted budget is
900 seconds, ending `05:40:08 UTC`. Review used **zero checker invocations,
zero native/tests/probes, zero children and zero Git commands**. Only source,
type, log, hash and metadata inspection was performed. There is no concrete
discrepancy requiring another checker grant. Primary integration validation
remains separately owned and is not substituted for this source/claim review.

## Cessation

The mandatory findings batch is empty. This is the final delta receipt for
the exact frozen identities above. The original receipt, original scratch,
source, imports, shared records and configuration were not written by this
review. After the final receipt hash is sent to primary, reviewer writes stop;
any later delta requires a separately authorized review and a new receipt.
