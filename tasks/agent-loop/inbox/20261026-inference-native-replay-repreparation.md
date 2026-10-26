# Native retained-acknowledgement re-preparation — frozen delta

Date: 2026-10-26. Assignment `20261026-inference-native-replay-repreparation`,
revision 1. Generic leaf worker `/root/native_replay_acknowledgement`;
no descendants. Requested/observed model and effort: UNKNOWN from runtime
metadata. Primary-reported accepted baseline:
`9fe10fd65bc8eac14ac1a9ef0560ea11c36756b1` on `yulang3`.

## Exact authorized outcome

Construct the concrete missing retained-index re-preparation path identified
by the accepted predecessor's fresh review, preserving the old terminal
preflight. Grant: 1,200 seconds from first clock `2026-10-26 05:17:16 UTC`, at
most ten focused checker/audit calls, each 120 seconds/one thread/1 GiB. No
Rust/native tests/probes, dependencies, children, Git or shared records.

Original parent remains `SourceProblem.InferenceSoundness`,
`Contracts.lean:128`: every supported original source, scope, generated
constraint and successful solution must yield an original source judgment with
the SAME scoped witness. No source-domain or semantic change is proposed.

## Written paths and preserved inputs

Only these repository paths were written:

- existing `notes/theory/lean/YulangClosure/NativeReplayAcknowledgement.lean`;
- new `notes/theory/2026-10-26-native-replay-repreparation.md`;
- this new handoff.

Scratch/cache/evidence lives only under
`/workspace/scratch/f98087c7ac1a/inference-native-replay-repreparation/`.
The accepted old acknowledgement paper/handoff/review and lifecycle paper were
rehash-verified byte-identical. No old evidence directory or prior receipt was
modified. The old accepted module is separately preserved as
`NativeReplayAcknowledgement-before.lean`; the complete patch is
`module-delta.diff`. All 35 old authored theorem statements and the terminal
preflight definition remain unchanged. The primary owns imports/global audit,
review, central records and Git.

## Constructed result and application

Outcome class: **kernel-checked constructive projection delta**, with full
native-map authentication still OPEN.

`FrameEvent.reprepare` records the original prepared index and selected ack.
`FrameStep.reprepare` carries the actual helper's presence/top/bounds/indexed
readback guards, has no stage guard, and changes only `prepared`. It preserves
`terminalPrepared`, stage, completed acknowledgements, vector, destination,
transition count and all other frame fields. Actual nonterminal callers include
Diagnostics. The old terminal `preflight` still selects `completed` only when
`completed=prepared`.

The new `Repreparation.prepareGuard` computes actual optional-owner/cursor
checks from `candidate_context.rs:2405–2427`, including exact Running ack/queue
identity, rejecting Ready, and adding no retired-bit check. Its equivalence to
independently stated cursor guards is proved.

`Repreparation.nonterminal_reprepare` is the combined root. From reachable
frame initialization/history, presence and supplied native cursor readbacks,
it computes the retained-suffix prefix, constructs its guarded frame trace,
derives reachability/accounting and full preservation of every other field,
bounds steps by the initial deficit, proves every preceding selected ack's
guard succeeds, and concludes complete preparation OR the exact first failing
guard. No supplied valid-ack list or completed-frontier invariant replaces the
computation. `reprepare_deficit_decreases` proves strict one-step progress;
`scan_complete_exact_steps` gives the exact successful iteration count.

`paired_owner_lookup_step` constructs the existing cursor `Step.prepare` and
new frame write from the same selected ack and the explicit equation
`owners ack.operation = readback cursorProjection`. It derives both accounting
facts. The local lookup equation is explicit; this is not a global map proof.

`commit_scan_outcome` includes working and Diagnostics stages without excluding
either. On complete scan, `commit_scan_complete_frame` proves exactly
`{ oldFrame with prepared := oldFrame.acks.length, terminalPrepared := false }`.
`complete_scan_then_append` preserves the full-prepared invariant after the next
working Transport append. Two-ack witnesses construct working and Diagnostics
commit/re-preparation, including the decisive second iteration where
`completed=0`, `prepared=1`, and the second ack is selected. A missing owner stops
at the first guard without advancing the prepared frontier.

Native owners: `lib.rs:14261–14335,14405–14416,14881–14947,14955–15035`;
`candidate_context.rs:2212–2216,2250–2279,2376–2382,2405–2427`.

## Resource and source boundaries

A complete prepared frontier is not a native `Ok`. The native helper can fail
at frame/replay undo reservation, injected preflight failure, or resource
observation after the loop, including after complete preparation.
`resource_stop_prefix` constructs and accounts every successful prefix of the
computed guard scan, including its full prefix. It does not invent allocation
success, identify an actual resource event, or prove the global rollback journal.

The full shared operation/worklist/frame/restoration/journal readback remains
OPEN, including authentication of owner-map inputs and selected preparation
events against one actual execution. `MERGE-EXPANSION-COVER-1`, semantic child
closure, original record boundary `j`, full Call, contextual meaning and the
whole original inference theorem remain OPEN. No runtime repair or compiler
bug/impossibility claim follows.

## Complete verification and preserved failures

Pinned Lake `/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual version receipts: Lake `5.0.0-src+eb6cafb` with Lean `4.35.0`; Lean
`4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Own isolated cache/project, three unchanged configs, only pinned Std imported.
`LEAN_NUM_THREADS=1`, `-j1 -M1024`, 120-second process-group timeout; bounded
native-execution escalation for the known sandbox self-location limitation.
No global-toolchain/SYSROOT/dependency changes.

- `check01.log`: failed proof iteration; simplifier recursion/guard unfolding,
  plus two new lint warnings. The warnings were repaired, not suppressed.
- `check02.log`: failed equality-normalization and witness-frame inference
  iteration; zero warnings. Both failure source snapshots remain in `sources/`.
- `check03.log`: final selected-module build PASS, 2 jobs, **zero warnings**.
- `audit04.log`: all-origin type/axiom audit PASS, **zero warnings**.

Audit coverage: **723 originating declarations, 306 theorem constants, all
67 authored roots (35 old + 32 new)**, including private/generated declarations.
Each has its complete printed type and axiom list. Actual sets over all
originating declarations: 585 none; 72 propext; 38 propext+Quot.sound;
28 propext+Classical.choice+Quot.sound. Main composed roots may use all three
allowed standard axioms; no project axiom, sorryAx, unchecked evaluation or
kernel bypass is accepted. Final changed-module forbidden-token search is clean.

`named-roots.txt`, `old-authored-roots.txt`, `new-authored-roots.txt`,
`named-types-axioms.txt`, `new-types-axioms.txt`, exact source/configuration
hashes, source snapshots, all logs, and the complete audit program are retained.
All final manifest entries were rehashed and matched after documentation.

Consumed four focused checker/audit invocations of ten granted, plus two
read-only version queries. No timeout, native/Cargo tests, executable native
probes, children or Git. No optional checks remain running.

## Frozen identities and cessation

| Artifact | SHA-256 |
| --- | --- |
| Extended Lean module | `5264c6b6d9904a43ec0b50c3ac0100a05612b724f52a8601e3a93c771f8204df` |
| New delta paper | `08c8e2d19cc36bb1572bfeba569bfb5e7b382098e2ec2201e8edfaa116f7fb2b` |
| Final selected-module build | `892032aec1f6cf18f2fd353a5d5324f8b94f1f0cbbacfd8bcafb3e4ff32137d5` |
| Final all-origin audit | `31a971b68216fc44a9cca9e4be423bc11e94798d58365dae43b0f0b31dde2523` |
| Final manifest | `366bec659fa56a20b8c4f73e3b4495adda40ef1e583171613f0f1c5e5a57ae46` |

**Writes stopped.** This revision and its checked module are frozen for fresh
nonauthor delta review. No descendants, background work or unresolved leases.
The primary owns exact integration and any subsequent repair lease. The author
does not claim independent acceptance. Remaining owner request: authenticate
the computed guarded suffix and resource-stopped prefix against the real
shared native maps; the finite re-preparation transition itself is now present
and checked.
