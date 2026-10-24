# CB-PERMISSION-TRANSPORT-20261024 — outcome

Status: ACTIVE. The frozen constructive source/runtime candidate passed fresh
independent review. This opens the three exact runtime implementation leases;
it does not certify the implementation or broader theorem.

Contract: `tasks/agent-loop/sprints/cb-permission-transport-20261024.md`,
SHA-256 `e3d2e8bdffb4cfda48057525b5e7da076acb248eee2c0c5ddaf384b478b18cd9`.
Baseline: `a0dcc92b8f8b866f7ed2e06acf399a4c86057a3c`.

## Frozen proof candidate

The candidate maps the retained HIR formal and nested Result annotation to the
same source-owned `FormalPermission` through pointer identity, parameter
recipe and structural path. It proposes separate immutable callback entry/use
records, leaving RootComp evidence and its receiver-sorted tables unchanged.
Value entry records the supplied callback and formal receipt; actual Apply
selection creates a dormant Result-effect view and use receipt before the
operation invocation. `OperationResultConsumer` opens that view after the
operation invocation retires, so request event observations include it.

The proof claims a finite frame invariant through request observation,
bubbling, delimiter unwind, discard, capture and replay. It reuses
`RootCompReturn` and `TemplateNode::View` without editing
`continuation.rs`.

Frozen files:

- `notes/theory/2026-10-24-cb-permission-transport.md`,
  SHA-256 `41c10cf9b1fc7837968f320822784867cab85855081b7d4c8d83dbc63d83c9ab`.
- `tasks/agent-loop/inbox/20261024-cb-permission-transport.md`,
  SHA-256 `0233c3eb6cc6a1d7a84c2ee6db9162a088352fe065bb246b3cae1e0384f6caaa`.

The producer stopped after 532 seconds, 33 read-only calls and three
artifact-only patches. No tests, builds, probes, code writes, Git or
descendants. No compiler behavior has been executed. The proof author cannot
certify the candidate.

## Independent review

Fresh independent review **PASS**: no blocking, major, or minor findings.
The reviewer confirmed all fourteen declared dependency hashes and the frozen
artifact, inbox and contract hashes. In particular, `RootCompReturn` checks
the returned value against its own `ReceivedValue.view`, not against the
callback effect view `w`; replay reopens historical `w, receipt` and the
resumed response retains its own consistent view/value pair. The review also
accepted the common-origin mapping, same-event/view/entry/family/active-owner
grant conjunction, RootComp separation, and lifecycle invariant through
bubbling, unwind, discard, capture and replay.

Review receipt: 2026-10-24 00:09:08–00:10:46 UTC; 98 seconds wall time, eight
read-only shell calls and two clock calls. No writes, tests, builds, probes,
Git or descendants. Session/model/effort UNKNOWN. Reviewer STOPPED.

## Independent implementation review — revision 1

The proof candidate remains accepted within its bounded construction. The
first frozen runtime implementation was reviewed independently and was **not
accepted** because of one MAJOR replay-owner defect. The proof does not certify
an implementation or broader theorem.

The reviewer found that pending `Frame::ValueEntry` stored its original
`entry_receiver`. If an argument requests and capture retains this pending
frame, replay can allocate fresh owner `r′` while the copied frame still names
retired owner `r`; the current-owner check then returns
`InvalidSourceReference` before a callback entry or receipt exists. The
reviewer's concrete sibling shape uses an unused callback argument whose
evaluation requests `signal::ping` while an enclosing handler resumes
`io::tick`. This is a code-derived transition witness, not an executed test or
verified whole-program inference result.

The minimum repair is restricted to the dormant executable Value entry:
resolve its owner through the replay control map before it is pushed. Callback
entries, uses, receipts, observations and captured views that already exist
remain immutable historical evidence. This separates executable pending-entry
ownership from historical evidence ownership.

Review receipt: 2026-10-24 00:18:31–00:20:44 UTC, 133 seconds wall time, eight
read-only shell calls and two clock calls. Contract, construction, inbox and
all three implementation hashes matched at freeze and cessation. The reviewer
reported no additional findings in the bounded paths; no files or Git state
were changed, and no tests, builds, probes or descendants ran. Session and
observed model/effort remain UNKNOWN. Reviewer STOPPED.

## Revision 1 implementation candidate (not accepted)

The implementation retains the authenticated source callback schema on Value
Lambdas, creates separate callback Entry and Use evidence, and keeps those
records out of RootComp's ordered boundary inventory. Only an actual direct
parameter-name Apply of a matching nullary Int operation creates a dormant
callback use. `OperationResultConsumer` opens its Result execution view after
the operation invocation returns and closes it through the reviewed existing
delimiter/template path. Callback Result observations cannot satisfy RootComp
queries; the local grant joins the same event, Result view, use, entry,
resolved family and active original Catch owner.

Frozen owner SHA-256 values:

- `tools/inference-playground/src/runtime/program.rs` —
  `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`
- `tools/inference-playground/src/runtime/receiving.rs` —
  `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26`
- `tools/inference-playground/src/runtime/machine.rs` —
  `084a6d72659ef0fdc9a85d3993ab1eef8384d3367506cbf6b18387fbabd23b82`

The single revision 1-authorized `cargo check -p yu-hir -p yu-solver -p
yu-playground` passed on these prior bytes. No tests or runtime probes ran, so
this is compile evidence only; it does not cover the repair.

## Bounded revision 2 repair and gate

Contract revision 2 is
`tasks/agent-loop/sprints/cb-permission-transport-20261024-rev2.md`,
SHA-256 `0c5fe5011811420ae334d2a72f0e46570eed17e0775e48f47228d799e12ce0d7`.
It preserves the original claim, semantics, baseline, three code leases and
3600-second total cap. It authorizes only replay-time resolution of a dormant
callback `ValueEntry` owner through the existing control map, one fresh
independent delta review, and one additional Cargo check after review. The
reviewed code acceptance gate remains open. No tests or runtime probes are
authorized; the additional check has not run.

The repaired three-file candidate is frozen for delta review. `TemplateNode::Bind`
resolves the pending callback `ValueEntry` receiver through the current replay
control map using `resolve_control`; the entry check and all historical
callback records remain otherwise unchanged. The repair is in `machine.rs`;
the other two runtime files retain their revision 1 bytes.

Frozen revision 2 candidate hashes:

- `tools/inference-playground/src/runtime/program.rs` —
  `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`
- `tools/inference-playground/src/runtime/receiving.rs` —
  `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26`
- `tools/inference-playground/src/runtime/machine.rs` —
  `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`

`git diff --check` passed. Independent revision 2 delta review **PASS**: no
additional blocking, major or minor findings. The reviewer confirmed that the
captured template enters the relevant outer `Owner` before the inner `Bind`,
so both borrowed-live and fresh-owner mappings are available when the dormant
entry frame is cloned. A repeated replay starts with its own control map, and
recapture retains the resolved executable owner. Only the dormant executable
frame changes; callback entries, uses, receipts, observations and views remain
unchanged.

Review receipt: 2026-10-24 00:24:58–00:25:38 UTC, 40 seconds wall time, four
read-only shell calls and two clock calls. The amendment, all three revision 2
implementation hashes and unchanged pinned dependencies matched. No edits,
Git, tests, builds, probes, descendants or running command handles. Session and
observed model/effort UNKNOWN. Reviewer STOPPED. At that point the repair had
review acceptance only; the separately recorded compile checkpoint followed.

## Revision 2 compile checkpoint

After delta-review PASS, the single revision 2-authorized command
`cargo check -p yu-hir -p yu-solver -p yu-playground` exited successfully
(0.91 seconds). It reported compiler warnings in `yu-hir` and `yu-solver`,
then finished the `yu-playground` dev profile. No tests or runtime probes ran.
This is compile evidence for the frozen revision 2 bytes only. The bounded
implementation review and compile gates are complete; the full source/native
theorem, arbitrary callback coverage and original A/B remain open.

The approved behavior and open-row rule remain unchanged; a signal grant must
not consume additional `write`. The full static residual, whole-program
acceptance, arbitrary callback coverage, source/native theorem and original
Simple-sub A/B remain open. At construction acceptance, no implementation,
tests, builds or runtime probes had run in this sprint.
