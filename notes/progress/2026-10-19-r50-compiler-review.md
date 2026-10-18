# R50 compiler review — primary-integrated receipt

Status: **CLEAN at proposal scope; NOT ADOPTED**. This receipt integrates the
independent compiler reviewer's message. The reviewer was read-only and did not
author a file; no reviewer-file hash is claimed. Luna independently checked
the frozen targets against the hashes below before persisting the message.

## Frozen target

- Contract: `tasks/agent-loop/sprints/active-link-admission-design-20261019-r50.md`, rev1, SHA-256 `283f2d8abe6c62cdcaee3fd7991705b4c8a0b3dce6df4446dc204aaf4737b8da`.
- Draft rev2: `notes/design/2026-10-19-active-link-admission-r50-draft.md`, SHA-256 `1e623a11b569ecffd403d997f934ffc92637da5c7f6b35e945edf4c486621673`.
- Handoff rev2: `notes/progress/2026-10-19-r50-implementation-handoff.md`, SHA-256 `f322bb7d5021bea95738dce9033a0cbb134b9e8528f26495ef21c3868c4c3ead`.
- Sol proof: `notes/theory/2026-10-19-r50-active-link-refinement.md`, SHA-256 `9f42dbbbf7c3e7e4d91484dc10f63026023684c6b3557d961b53399ff1b74413`.
- Sol inbox: `tasks/agent-loop/inbox/20261019-r50-proof.md`, SHA-256 `0c3a9f14864620b9028481c851a7df680437d57cfad752bc15d15affda7cc0a8`.

## Independent source findings

No blocking, major or minor finding. The pinned source path supports the
proposal's conditional successful-prefix claim **if** a guarded current-action
context is added as specified by P1–P4. The current compiler has no such active-
Link consumer guard:

- `candidate_source.rs:1032–1124,1239–1253`: an active initializer emits a
  Link to its existing root before Install; nested helper Names can retain the
  outer active root.
- `candidate_source.rs:1445–1475`: definition bodies also emit Link, so opcode
  identity alone cannot prove active-local origin.
- `candidate_source.rs:1608–1660,1669–1673`: the source cursor advances only
  after action success; Link uses ordinary slot-30 value constraint flow.
- `candidate_scheme.rs:1986–1993` and `lib.rs:12042–12099,12296–12319`: the
  guarded Link path runs the typed drain to completion before returning. A
  same-frame current Candidate can therefore rely on the earlier successful
  prefix, but this does not prove satisfiability or source typing.
- `candidate_call.rs:690–739`: current scoped authentication requires exact
  occurrence, installed scheme and authentic FreshUse; there is no active-Link
  branch.
- `shadow_apply.rs:1763–1789` and `lib.rs:11218–11235`: an alternate admission
  caller exists. The proposal's explicit current-action guard must reach the
  consumer; `graph.source.is_some()` alone is insufficient.
- `lib.rs:9214,9467–9490`: rollback restores source frame, local slots and
  routes. The proposal correctly distinguishes an earlier intrinsic Link from
  later failed route work and does not claim same-session replay after intrinsic
  failure.
- The fixture/assertion at `candidate_source.rs:1717–1754` and
  `candidate_scheme.rs:2663–2717` was inspected. The scoped `execute().unwrap()`
  was not executed and is not runtime evidence.

Under proposed P1–P4, sibling/stale occurrence, another attempt, solver-equal
root substitution, failed or unexecuted Link, definition-body Link,
Install-after use and an unguarded caller cannot authenticate. Existing
installed generalized-local checks remain in force. These are unimplemented
conditions, not current compiler guarantees.

The independent spec review also found the proposal clean. Explicit user
adoption remains required before architecture adoption; implementation then
needs a separate exact code contract. Parent remains **OPEN, 0 -> 0**. `Desc`/
`D_q`, complete Call, effects, F1/FK1, soundness, principality, evaluator and
production correspondence remain open.

Reviewer receipt: requested `compiler_referee`; effective model/effort,
CPU/RSS UNKNOWN; 300 seconds charged. Read-only inspection/hashing only; no
tests, build, runtime, Git, edits or descendants. The reviewer reported
**WRITES_STOPPED; NO_DESCENDANTS**. This file is Luna's message integration, not
a reviewer-authored artifact.
