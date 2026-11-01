# R142 — repair the R141 candidate's sibling-module visibility seam

Status: admitted by Luna under the ongoing Yulang soundness objective.
Parent: `YulangClosure.SourceProblem.InferenceSoundness` and effect-hygiene H remain OPEN.
Baseline: `a88e405b1b1c1b99a6c38e6180c977454b2507e6` (`origin/yulang3`).

## Fixed outcome

Correct only R141 review finding B1 in a patch-only revision. Reconstruct from
the immutable baseline and the frozen R141 handoff, changing the visibility of
`Snapshot` and `SnapshotError` to `pub(super)` while keeping their fields and
all other implementation details private. The sibling fixture must be able to
use the returned `Result` via inferred `.expect(...)`. Preserve the exact
single successful constructor invocation, same-State suffix capture,
transaction boundary, source/native order checks, and all existing fixture
assertions.

Do not inspect or edit dirty/quarantined Rust paths. Do not materialize the
candidate patch into source, apply it, build it, or run tests. This only resolves
the static visibility seam; it does not approve the internal-producer fixture
as accepted-source evidence or close source/native equality, the parent theorem,
H/A/B, or production.

## Frozen inputs and exact leases

- Baseline commit: `a88e405b1b1c1b99a6c38e6180c977454b2507e6`.
- R141 full candidate: `tasks/agent-loop/inbox/effect-permission-snapshot-integration-r141-source.md`, revision 1, SHA-256 `65c3d181b50c45f1716092e94a519aaa74a40f93a863bf1f264d1f1da12be76f`.
- R141 independent review and B1: `tasks/agent-loop/history/effect-permission-snapshot-integration-20261102-r141-review.md`, SHA-256 `be08b8fa589aa0d2a91bd0468b92620e141093873e094c3412854d4de717f650`.
- Sole producer output: `tasks/agent-loop/inbox/effect-permission-snapshot-visibility-fix-r142-source.md`.
- Sole fresh reviewer output: `tasks/agent-loop/history/effect-permission-snapshot-visibility-fix-20261102-r142-review.md`.
- Luna outcome: `tasks/agent-loop/history/effect-permission-snapshot-visibility-fix-20261102-r142-outcome.md`.

The producer records R141 v1 source/patch/target hashes, gives the full
corrected unified patch against the pinned baseline, records corrected target
bytes/hash, and demonstrates in-memory patch applicability. The patch may
differ from R141 v1 only at the two visibility modifiers and any explanation
made necessary by that correction. The producer does not replace or mutate the
R141 v1 handoff.

## Review, resources and stop conditions

- Luna/high implementer: at most 120 seconds; exact producer handoff only.
- Fresh compiler-referee reviewer, distinct from R141 author and reviewer: at
  most 240 seconds; immutable baseline and frozen R142 handoff only.
- Luna state/outcome/Git: at most 150 seconds.
- Total: 510 seconds. Cargo, tests, build, Lean/Lake, source materialization,
  scratch/environment, Astra, and force-push: zero.

Accept only if both exposed types are accessible to the sibling fixture, fields
remain private, the corrected patch is complete/applicable, and no unrelated
patch change or remaining Rust integration defect is found. Any further
compile/type issue stops this packet and remains explicit. The result is still
patch-only research evidence and does not release any existing source lease.
