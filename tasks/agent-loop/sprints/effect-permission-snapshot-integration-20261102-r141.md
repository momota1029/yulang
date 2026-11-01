# R141 — prepare a reviewed Rust integration patch for the ordered snapshot

Status: admitted by Luna under the ongoing Yulang soundness objective.
Parent: `YulangClosure.SourceProblem.InferenceSoundness` and effect-hygiene H remain OPEN.
Baseline: `a88e405b1b1c1b99a6c38e6180c977454b2507e6` (`origin/yulang3`).

## Fixed outcome

Prepare and independently review a complete patch, against immutable baseline
blobs only, that connects the R140 same-call ordered-permission comparator to
the existing successful AAR/RRR formal-permission regression fixture. The
patch must preserve the single native constructor invocation, source-row and
native-row ordering, metadata checks, and rollback assertions. It remains an
in-memory research patch: do not materialize it into Rust source, apply it,
compile it, or run tests. The existing working-tree `candidate_effect.rs` and
all other dirty/quarantined paths are outside this assignment and must not be
read, modified, staged, or used as inputs.

This fixture exercises an internal formal-annotation producer and bypasses
source preflight. It cannot establish accepted-source behavior, source/native
identity equality beyond the comparator's explicit table, injectivity of
`SourceNodeKey`, the parent theorem, H/A/B, or production readiness.

## Frozen inputs and exact output

- Baseline commit: `a88e405b1b1c1b99a6c38e6180c977454b2507e6`.
- R140 source candidate: `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-source.md`, SHA-256 `3335922fa8b259a1f4dea95bbf72e4ee6db8a99d7dd22fce25b3909e91aa8f56`.
- R140 Lean candidate: `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean`, SHA-256 `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985`; constructed but unchecked, not an acceptance premise.
- R140 independent review: `tasks/agent-loop/history/effect-permission-ordered-snapshot-20261102-r140-review.md`, SHA-256 `d3a66d051dacb2cca835325adaf081865e08987fe253aed56d89f30f2c531624`.
- Sole producer output: `tasks/agent-loop/inbox/effect-permission-snapshot-integration-r141-source.md`.
- Sole reviewer output: `tasks/agent-loop/history/effect-permission-snapshot-integration-20261102-r141-review.md`.
- Luna outcome: `tasks/agent-loop/history/effect-permission-snapshot-integration-20261102-r141-outcome.md`.

Producer uses only immutable source blobs at the baseline plus the frozen R140
candidate. Handoff includes exact base and target bytes/SHA-256, the full patch,
the native call and transaction boundary, visibility/type reasoning, expected
constructor count, and explicit exclusions. If the exact fixture/production
code shape cannot accept the comparator without changing semantics, stop and
record the first mismatch rather than inventing another fixture.

## Resources, review and stop conditions

- Luna/high implementer: at most 600 seconds; writes only the producer handoff.
- Fresh compiler-referee reviewer: at most 240 seconds; reads exact immutable
  blobs and frozen handoff, writes only the review receipt. Reviewer does not
  apply/compile/run the patch.
- Luna integration/state/Git: at most 180 seconds.
- Total: 1,020 seconds. No Lean/Lake, Cargo, build, test, environment creation,
  source materialization, scratch file, Astra, or force-push.

Accept only if the patch is complete against the pinned baseline, calls the
native constructor exactly once, compares the same-call successful suffix,
retains existing AAR/RRR, metadata and rollback assertions, and the fresh review
finds no correctness or scope issue. A reviewer change request or missing hash
is not accepted. The outcome is a reviewed research artifact, not source
integration authority. Unknown writers and quarantined paths remain untouched.
