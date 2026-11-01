# Sprint R197 — source-directed FormalEntry permission

Status: ACTIVE under exact leases in `tasks/agent-loop/history/source-formal-entry-permission-r197-activation.md`.
Branch / baseline commit: `yulang3` / `90d757d2f`.
Authority: continuing user goal (Yulang type/effect inference soundness,
effect hygiene priority); selected annotation policy
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2;
original source rule construction in `OriginalSourceSyntax.lean` and
`OriginalSourceGeneration.lean`.
Contract revision: 1.

## Original outcome and success evidence

Original parent remains `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`, with the same supported source, scope, assignment,
and one shared source witness. Before: **5/5 prerequisite packages open; 0/4
roots closed**. R169/R171 prove conditional finite-event facts but do not define
the mathematical source annotation interpretation or construct an original
source permission rule.

Construct the source-level FormalEntry effect-permission rule for an actual
annotated `OriginalSource.Formal`. Begin with its original annotation
declaration identity and exact parameter-entry scope; derive the permission
from the selected, polarity-sensitive annotation policy. Do not require or
assume a successful Rust `Trace`, expected permission payload, `prepare`,
`permissionFor`, source admission, or an already proved whole `sourceJudgment`.

The target rule must preserve the whole original coordinates (annotation ID,
Lambda/formal occurrence, parameter, source row, binder/scope/path, complete
resolved effect identities and type arguments). Symbolic variables and their
connections remain constraints. A permission is separate from actual inflow:
it creates no effects, closes no open input row, and does not subtract by
itself. Covariant `[E]` permits concrete `E` at that position; contravariant
`[E]` permits local subtraction there, while the actual handler performs it.
For example, permitting `signal` leaves an additional `write` in the outward
row when only `signal` is handled.

Success is either:

1. a kernel-checked source definition and constructor theorem deriving an
   occurrence/scope/path-owned permission from the actual source annotation
   declaration and FormalEntry rule, preserving exact concrete members,
   symbolic links and the unchanged actual inflow; then apply it to the
   original parameter-entry effect obligation; or
2. a source-grounded **BLOCKED_SOURCE_DEFINITION** receipt naming the exact
   missing declaration/meaning equation and owner, with no guessed semantics.

A definition alone, a theorem conditional on `Trace`/`permissionFor`, or a
consumer theorem is not a premise reduction. Keep the overall delta at 5/5
packages and 0/4 roots unless a source-theorem premise is actually discharged
and applied. Report any distinct effect-hygiene premise separately from those
four generic roots; do not inflate closure counts.

## Exact source and policy boundary

Original syntax gives `Formal.annotation : Option Annotation`; `Annotation` is
a resolved declaration ID. The Lambda generation case emits the actual
`sourceFormalRole` atom and value-entry `receiptFormation` plus
`entryForceReturnRebind`, or computation-entry `receiptFormation` plus
`retainedEntry`, at their original scopes. Preserve both entry modes, the
outer annotation boundary, and composed Function polarity. Do not reinterpret
the ID as inline syntax or replace it with an inferred type.

The approved policy is fixed by the user and may be used without another vote.
The missing task is its independent source-level declaration environment,
FormalEntry formation and permission equation. If the inspected source
authorities do not define how the resolved annotation ID denotes its typed
positions/concrete effect members, stop at that exact equation. Do not invent
a registry grammar, infer membership from row equality, or treat the native
collector model as the language semantics.

R169's `successful_nonempty` and R171's `successful_annotation_origin` may be
used only as clearly labeled conditional construction evidence. They do not
authenticate source semantics and cannot be premises of the new source rule.
R116/R45/R54 are downstream consumers; do not fuse their native obligations
into this source definition.

## Proof, review and source lanes

- Proof author: registered `lean_prover`, requested Sol/high, at most 2400
  seconds; one new Lean module and its one handoff only.
- Fresh independent review: `spec_auditor` or `compiler_referee`, at most 600
  seconds, after writes stop. Review the source authorization and theorem type;
  author cannot review.
- Source/Rust lane: WAITING. Do not read, build, test or edit quarantined
  `tools/inference-playground/src/runtime/machine.rs` or `receiving.rs`, or any
  other unleased Rust source. The latest FormalEntry evidence does not justify
  a Rust change. No path lease or capacity reservation is released here.
- No new environment, cache, target, scratch tree, Cargo, broad build or tests.
  The author is the sole owner of the already-existing pinned Lean 4.35.0
  `.lake` during at most two targeted checks, each at most 120 seconds, one CPU
  and the project's memory cap. Record exact printed types and complete
  transitive axiom audits for every delivered theorem.
- Keep the accepted policy and source constructor unchanged. No unsupported
  source restriction, no weakening of the shared witness, and no production
  promotion.

## Pins, leases, falsifier and integration

Frozen direct inputs and SHA-256:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceSyntax.lean`: `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- selected annotation policy: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`
- R39 `ComputationPermissionEntryR39.lean`: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`
- R116 `SuppressionPermissionR116.lean`: `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`
- R45 `InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`
- R169 `FormalEntryPrestateBridgeR169.lean` (conditional comparison only): `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`
- R171 `FormalEntryOriginR171.lean` (conditional comparison only): `03e727c104e2773ec3bbe1589c5dfb61ddb2df40d40a54de6be45583d01506f6`

Exact outputs, subject to primary collision/lease checks:

- `notes/theory/lean/YulangClosure/SourceFormalEntryPermissionR197.lean`
- `tasks/agent-loop/inbox/source-formal-entry-permission-r197.md`

First falsifier: an original annotation declaration or composed position whose
meaning cannot be supplied from approved source semantics without adding a
new rule; alternatively, a proposed permission that changes the actual inflow,
loses a symbolic connection, or authorizes subtraction without an actual
handler. The exact counterexample or missing equation must be retained.

After independent review, Luna records whether the source parameter-entry
premise was discharged, what still blocks the generic soundness root and
effect hygiene, actual resources used, and the next source-to-native seam.
Only explicit reviewed paths may be committed/pushed. All unrelated dirty,
pending-question and quarantined paths remain excluded.
