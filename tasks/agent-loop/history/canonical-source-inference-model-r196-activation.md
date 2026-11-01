# R196 activation — canonical source-level inference model

Date: 2026-11-01. Primary: Luna/high.

## Authority and original objective

Activated under the user's continuing Yulang type-inference goal and the
2026-11-01 parent-backward plan. Original parent is
`YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:128–130`);
source domain, supported inputs, same scope/assignment, and shared witness are
unchanged. Call and contextual effects remain where the original rules place
them. No Rust production authority is granted in this mathematical sprint.

R195's source/core literal payload conversion is not admitted as an independent
prerequisite: the original soundness contract does not mention `Core`,
`coreJudgment`, or `elaborates`. Keep the source payload domains. The pending
typed-Union question remains open and is not answered by this activation.

## Frozen contract and dependencies

- Contract: `tasks/agent-loop/sprints/canonical-source-inference-model-r196.md`
- Contract SHA-256: `fa26559ffc6d30bbf1b91db03ab7e8f401bfe335e9d8e48e891e57155ee44fcb`
- Baseline: branch `yulang3`, commit `84f0ff11e`.
- Contract-pinned source inputs were re-hashed before activation; see the
  contract's exact SHA-256 table. The root theorem source is `Contracts.lean`.
- Original `CoreSyntax.lean` is reference-only, not a required dependency.

## Leases and resources

Exclusive output leases:

- `notes/theory/lean/YulangClosure/CanonicalSourceInferenceModelR196.lean`
- `tasks/agent-loop/inbox/canonical-source-inference-model-r196.md`

Both paths were absent before activation. No overlapping lease appeared in
current state. The live collaboration roster showed the primary active and the
prior named producers/reviewers completed; the parent selector completed its
R196 consultation. Current-state UNKNOWN identities remain UNKNOWN and their
paths quarantined; no capacity or path lease was released. There was no current
RUNNING/WAITING child to notify.

## Current-session runtime receipts

- Primary `/root`: `collaboration.list_agents` returned `/root` RUNNING during
  the R196 activation turn. This activation and its active proof coordination
  are the current work receipt. Requested Luna/high; observed model/effort
  remain UNKNOWN.
- Leaf `/root/r196_canonical_model`: direct current-session acknowledgement:
  “R196 leaf active; reading source/definitions and pins.” The primary
  confirmed this leaf is the sole verifier and owner of the existing `.lake`
  cache. Requested configured `lean_prover` (Sol/high); observed model/effort
  remain UNKNOWN.

Proof assignment: registered `lean_prover`, requested via the configured role;
maximum 2400 seconds, leaf only, no Git or semantics authority. The author owns
the existing pinned Lean 4.35.0 cache for targeted verification. No new cache,
environment, target, scratch tree, Cargo work, broad test, or full build.
Fresh independent review is reserved after a frozen deliverable, maximum 600
seconds; author cannot self-review.

## Gate and progress accounting

Before: **0/4 original roots closed; 0/5 dependency packages removed**.
The five-package counting convention is defined in
`notes/theory/2026-11-01-parent-backward-inference-plan.md`. A complete reviewed
model removes only its model package; it does not close soundness. A conditional
model or exact semantic blocker changes neither count.

The only success gate is an actual complete original-source model applied to
the unchanged parent, or an exact first missing authoritative equation with
its owner. No source constructor may be silently dropped, including pending
typed Union. No local lemma count is used as progress evidence.
