# R81 — repair the existing R66 Incidence construction proof

Status: admitted bounded research sprint for the user's continuing Yulang soundness objective.

## Fixed outcome

Kernel-check the existing R66 `Incidence` constructor, a nonempty successful finite witness and the named rejection cases. Start from frozen R80. Repair proof elaboration and finite construction without weakening R80 statements, changing the original R66 type, adding assumptions, or supplying `Incidence`, `Root`, successful `sourceProbe`, or global-selection success.

Keep all original inventories, owner records, exact permission, source/native occurrence coordinates and Name/use versus Apply/checking coordinates. Prove the actual reader equations and constructor equalities; explicitly construct the successful finite output and derive permission/root identities. Keep adversarial rejection cases based on finite data checks. Any source mismatch, altered mathematical statement or unavailable owner record stops the packet.

## Exact assignments

- Constructive Lean proof owner (`lean_prover`): `notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean`; handoff `tasks/agent-loop/inbox/effect-permission-incidence-repair-r81-proof.md`.
- Fresh independent read-only reviewer after freeze: `tasks/agent-loop/inbox/effect-permission-incidence-repair-r81-review.md`.
- Reuse R80 Rust receiver `b1873abe5b88a3d6b750bf517d565b1ffcfc3a619f223243c19d00e9d15c0085` as the reviewed consumed join; no Rust edits or build lane. `crates/yu-solver/src/lib.rs` remains read-only.
- Primary Luna owns current state, exact-input audit authorizations, adjudication, outcome, explicit-path staging, commit and push.

## Baseline and dependencies

Baseline is post-R80 closeout commit `661b40348a712120f921cc4dbcbbbce2e467821e`. Exact source pins and retained failure/review artifacts are in `tasks/agent-loop/sprints/effect-permission-incidence-repair-20261031-r81-inputs-r1.json`. Governing definitions are R45/R55/R65/R66/R77/R79. R80’s two failed audit inputs, outputs, frozen candidate and independent review remain preserved. The first gate is accepted construction and successful witness; R66 Root and physical joins remain separate.

## Resources and checks

Fresh envelope: 2,400 seconds total (proof 1,200; independent review 600; primary 600 including 500 closeout); Astra 0. At most two separately committed and pushed exact-input Lean stdin audits, each at most 120 seconds, combined at most 240 seconds. Audit 2 failure or a changed mathematical statement stops the packet.

Same checkout only. No compiler, Cargo, tests, builds, formatter, Lake, cache, target, scratch, additional environment, nested CLI or worktree. Audits use in-memory stdin/stdout only. Retain exact inputs, stdout/stderr, executable/source hashes, complete theorem types and axiom reports. The static sprint checker and `git diff --check` are bookkeeping only, not proof or compilation evidence.

Preserve 32 pending items, UNKNOWN worker observations and quarantined path leases. Keep current state <=16 KiB. Stop with the theorem gate open if author budget expires or audit evidence fails.

## Review and integration

Freeze proof and dependencies before review. Reviewer authenticates the actual R81 construction and successful witness, all named rejection cases, complete available axiom census, source correspondence and remaining gates. Integrate only exact leased paths. Push only a coherent reviewed range to `origin/yulang3`; never force-push or disturb unrelated work.
