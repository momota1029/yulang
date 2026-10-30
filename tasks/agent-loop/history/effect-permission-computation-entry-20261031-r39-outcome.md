# R39 outcome — CLOSED_PASS / computation-entry permission retention

Status: **CLOSED_PASS for the bounded source-retention gate**. The original effect-hygiene and whole-language proof goal remains OPEN.

Sprint: `EFFECT-PERMISSION-COMPUTATION-ENTRY/20261031-R39`
Contract SHA-256: `4324528f3c04bc78034ca7104c3be86db44cbb5a3fe9aade47635602b54080f0`
Manifest SHA-256: `e9b5643fdb925b0c45760c2e9bc930a82da215facc39ac66cdd2be271318efd1`
Baseline: `196beb2cdf76aa7250bb8a8d40bd114117290cdd`

## Adjudicated result

**PASS.** The computation-formal constructor now authenticates the actual registration through its owner HIR and the registered index in that owner's `LocalSource.expressions()`. It requires a Lambda, the exact registered parameter identity, and the exact action occurrence. It retains the complete ordered concrete row, including duplicates, and records the registration, formal, owner, scope, Lambda occurrence, annotation position, row position, and entry-effect port. State backing-byte accounting and checkpoints include the retained entry permission. The existing symbolic equality links remain; the retained permission does not add concrete inflow or subtract effects.

The revision-1 reviewer caught a blocking lookup-domain error: a LocalSource index had been used to index the separate expression-root schedule vector, rejecting valid definition-backed formals. Revision 2 fixed the source lookup and updated the Lean model. The revision-2 independent review was CLEAN, and reproduced the original dirty baseline hash exactly. Only the reviewed 98-line R39 delta across 12 narrow hunks was staged; all prior dirty changes to `candidate_effect.rs` remain outside the commit.

## Lean evidence

`ComputationPermissionEntryR39.lean` passed pinned Lean 4.35.0 read-only stdin audit: 18 complete theorem types and axiom audits, exit 0, no diagnostics. Audit input SHA-256: `859b12edafd5ef094d5de3fe95ec0ec7cf207f5e95088784a23f2d86c8a97d1f`. Dependencies are only `propext` and `Quot.sound`; two theorems are axiom-free. The corrected model derives the Lambda/formal pair from the owner-local source index and includes owner-mismatch rejection plus a definition-backed empty-schedule counterexample and valid owner-local case.

Frozen artifacts:

- Rust source `candidate_effect.rs`: `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db`.
- Lean module: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.
- Rust handoff revision 2: `c32634e3ef4a973883a25b6115e77adab9e0229d077c970f84d72e4ad7f1f142`.
- Proof handoff revision 2: `aa8a9a8aae5f4b42779bcf752e5e8b5f6bb1e4474b5f4d49254fc58a03b4d5de`.
- Independent review receipt: `63e681a488d2d812d9d321bc69d80062d0fbebc5fe62614b7d74e5712699696f`.

## Limits and Git

This gate ends at retained computation permission. Provider arrival, solver propagation, selected Catch/residual correspondence, native execution, the original Simple-sub claims, whole-language hygiene, soundness, principality, progress, termination and production remain OPEN. No Cargo, build, tests or Lake ran under the storage-constrained contract; Rust compilation and execution remain unobserved.

The first integration commit, `ff5d4d5002abafc31aa4604de7d59835393d9ceb`, was pushed before an index staging-offset defect was discovered. Its `candidate_effect.rs` blob misplaced several R39 additions despite the reviewed working source being correct. The primary recorded this error and reconstructed the exact intended blob from parent `196beb2cdf76aa7250bb8a8d40bd114117290cdd` plus only the reviewed R39 delta, excluding the preexisting dirty baseline.

The corrected `candidate_effect.rs` SHA-256 is `477b7fe56beb9eb08a2ff46ecee93785aee25b1d929d19578ea29f4c37a2bf26`. Independent review verified the corrected index candidate and then the committed blob. Corrective commit `1f5835c276143537ec58ed81db96c7c108cea8e7` (`fix: restore R39 source placement`) changes only that file and was non-forced pushed to `origin/yulang3`; push advanced `bea6b4868012da46adf52d5080c2cfad4543d707..1f5835c276143537ec58ed81db96c7c108cea8e7`. Local and remote HEAD match. No build or test was run, so Rust compilation remains unobserved.
