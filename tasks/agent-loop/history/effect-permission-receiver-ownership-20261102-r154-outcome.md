# R154 outcome — receiver deletion held

Sprint: `EFFECT-PERMISSION-RECEIVER-OWNERSHIP/20261102-R154`
Baseline: `41c1582a26a8e80dbaa95171b298fc229a53d4aa`
Contract SHA-256: `f17ad7acc09f8045a4edb5bd453b87a310cae4252dff8e5e5bc1409772898a5e`

## Outcome

**HOLD / NO_PATCH.** The immutable dirty receiver diff is not safe to accept as preserving its existing evidence contract. No source change was applied or authorized for integration. The deletion is not an established ordinary-inference regression, and no erroneous suppression was demonstrated.

The initial owner/batch/live-context pointer comparisons are supplied by the private constructor path: the residual projection takes those values from one owner, and the internal projection retains the same owner and state. No accepted cross-session mixture was found through these constructors.

Three independent evidence obligations block the full deletion:

1. The replacement uses a registration ID as a compact permission-vector index. The vector omits formal registrations with empty concrete rows, so those coordinate systems are not interchangeable without a separately proved bounded invariant. Preserve unique registration lookup and its packed-slot/record association.
2. The observer drops the full provider/selected-arm operation identity comparison. The actual residual decision still checks operation matching, so this establishes a missing evidence join, not an execution bug.
3. The observer drops the R119 carried concrete-member index and indexed read from the same retained permission record. Boolean family membership alone does not preserve the ordered first-member correspondence.

No provider/source-owner equality is required; returned/local functions may have distinct construction owners. Permission provenance continues to depend on the exact FormalEntry action, Lambda annotation, unique registration, ordered concrete vector, and retained slice association.

## Frozen evidence

- Frozen input diff: `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154-input.patch`, SHA-256 `db49313b2b4dd1e3623f135cc043b4d8be296868c5ec3dbfe90efa6ae5a66438`.
- Implementation handoff: `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154-source.md`, SHA-256 `3e43755b3b970c780739727bea80e7d0179a2bd11a02f42cebe3543f262b5d66`.
- NO_PATCH marker: `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154.patch`, SHA-256 `585c06b7c585b42fbf003f0dfbd67df09c6e823b107fe95d6b55b80eebe48af3`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154-proof.md`, SHA-256 `6f8cb681b7e4c19a1d9f4a299f6c50d3aace2e9fa5c7d2ac5f467998366d4279`.
- Independent review: `tasks/agent-loop/history/effect-permission-receiver-ownership-20261102-r154-review.md`, SHA-256 `dce151fb043b73114079a15185f464a0266acb3206ef60e8d205807a5fd644eb`.

All seven committed Rust source hashes matched the R154 contract. The reviewer reconstructed the six input patch hunks exactly against the committed receiver baseline, without offsets or fuzz. All analysis read only committed blobs and the immutable patch; it did not inspect live dirty Rust or quarantined runtime paths.

## Checks and limits

No Rust build, Cargo test, Lean run, checker, patch application, Rust source write, scratch/cache/environment/worktree creation, or Git integration ran in this audit. The sprint's exact contract forbids staging, committing, or pushing its receiver candidate. The only commit and push under R154 covered the separately reviewed admission record, before the audit lanes began.

Compilation, runtime reachability, source-to-Lean decoding, INITIAL-STATE, CONSUMER, H, original A/B, soundness, principality, termination, and production remain **OPEN**. The separate dirty `candidate_scheme.rs` diff and quarantined runtime files remain untouched.
