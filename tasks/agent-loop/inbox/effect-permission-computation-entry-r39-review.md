# R39 independent review — revision 1

Reviewer: `/root/r39_review` (compiler_referee)
Verdict: **BLOCKING**
Reviewed source SHA-256: `e768a467fabbd84bae0ad399da35bbae54a5747e24ea459ce5f5e3992c64893f`
Reviewed Lean SHA-256: `9073761488d740a209ed503bd0c572d9b8996a1ea5695e2f38b61464a5f3dde4`

## Blocking finding: wrong Lambda index domain

`FormalRegistrationInput.lambda` is assigned from the owning `LocalSource.expressions()` index (`candidate_source.rs:1098–1111`). R39 instead used that number against `CandidateSource.expressions`, which stores only expression-root schedules; definition actions live in `schedules` and member actions in `members` (`candidate_source.rs:2216–2220`).

Counterexample: `act io\nmy relay (thunk:[io] int) = thunk`. Its Lambda belongs to a definition source and there are no top-level expression schedules. The lookup fails and rejects the valid computation formal before retaining permission. Empty and symbolic-only annotations are rejected too.

The Lean model repeats this mismatch: `Inputs.expressions[f.lambda]` is assumed to equal the action occurrence. Its local theorems therefore do not establish source correspondence to the Rust constructor.

Required repair: resolve the HIR and LocalSource for `registered.owner`, index that LocalSource by `registered.lambda`, require a Lambda whose parameter ID matches `registered.parameter`, and compare its actual occurrence to the current action occurrence. Model the same owner-local derivation in Lean; do not remove the guard or search unrelated schedules.

## Other reviewed properties

The record copies the complete ordered concrete vector, including duplicates and coordinates. It adds no inflow/subtraction, preserves symbolic equality links at slots 45/46, and accounts for retained bytes/checkpoints. Final resource sampling may fail after publication; neither Rust nor Lean claims whole-call rollback. Provider arrival, Catch/residual, propagation and parent closure remain OPEN.

## Dirty-base isolation

Reviewer reconstructed the pre-R39 dirty source in memory by removing only R39 record/accounting changes and restoring the old constructor. Its SHA-256 exactly matched the admitted baseline `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`; pre-existing 802/41 changes were preserved. R39 contributed 94 net lines before correction.

Static source review only; no builds, tests, Cargo, Lake, scratch or Git mutations. Reviewer STOPPED. The correction uses only the existing R39 source/proof leases.

# R39 independent review — revision 2

Reviewer: `/root/r39_delta_review` (compiler_referee)
Verdict: **CLEAN** for the bounded R39 revision-2 delta. No blocking, major or minor findings. Reviewer STOPPED.

Reviewed SHA-256: Rust `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db`; Lean `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; Rust handoff `c32634e3ef4a973883a25b6115e77adab9e0229d077c970f84d72e4ad7f1f142`; proof handoff `aa8a9a8aae5f4b42779bcf752e5e8b5f6bb1e4474b5f4d49254fc58a03b4d5de`.

The repaired guard follows `registered.owner` through `batch.hir_for_source_root` to that HIR’s LocalSource, indexes `registered.lambda` in that source, requires the Lambda and exact registered formal ID, and compares its occurrence to the action. No schedule-array lookup or fallback remains. The Lean `sourceLambda` models the same owner-local derivation; its exactness, mismatch rejection, and definition-backed empty-schedule counterexample/positive case cover the seam without assuming a Rust simulation law.

Independent static review confirmed ordered concrete vector and identity-coordinate retention, no concrete inflow/subtraction, unchanged symbolic links at slots 45/46, reservation and symbolic handling before publication, accurate post-publication sampling boundary, byte/checkpoint accounting, and unchanged nested Function handling. Provider arrival, propagation, Catch/residual, parent theorem and production promotion remain OPEN. The reviewer relied on the producer’s reported Lean 4.35.0 18-theorem/axiom audit and did not rerun Lean.

Dirty-base isolation was reproduced in memory exactly: removing R39 changes and restoring the pre-R39 14-line constructor yields the admitted baseline SHA-256 `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`. R39 is separable as 98 net lines across 12 narrow hunks. The mixed accounting expression at source line 665 requires applying only its trailing R39 term. No unrelated dirty base change is authorized for staging. Static/read-only review; no build/test/Cargo/Lake/Git/scratch/cache/worktree.
