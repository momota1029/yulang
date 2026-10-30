# R39 stage ledger

Sprint: `EFFECT-PERMISSION-COMPUTATION-ENTRY/20261031-R39`  
Contract SHA-256: `c0336d8077d763138c8a15f6dbb954595d11513908e3a1aa6e8ad8116eab70c1`  
Input manifest SHA-256: `e9b5643fdb925b0c45760c2e9bc930a82da215facc39ac66cdd2be271318efd1`  
Baseline: `06f1ce59eac7a953af18f27558ad0dd8b2a97237`.

## Stage 0 — admission

- The lightweight dispatcher selected the actual source obstruction: the admitted outer computation formal `[E] int` schedules `FormalEntry` and `FormalAnnotation`; the former currently links only an optional symbolic row and the latter reaches root `Int`. Neither retains a concrete computation-permission witness.
- R39 targets only witness retention in `candidate_formal_entry_annotation` and the state/accounting it owns. It does not add inflow, impose a closed bound, subtract an effect, or authenticate provider/Catch consumption.
- Rust baseline `candidate_effect.rs` is already dirty; its exact admitted bytes are pinned in the manifest. The writer's exact path lease preserves that prefix and permits only a review-separable R39 delta; no existing diff or unrelated path may be staged.
- The proof model must derive the retained witness from explicit owner/registration/annotation/row inputs; source correspondence is independently reviewed. Full rollback is not a goal under the governing top-level principles.
- Same checkout, no new environment/worktree/copy/scratch/build artifact, no Cargo/Lake/build/test/formatter. Budget and stop conditions are in the frozen contract and admission.

## Stage 1 — parallel lanes launched

- `/root/r39_rust` launched through registered `implementer`; `/root/r39_proof` launched through registered `lean_prover`. The collaboration roster synchronized after both launches and reported both RUNNING. Effective model/effort remains UNKNOWN for the proof worker; the implementation role requested Luna/high and does not imply effective runtime settings.
- Exact disjoint output leases are recorded in `current.json`. Only the implementer has the exact dirty `candidate_effect.rs` lease; proof writes only its standalone Lean module and handoff. Neither worker has Git or status-record ownership.
- The 6,000-second R39 envelope is reserved at admission; no transfer or renewal. No environment/worktree/build/cache/target/scratch is allowed. No compiler or tests have run.

## Stage 2 — Rust producer frozen

- `/root/r39_rust` returned its frozen handoff: `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-rust.md`, SHA-256 `60f4651f519212dd5ad10034b4d4189be92b3d48adead4617a7524bf90b25667`. Live roster shows the writer STOPPED; exact write lease is now frozen for Luna intake.
- R39 source SHA-256 is `e768a467fabbd84bae0ad399da35bbae54a5747e24ea459ce5f5e3992c64893f`; original admitted dirty prefix hash was `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`. The cumulative working-tree diff versus pushed HEAD is 902 insertions/47 deletions; the pre-admission diff was 802/41. The approximate 100/6 delta is subject to exact hunk separation and independent review; do not stage the pre-existing changes.
- Producer reports a distinct `FormalEntryPermission`, registration/formal/owner/scope/Lambda occurrence checks, annotation and row positions, entry-effect port, ordered concrete IDs, state-byte accounting and checkpoint integration. The symbolic row equality remains; no inflow/subtraction is added. This is not yet independently reviewed or integrated.
- Path-limited `git diff --check` passed. No build/test/Cargo/Lake or persistent output was created. Runtime/model observations and actual time remain UNKNOWN.

## Stage 3 — Lean producer frozen

- `/root/r39_proof` returned a frozen standalone module and handoff; synchronized roster reports STOPPED. The module `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` is SHA-256 `9073761488d740a209ed503bd0c572d9b8996a1ea5695e2f38b61464a5f3dde4`; handoff is SHA-256 `cc0bca1a3f4ac90559b2d04d7d12a2363e2a4529471ef4d292318857a7544a52`.
- Pinned Lean 4.35.0 read-only stdin audit exited 0 for 14 theorem declarations, with complete types/axioms captured. Axiom sets are only empty, `[propext]`, or `[propext, Quot.sound]`; no holes or project axioms were reported. The finite model covers local source-derived constructor inputs, complete row retention and existing symbolic links; it does not establish source correspondence, runtime propagation, provider/Catch/residual, or the parent goal.
- The proof leases are frozen for Luna intake. Independent review found a blocking Rust correspondence defect: `FormalRegistrationInput.lambda` is a `LocalSource.expressions()` index but was used against `CandidateSource.expressions` schedules. Correction is in progress before R39 adjudication or commit.

## Stage 4 — independent review found a blocking correspondence defect

- `/root/r39_review` independently reconstructed the Rust pre-R39 dirty baseline exactly (SHA-256 `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`), confirming existing 802/41 changes were preserved; R39 contributes 94 net lines before correction.
- Blocking defect: `FormalRegistrationInput.lambda` is an index into the owner’s `LocalSource.expressions()`, while the implementation used it to index `CandidateSource.expressions` schedules. Definition/member-backed computation formals can be rejected. The Lean model repeated the invalid lookup domain. The full reviewer report is retained in the primary-authored R39 review record.
- Following selector guidance, correction stays within the existing R39 Rust and proof paths: resolve the HIR/LocalSource for the registered owner, use the registration’s local index, verify Lambda parameter identity and exact action occurrence; model that owner-local relation in Lean. No lease expansion, environment, build, test, or Cargo/Lake is authorized.
- Rust/proof exact write leases are reopened for this bounded correction; the reviewer STOPPED.

## Stage 5 — Rust owner-lookup correction frozen

- The implementer corrected `candidate_formal_entry_annotation` to resolve `registered.lambda` through `batch.hir_for_source_root(registered.owner)` and that HIR’s owner-matched LocalSource expressions. It requires a Lambda, the exact registered parameter ID, and the exact current action occurrence. Registration/owner/scope/recipe/domain/duplicate guards remain.
- Frozen source SHA-256 `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db`; Rust handoff revision 2 SHA-256 `c32634e3ef4a973883a25b6115e77adab9e0229d077c970f84d72e4ad7f1f142`. Revision 2 preserves the revision-1 handoff prefix. Path-limited diff check passed; no build/tests/Cargo/Lake.
- Source lease is frozen for primary intake. Lean correction remains active; no commit until its source correspondence and independent delta review close.

## Stage 6 — owner-local proof correction frozen

- R39 Lean revision 2 now derives the selected Lambda from the registration owner’s local source entry and checks its typed parameter and exact action occurrence. It removes the invalid schedule-array lookup and adds owner-local exactness, mismatch rejection, and a definition-backed empty-schedule counterexample/positive case. Revision-1 proof text is preserved in the handoff.
- Frozen module SHA-256 `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; handoff revision 2 SHA-256 `aa8a9a8aae5f4b42779bcf752e5e8b5f6bb1e4474b5f4d49254fc58a03b4d5de`. Pinned Lean 4.35.0 read-only stdin audit exited 0 with 18 complete theorem types/axiom audits; input stream SHA-256 `859b12edafd5ef094d5de3fe95ec0ec7cf207f5e95088784a23f2d86c8a97d1f`. Axioms only empty, `[propext]`, `[propext, Quot.sound]`.
- Both producer leases are frozen. The R39 revision-1 review remains BLOCKING; a fresh independent review of the correction is required before integration.

## Stage 7 — revision-2 independent review clean

- Fresh `/root/r39_delta_review` returned CLEAN for the exact revision-2 Rust/Lean delta; reviewer STOPPED. Full revision-1 BLOCKING and revision-2 CLEAN reports are preserved in `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-review.md`, SHA-256 `63e681a488d2d812d9d321bc69d80062d0fbebc5fe62614b7d74e5712699696f`.
- Reviewer confirmed the owner-local source lookup, exact formal and action identities, complete ordered permission retention, no inflow/subtraction, symbolic-link identity, state accounting/checkpoints, and accurate local publication boundary. Parent/runtime/provider/Catch/residual obligations remain OPEN.
- Dirty-base reconstruction exactly matches admitted SHA `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`. R39 is separately stageable as 98 net lines across 12 narrow hunks; one accounting-expression hunk must retain only its R39 suffix. No pre-existing change may be staged.

## Stage 8 — commit and push receipt

- R39 bounded source-retention gate adjudicated CLOSED_PASS after the revision-2 CLEAN independent review and the pinned Lean audit. Outcome: `tasks/agent-loop/history/effect-permission-computation-entry-20261031-r39-outcome.md`, SHA-256 `f1a278f2373ab70a051e9e39007a0d59e4d1c5bb86fbf5c0a46a9baff1847258`. Parent effect-hygiene/soundness and provider/propagation/Catch/residual gates remain OPEN.
- Exact reviewed R39 patch and records committed in `ff5d4d5002abafc31aa4604de7d59835393d9ceb` (`feat: retain computation entry permissions with source identity`). Outbound range was one commit, eight R39-owned paths; prior dirty source changes were excluded.
- Non-forced push succeeded: `origin/yulang3` advanced `196beb2cdf76aa7250bb8a8d40bd114117290cdd..ff5d4d5002abafc31aa4604de7d59835393d9ceb`.
