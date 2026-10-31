# R118 static Rust integration analysis — revision 1

## Assignment and parent

- Sprint / contract: R118 revision 2; contract hash was not among the frozen inputs supplied to this worker.
- Assignment / handoff: `R118-RUST-INTEGRATION` / revision 1.
- Parent: original Simple-sub inference-soundness and effect-hygiene claims, source/native correspondence, original A/B claims, and production remain OPEN.
- Baseline: immutable source commit `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`.
- Requested model / effort: Luna / high. Observed model / effort and runtime telemetry: UNKNOWN in this worker view. Current worker identity: `/root/r118_rust_integration`; assignment bound ≤300 seconds. No descendants.
- Claim class: static integration-candidate analysis only. No Rust source was integrated, compiled, or validated.

## Frozen input identity

The R117 patch SHA-256 matches the assigned value:

- R117 patch: `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`.
- R117 Rust handoff: `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e`.
- R117 independent review 2: `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`.
- R113 corrected handoff: `2227bbd1b596e2c794d9f820e05c9ad766b7593c733a6eb278697f66e2545013`.
- R113 outcome: `c30d59940912c6a056f8b72cbf55d83d9b38b5f4c65f487d0d90206636f41922`.
- R111 corrected handoff: `54a79a1b4f49d75b78bd3c3e96ff2c317941c57e24dfbad6e2c441309f131d9d`.
- R111 outcome: `a0ed59f783f4b1b06504a66aa3c6e7bf55039a8038352860434de760d75e26a0`.
- R111 contract rev3: `d1461c3204bacf59783d918e2c6ebc6ec1776693ecf814ed5d31dda938597976`.
- R113 contract: `a52bfb6a5e9d6e92dd5543214ff6b442ecc8e70e09e2be6daa1662385fba71f4`.

Prior review/outcome evidence says the R111 candidate receiver target is `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`, derived from baseline receiver blob `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`. R111's complete candidate also needs `lib.rs` target `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` and baseline `candidate_effect.rs` plus only the `RowKey` import, target `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`.

## Static hunk interaction

R117 is a six-hunk candidate against the baseline `candidate_receiver.rs`. R111's four receiver repairs are at baseline lines 4186, 4385, 4433 and 4628. Comparing those locations and the frozen hunk bodies shows no shared edited line or replacement context:

| R117 baseline hunk | R111 interaction | Static observation |
|---|---|---|
| 231 (projection fields) | none | Independent struct-field additions |
| 603 (request fields) | none | Independent request-field additions |
| 1860 (permission lookup and consumer guards) | none | Before every R111 receiver edit |
| 4844 (request construction) | none | After R111 edits; R111 ownership correction removes three net lines before this hunk |
| 5052 (owner/batch/state identity) | none | After R111 edits; same three-line preceding offset change |
| 5106 (origin, retained permission join, projection construction) | none | Review 2 reports the baseline old context actually starts at 5109 although the hunk header says 5106. R111's three-line net deletion before it moves that context to 5106 in the R111-first candidate, but does not change the context bytes. |

Thus the patches have no direct semantic hunk overlap in the receiver. Their line coordinates do interact: applying R111 first shifts R117's later contexts by -3 lines; applying R117 first shifts later R111 locations by the preceding R117 net insertions. The final R117 hunk's already-noted three-line header/context discrepancy is especially relevant: the R111 net deletion happens to align its actual context with the advertised old start in an R111-first layout. This is coordinate arithmetic only; no patch application or conflict-resolution test was performed.

An R111-first overlay is the clearest conceptual integration order because R117's baseline owner checks are then read against the R111-corrected receiver and all R117 changes are additions or replacements at distinct regions. It does not authorize integration. A combined candidate full-file hash is **not reported**: no patch application or byte synthesis was performed, and no exact combined bytes were frozen. The R117 patch SHA authenticates only its unapplied patch, not a combined source candidate.

## Type, API, and borrow observations

- R117 review 2 already statically inspected the iterator item shape in the package permission vector: `permission` is a reference to the retained record through the tuple, so `std::ptr::eq(*permission, self.catch.permission)` compares the retained payload addresses. R111 changes no type or use at this site.
- The provider projection borrows `provider_family` from the selected owner view and `permission` from the retained source-internal permission inventory. The patch carries those borrowed values into `InventoryCatchRequest`; no R111 hunk changes those source lifetimes. The exact lifetime/type check nevertheless remains unestablished absent compilation.
- R117 adds calls to `Option::is_none_or` and `std::ptr::eq`, plus `usize::try_from`; the frozen R111 evidence says the baseline does not pin a Rust toolchain. Therefore the standard-library API floor and actual method-resolution/type-check result are unknown under this contract. R117 review 2 explicitly lists Rust type/borrow checking as unestablished.
- The provider/catch checks use full operation IDs and the retained record's `registration`; the package check keeps compact-vector `permission_index` separate. R111's Member ownership repair invokes the pre-existing `owns_source_root` path and does not remove these checks. This is static correspondence only, not evidence of executable behavior.

No additional blocking type error was established from the frozen inputs. That statement is not a compile result.

## Parent application and disposition

This R118 analysis adds a narrow integration fact to R113: R117's receiver patch and R111's reviewed receiver repairs touch distinct source regions, and the R111 ownership edit shifts later R117 coordinates by three lines while offsetting the R117 review's final-hunk metadata discrepancy. It does not establish a source-to-constraints-to-propagation-to-execution path, or any new consumer, propagation edge, or runtime behavior. R117 strengthens a private native observation/projection route only.

R113 already records `NO_SAFE_CODE_SLICE` and the R111 compile gate as blocked because the contract's isolated hard storage cap is unavailable. R117 review 2 accepts only an unapplied, uncompiled research patch. Therefore no Rust source integration, source promotion, compile, or push is authorized by this analysis. The exact current answer is **static candidate overlay is regionally compatible in the inspected receiver hunks; integration remains blocked by the unchanged R111 compile gate**.

Reused evidence: R111 exact source candidate hashes, source/API pins, Member-owner behavior and execution blocker; R113 corrected classification, protected-expectation findings, absent adapter consumer and `NO_SAFE_CODE_SLICE`; R117 handoff and independent review for the six patch hunks, payload pointer level, unique registration selection, retained-storage index, operation identity, owner/batch/live-state pointer checks and review limits.

Rejected as evidence: R111 review is not compilation; R117 static review is not compilation; no green test, runtime trace, or theorem is inferred. No withdrawn Simple-sub bypass is restored. No source domains, diagnostics, expectations or semantics were changed.

## Checks, resources, and STOP

- Checks: read only required workflow guidance and the listed frozen R111/R113/R117 artifacts; verified SHA-256 of the R117 patch and listed handoff/outcome inputs; compared R117's six frozen hunk regions with R111's four receiver edits and recorded the offset relationship. No source patch was applied or materialized.
- Not run: Cargo, rustc, compiler/build/test, formatter, patch application, repository check, Git mutation, environment/storage probe, source write, scratch/cache/worktree operation.
- Runtime receipt: requested Luna/high; observed model/effort UNKNOWN; actual active seconds and launch telemetry unavailable. No descendants. Writes stop with this frozen revision.
- Exact changed path: `tasks/agent-loop/inbox/effect-permission-rust-integration-r118.md` only.
- Generated/disposable scratch paths: none.
- Pending: fresh primary adjudication and any independent review required by Luna. This author does not certify the analysis.
- Next related in-envelope step: none for this static packet. A next source integration attempt depends on Luna resolving the already-recorded R111 execution-cap blocker; this worker does not request an authority or lease change.
