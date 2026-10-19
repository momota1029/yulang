# R128 rev4 — recovery of frozen candidate provenance and verification order

Status: **RECOVERY PROPOSAL; no recovery receipt, review, or verification is authorized until a fresh prospective spec review is CLEAN and Luna grants the exact continuation.** This version preserves the R128 parent, source, and claim. It records rather than erases the rev3 workflow breach.

## Parent and authority

Parent remains `R119-TARGET-JOIN-1`, with the unchanged 148-byte R119 role/impl source, original quantifiers, and M/T/A separation. Rev3 contract SHA-256 is `0b7a1e2b625a1d95d62cbf63e19ef5c51d6ea1427baffc6b1820ed02b82a5273`. Its frozen checkpoint remains `58d5507d400385d7b4affbda1e7c9b51779ce019` (short `58d5507d4`). The proof and source/test claims remain bounded to finite syntax-to-HIR source correspondence and the earliest candidate-gate obstruction.

No method selection, R85 adoption, compiler behavior, test expectation, fixture, or public method-execution claim is authorized. Keep R119 M/T/A, R85 adoption, all six effect-hygiene parents, and original Simple-sub/evaluator A/B OPEN.

## Adjudicated rev3 findings and immutable chronology

The rev3 exact test passed once before the three required final reviews. At that execution, the reviews were NOT_RUN. This breached rev3's review-before-verification order. The breach is permanent historical fact and is not retroactively cured by this revision.

The producer implementation handoff records test SHA-256 `1e4ffaa52e14008716da3a790808cf6bae7aea5b165b71df4283d94c7c7f9571`. Luna repaired six `PositionId` borrow expressions; the exact post-repair file at the reviewed checkpoint hashes to `65de2d91ff14af0c5408fc1f1770deefd4a4e611d7bd327d4c3bfc55b58e98fb`. The pre-repair bytes are authenticated in unreachable commit `72700e3b1e5ebb46045604aa0ec7ecc9c3c09a9d` (`Checkpoint`, parent `b37e7ab9defb1b2142976c1bef782c08a3ba6b31`); the file there hashes to the producer's `1e4ffaa...` receipt. The diff from that checkpoint to `58d5507d4` is exactly six borrow-only edits, each adding a borrow to the `artifact.position` argument. No other test lines changed. No Git ref was created or changed to recover this evidence.

The three rev3 review receipts are immutable:

- compiler/source: `tasks/agent-loop/inbox/20261019-r128-compiler-final-review.md`, MAJOR / not CLEAN;
- spec/authority: `tasks/agent-loop/inbox/20261019-r128-spec-final-review.md`, NOT CLEAN / BLOCKING;
- regression: `tasks/agent-loop/inbox/20261019-r128-regression-final-review.md`, CLEAN for the bounded test at `58d5507d4`.

Their disagreement and findings remain in force as historical rev3 outcomes. Recovery can establish prospective acceptance of one authenticated candidate; it cannot make rev3 CLEAN.

## Fixed recovery outcome and outputs

Authenticate a primary recovery receipt relating the producer's exact pre-repair bytes to Luna's exact post-repair bytes, authorship, six-line delta, frozen checkpoint, and test execution chronology. Reuse the frozen proof and existing regression review. Obtain fresh compiler/source and spec/authority acceptance of the same recovery receipt and immutable checkpoint. If both are CLEAN and the regression receipt remains applicable, run the exact contracted HIR test one more time as a **second**, prospectively authorized execution. This second execution does not replace or relabel the first.

Recovery receipt: `tasks/agent-loop/inbox/20261019-r128-recovery-implementation.md`.

Fresh review outputs:

- `tasks/agent-loop/inbox/20261019-r128-recovery-compiler-review.md`;
- `tasks/agent-loop/inbox/20261019-r128-recovery-spec-review.md`.

The source/test tree, proof, rev3 contract, original implementation handoff, and three rev3 review receipts are immutable. Luna writes only the recovery receipt and current state. Reviewers write only their respective review output. No producer or reviewer may amend prior receipts.

## Verification gate

After the recovery receipt is frozen and both fresh reviews are CLEAN, and Luna confirms the prior regression CLEAN still applies to exactly the same test bytes, run exactly once:

```sh
cargo test -p yu-hir --lib tests::shadow_method_role_source::qualified_member_head_routes_through_operation_namespace_without_target_join -- --exact
```

This is a second execution. It is authorized only by this rev4 after the stated prospective review gate. Charge up to 120 seconds and stop on failure. Do not run any other test, build, compiler, CLI, probe, formatter, or Git mutation under this recovery packet. Any candidate-byte change, new regression surface, failed review, or resource inconsistency stops the packet and requires a new Luna adjudication.

## Resource envelope

Rev3 accounting is preserved, with 1,354 seconds charged (including a conservative 30-second charge for Luna's six-borrow repair), and its three final reviews remain fully charged. Rev3's remaining 146 seconds comprised 86 seconds of verification reservation and 60 seconds for closeout. This revision cancels the unused 86-second verification reservation and reallocates it to recovery work; the 60-second closeout reservation remains. The recovery allocation is 400 seconds, of which 86 are reallocated and 314 are a new increment. The cumulative R128 cap is 1,814 seconds (1,354 charged + 400 recovery work + 60 closeout). There is no reset, refund, Astra allocation, or release of inherited UNKNOWN reservations.

Recovery work allocation (400 seconds total): prospective contract review 60; Luna recovery receipt and frozen hash inventory 60; fresh compiler/source review 80; fresh spec/authority review 80; one second exact verification 120. The 60-second contract review is spent before any recovery receipt is written. The remaining allocations are granted only after that review is CLEAN. No budget category may be borrowed or expanded by a worker.

## Stop and completion conditions

Current state is `REVIEW_BLOCKED_RECOVERY_PROPOSED`; no recovery writer or reviewer is running. Unknown legacy identities, quarantined paths, and reserved capacity remain unchanged.

Stop if the prospective reviewer rejects this recovery contract, if provenance cannot be authenticated, if either fresh final review is not CLEAN, or if the second exact verification fails. A successful recovery closes only this bounded R128 evidence packet as a verified conditional witness. It closes no theorem, method-target join, semantic adoption, production, effect-hygiene, or original A/B gate. Luna remains sole adjudicator and Git integrator.
