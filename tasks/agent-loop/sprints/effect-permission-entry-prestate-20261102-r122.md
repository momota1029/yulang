# Sprint EFFECT-PERMISSION-ENTRY-PRESTATE/20261102-R122

Status: ADMITTED bounded source/proof correspondence audit. The unchanged Rust/Lean effect-hygiene and soundness goal remains open.

## Parent, authority and success

Preserve the original quantifiers and source domain in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 and the effect permission/inflow/subtraction policy in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2. The immediate seam is R39's `ComputationPermissionEntryR39.Valid` pre-state: `recipe ∉ occupiedDomains` and `registration ∉ retainedRegistrations`.

Success means an immutable-source derivation of those two absences immediately before the actual `FormalEntry` constructor, from every relevant writer and action/retry boundary, or an exact first missing edge/source-reachable counterexample. Map only justified source facts into the existing R39 theorem premises. Do not add a Lean model/theorem, assume a source simulation, infer absence from post-state, or equate the nested callback `[Result]` row with the outer computation-entry row.

## Inputs and exact leases

Branch `yulang3`; source baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; corrected R39 source baseline `1f5835c276143537ec58ed81db96c7c108cea8e7`.

- Rust/source reads only: `candidate_source.rs` at `d177c46…` and `candidate_effect.rs` at `1f5835c…`; exact HIR/R39/R114 owner handoffs named in the input manifest.
- Existing Lean reads only: `ComputationPermissionEntryR39.lean` and its frozen proof handoff at `1f5835c…`.
- Researcher writes only `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-source.md`.
- `lean_prover` writes only `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-proof.md`; it may apply existing R39 declarations to source facts after the source handoff freezes. No new Lean declaration or audit process.
- Luna owns contract, manifest, admission, review, current state, outcome and Git.

## Required source coverage and falsifiers

Trace registration construction; initial state; `FormalEntry` scheduling/dispatch; all writes/clears of `formal_domains` and `formal_entry_permissions`; same-registration retries, failed actions, rollback/checkpoint restoration and reuse; and whether `FormalAnnotation` can precede or repeat `FormalEntry`. Distinguish recipe index from registration index and exact owner identity. Identify which checks are direct constructor guards versus global reachability invariants.

Falsifiers: a source-reachable entry action with either member already present; a write/retry/reuse path that bypasses the guard; action ordering or ownership not preserved by the R39 inputs; or a Lean `Valid` field with no corresponding actual owner. Arbitrary malformed model states are not source counterexamples.

## Limits, review and resources

No source edits, patch application, Cargo/Rust/Lean/Lake/build/test/checker execution, storage/environment probes, caches, target, worktree, copies, scratch, or quarantined/dirty-source reads. R111 remains waiting on its exact enforced 6-GiB verification resource or configured remote runner. Runtime `machine.rs` and `receiving.rs` remain quarantined. No production promotion.

Author caps: researcher 300s; `lean_prover` 300s; fresh `compiler_referee` 180s after both outputs freeze; Luna 300s; total ≤1,200s, Astra 0. Review checks all source writers, reachability, owner/index separation, theorem-premise mapping and source-domain preservation. A useful result is committed/pushed only after review and exact-path integration. STOP with the first genuine missing owner; do not produce another conditional model.

R39 source-retention gate is already reviewed/pushed. R35–R37 concern a nested callback result row and do not authenticate this outer computation row. R121 proves a successful indexed read entails local membership only after the same-record Rust-to-Lean read equation is supplied; R122 does not claim that later consumer bridge.
