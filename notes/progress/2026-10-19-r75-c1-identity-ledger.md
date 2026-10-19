# R75 C1 identity-ledger closeout

Status: **CLOSED_UNFINISHED / OPEN**. The R75 rev2 source snapshot is frozen; its sole authorized focused command failed during compilation, so no C1 ledger was produced and the remaining identity-coverage obligation is unresolved.

The fixed command was:

```text
CARGO_BUILD_JOBS=2 timeout 180s cargo test -q -p yu-solver --features shadow-apply-candidate --lib candidate_c1_observer_tests -- --nocapture
```

It exited 101 after 4.8 seconds. Rust reported E0382 at `candidate_c1_observer_tests.rs:367,402`: `hir` is moved into `ConstraintBatch::collect_candidate_mode(hir, ...)` and later borrowed for `value_identity_labels`. The R75 contract ends execution authority after any failed command. No retry or code fix was made.

The frozen code copied the actual `modules`, `vertices`, `values_by_ordinal`, `checking`, and indexed `checking_by_event` containers through a `#[cfg(test)]` projection. However, because the test did not compile, it emitted no labels or owner dictionary. Independent spec review also found that the proposed test only labels HIR identities and value-graph entries while other identity-bearing fields in the C1 snapshot remain in Debug text. Complete identity-reference coverage and successful-path observer erasure are therefore **not established**.

Frozen snapshot hashes are pinned in `tasks/agent-loop/current.json` under `active_sprint.pins.r75_*_frozen`. The R75 rev1 conditional proof remains frozen and does not resolve these gaps. The spec review was STOPPED with three major findings: this compile failure, incomplete identity joins, and the stale run record that has now been corrected in current state and this receipt. Fresh independent review is complete. Compiler review confirmed the E0382 compile blocker and found a second major completeness gap: `intrusion.active_roots` (`DefinitionOrderId` references), `active_uses` (`DefinitionUseId` references), and `Plan.source_owners` are retained in the C1 snapshot but are not joined to the identity dictionary. Their Debug output omits equality payloads. The uniqueness assertions only constrain identities already collected, so complete reference coverage is still unproved. The value-graph projection itself correctly enumerates the actual five containers independently and preserves indices/multiplicity. Spec review's stale execution-record finding was corrected; its delta review cleared that finding and confirmed the remaining OPEN status. These reviews do not authorize a repair or retry.

No solver semantic or production change was made. Computation-forwarding preservation, full inference/evaluator, Simple-sub A/B remain OPEN 0→0; R50 remains NOT_ADOPTED. R75 is closed unfinished. Further C1 storage/suffix work is not authorized by this closeout and requires a new portfolio decision.

Portfolio direction from the user: retain proof depth while broadening to method syntax and role inference. After R75 reconciliation and exact baseline/runtime/lease checks, prepare a separate bounded method/role source-to-inference sprint. It must prove constructor-owned receiver/member/occurrence/scope/declaration projection and derive an authorized candidate constraint, or identify the exact missing semantic rule. No method dispatch or role-selection law may be inferred from successful solving alone.
