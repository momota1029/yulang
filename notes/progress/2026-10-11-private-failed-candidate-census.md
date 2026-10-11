# Private failed-candidate census repair

Date: 2026-10-11
Status: bounded implementation slice reviewed; broader rollback and W/A3 gates OPEN.
Branch: `research/simple-sub-intrusion`
Baseline: `befbe308fb123915385b3ec54a2e1fc3668a279e`

## Authority and scope

The Authoritative private candidate suspension contract §6 requires accurate
accounting across failed retained Local and RetainedResume transactions. The
F5c producer-order addendum §3's conditional O(1) postrollback rule remains
scoped to `route_incoming`. The private repair uses the existing checked census
only after failed private transaction bodies; successful transactions and
ordinary incoming/generic transaction finalization are unchanged.

## Implementation

`finish_route_transaction_with_candidate_accounting` runs one current census
after semantic rollback returns successfully and restores the journal owner.
RetainedResume transactions select this path by transaction purpose; candidate
Local routes select it explicitly. Rollback errors bypass the census. A census
overflow returns `IdentityExhausted`, and the test verifies the previously
published ledger and complete execution counters remain unchanged. Existing
event peaks survive a successful final sample.

Changed code paths:

- `crates/yu-solver/src/lib.rs`: candidate failure finalization and sampling.
- `crates/yu-solver/src/candidate_scheme.rs`: private Local selection.
- `crates/yu-solver/src/candidate_context_tests.rs`: retained-byte/current
  census, event-peak, one-final-sample, and overflow atomicity coverage.

The first compiler-referee found no blocking or major defect and one minor test
gap: the original operation and final sample returned the same error, while the
test did not compare the full counters. The primary repaired the test to return
`ReceiptMismatch`, assert final `IdentityExhausted`, and compare the complete
counter snapshot. The spec-auditor found no findings in the frozen
implementation. After the repair, the focused new tests passed again.

## Verification

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 timeout 120s cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 private_failed_candidate_census -- --test-threads=1
```

Result: 2 passed, 0 failed. The producer also ran `parsed_local_` with the same
feature, offline and single-job settings: 2 passed, 0 failed. No broad suite,
feature-disabled build, or performance measurement ran.

## Remaining gates

This closes only the private failed-body retained-census slice. Setup failure
accounting, terminal consuming-session drop on census overflow, early semantic
rollback failures, incoming candidate event accounting/O(1) correspondence,
all-source inverse totality, native HashMap reverse-insertion headroom, original
W/A3, lifecycle/readiness, complete Simple-sub inference, effect hygiene,
soundness/principality and production F5 cutover remain OPEN.

Next: establish the constructor-qualified native history (or invariant) for
capture-map rollback headroom, while continuing the independent authentic
readiness/filter/dependent-observation lifecycle bridge.
