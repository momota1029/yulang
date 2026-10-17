# Ordinary HIR recovery expectation delta review

## Result

**CLEAN** for the exact rev7 test-only repair. The binding-specific recovery
expectation follows adopted successor §§3–4 and the independent spec
adjudication. No compiler source, public API, or diagnostic behavior changed.

The test verifies that `broken` has nonempty causal IDs; each ID resolves to an
authoritative inherited recovery record attached to `Value(broken.id())`; and
the ordered IDs equal the complete inherited record sequence for that binding.
The check rejects losses, duplicates, substitutions, extra records, and using
`prior`'s records as evidence for `broken`. Existing no-Apply,
no-UnresolvedName, and unsupported-sibling checks remain.

## Pins

- Contract rev7: `5572d93a543c49780c1275fea3a4450695f2c997e3944e18f5ba8f67194f5960`
- Adopted successor: `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`
- Spec adjudication: `3958bdf0230524dafb0d7cea5eeb939e99bc2921781e586ad6bc4cc1a1faf33c`
- Test: `46402bb4fe7a8e41eed3590c9788248e2fc4f769ccbdafcd8d98b1c57e891d79`
- Handoff rev20 as reviewed: `f5e15e312b206ac909c24309502f82c1e304c3aa2e936c2d983cdf0f476b92b1`

Read-only source/spec/test inspection only. No tests, builds, Cargo, probes,
Git, writes, or descendants. This review establishes neither test execution
nor closure of an original theorem condition.

Reviewer: `/root/ordinary_hir_recovery_expectation_delta_review`,
regression auditor, requested `gpt-6.1-sol`/low; effective model and effort
UNKNOWN. Cessation: **STOPPED**.
