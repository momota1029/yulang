# Spec adjudication: recovery expectation in ordinary HIR test

Fresh independent spec auditor `/root/ordinary_hir_recovery_expectation_spec_adjudication`
(`spec_auditor`; requested gpt-6.1-sol/low, observed UNKNOWN) STOPPED with a
MAJOR finding that the assertion is defective under already adopted semantics.
Reported active work about35s; charged40s cap. Read-only only; no tests, builds,
Cargo, probes, Git, writes, network or descendants.

Verified contract rev7 SHA-256
`5572d93a543c49780c1275fea3a4450695f2c997e3944e18f5ba8f67194f5960` and adopted
successor SHA-256
`2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.

Finding: `ordinary_application_admission.rs:326–330` incorrectly expects a
module-wide `UnsupportedExpression` for recovery-bearing
`my prior = @; my broken = f(`. Adopted successor §3 lines88–89 and §4
lines119–129 preserve existing recovery causes/attachments and place
`has_recovery` before projection. Broad §2 wording does not require synthesizing
an unsupported diagnostic when the recovery gate already returns its causal
`ResolvedExpr::Error`. `module.rs:2196–2204` implements the adopted ordering.
Adding such a diagnostic would change semantics and is not authorized.

For each `b` in `{prior, broken}`, its value remains `ResolvedExpr::Error` with
its existing ordered causal IDs/body range/occurrence. Each referenced
inherited error is attached to `Value(b.id())`; neither binding admits Apply or
resolves hidden operands. No synthetic `UnsupportedExpression` is required for
either recovered body. IDs from `prior` cannot establish inheritance for
`broken`.

Minimal expectation closure: for `broken`, look up every exact `HirErrorId`
from its Error value in `HirModule::errors()`; assert the records are authentic
inherited recovery kinds attached to `Value(broken.id())`, and the ordered list
equals all inherited causal records for that binding without loss, duplication
or substitution. Preserve no-Apply, nonempty causal-ID and no-UnresolvedName
assertions. A module-wide inherited-kind assertion is insufficient.

This is an erroneous test artifact, not an implementation defect or new
semantic choice. This review alone grants no edit authority; Luna has explicitly
adjudicated the conditional test-only correction under sprint rev7. Original
theorem conditions remain open; closed: 0.
