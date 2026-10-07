# Two-tail left-associated Apply shadow retention

Date: 2026-10-07
Baseline: `33d8cd4ef95d85712d2ab99dca0190e15c4d06bf`
Branch: `research/simple-sub-intrusion`
Status: reviewed default-off structural implementation slice
Authority: user-authorized shadow/experimental lane; no semantic or production authority

## Result

The opt-in shadow HIR path now retains exactly two ungrouped ML-application
tails as `Apply(Apply(f, a), b)`. Each Apply and operand keeps its own source
occurrence and position through the existing raw-core endpoint inventory,
pending solver rows, collection, and solve.

The computed outer callee is the retained inner Apply. It has no direct Name
resolution or direct-use registration. The inner Apply retains its actual
direct Name use. Its source-specific premise inventory contains the six
common unresolved rows; the direct inner use contains those six plus the two
formal-use applicability and directional-protection rows. No row is fabricated
for the computed outer callee.

Every Apply still carries `UnsupportedExpression` and remains
`ApplicationTypingRuleUnresolved`. Current/production HIR and source-identity
only lowering retain their previous refusal. The shadow collector emits no
semantic occurrences or facts. Three-tail calls, grouped/computed heads,
mixed tails, and nested application forms outside this exact shape remain
atomically rejected.

## Review and verification

Pre-write `spec_auditor` review established that the former `f 1 2` rejection
was only this experimental shadow support boundary, not a language acceptance
rule. The compiler-referee found no findings. The regression-auditor found two
minor test issues; the repair added five adjacent rejection controls and
corrected the explicit outer-callee endpoint assertion. Primary diff review
and focused verification closed that delta.

Commands:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --test shadow_application_resolution -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-hir -p yu-solver
rustfmt --edition 2024 crates/yu-hir/src/module.rs crates/yu-hir/tests/shadow_application_resolution.rs crates/yu-solver/tests/shadow_f5_differential.rs
git diff --check -- crates/yu-hir/src/module.rs crates/yu-hir/tests/shadow_application_resolution.rs crates/yu-solver/tests/shadow_f5_differential.rs
```

Results: HIR 8 passed; solver differential 5 passed; package check, formatting,
and whitespace check passed. No broad tests or benchmarks were run.

## Boundary

This slice establishes source/core/solver identity correspondence for one
bounded left-associated syntax shape. It proves no application typing,
call-view formation, role selection, original `beta`/`Slots(beta)`, typed
owner/contribution association, generalization, licensing, admission,
soundness, principality, or old-infer inference parity. No production route or
DAG status changes.
