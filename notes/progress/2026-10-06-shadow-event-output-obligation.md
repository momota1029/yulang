# Shadow pending event-to-output obligation

Date: 2026-10-06
Status: M1 default-off shadow record; spec-auditor reviewed, no findings
Baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Authority: user-authorized shadow lane and current directional-protection gate
Implementation authority: pending premise only

## Result

Every retained `Apply` in the HIR shadow skeleton now carries one additional
`SourceEventContributionAndTypedOutputObservation` pending record. It marks
the unresolved source producer that must connect event contribution to the
original upper complete-invocation output occurrence and typed receipt /
receiver observation.

The record reuses only the existing Apply identity. It invents no typed event,
output, receipt or receiver identity and establishes no event existence,
upper exposure, `Flow`, protection, admission or semantic fact. The original
`beta`, scope and whole `xi=(nu,K,D)` remain unresolved. Existing premises and
source identities are retained in their prior order.

The exact test inventory changes are supported by the pre-write
spec-auditor's expected-output review: these arrays count pending structural
obligations, not a semantic result or an approved maximum. Only affected
inventory counts were adjusted; the reason is recorded in
`shadow_call_source_occurrences.rs` under `rules/testing.md`, expected-output
protection items 1–4.

## Review and verification

The pre-write spec audit found no issue with the pending-only contract or its
authorization. The post-write spec audit found no blocking, major or minor
conformance issue in the frozen six-file change.

Focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_ -- --test-threads=1
# 34 passed, 45 filtered
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib flat_chain -- --test-threads=1
# 2 passed; covers the private 16,000 -> 20,000 pending-count assertion
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow::tests::selected_nested_scope_accepts_formatting_with_approved_names_and_modifiers -- --exact
# 1 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow::tests::call_tail_preserves_one_whole_argument_and_pending_premises -- --exact
# 1 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-hir
rustfmt --edition 2024 --check --config skip_children=true crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_call_use_source_inputs.rs crates/yu-hir/src/tests/shadow_annotation_positions.rs crates/yu-hir/src/tests/shadow_call_source_occurrences.rs crates/yu-hir/src/tests/shadow_source_core.rs crates/yu-hir/src/tests/shadow_resolved_call_incidence.rs
git diff --check -- crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_call_use_source_inputs.rs crates/yu-hir/src/tests/shadow_annotation_positions.rs crates/yu-hir/src/tests/shadow_call_source_occurrences.rs crates/yu-hir/src/tests/shadow_source_core.rs crates/yu-hir/src/tests/shadow_resolved_call_incidence.rs
```

No production inference, F5 observation, broad workspace test or performance
measurement changed or ran. The default-off package check passed. Soundness,
principality, source adequacy, event contribution and typed evidence
realization remain open.

## Changed paths

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/tests/shadow_annotation_positions.rs`
- `crates/yu-hir/src/tests/shadow_call_source_occurrences.rs`
- `crates/yu-hir/src/tests/shadow_call_use_source_inputs.rs`
- `crates/yu-hir/src/tests/shadow_resolved_call_incidence.rs`
- `crates/yu-hir/src/tests/shadow_source_core.rs`

The primary owns task/theory synchronization and Git integration.
