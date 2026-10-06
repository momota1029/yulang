# Test-only current F5 freshening correspondence trace

## Scope

This checkpoint adds private, test-only observation of current F5 incoming
route freshening. It records the exact `DefinitionUseId` and target member,
then maps each quantified or recursive binder ordinal to the fresh value-row
ordinal already produced by the existing substitution. Row ordinals are
session-local.

The trace is compiled only under `cfg(all(test, feature = "shadow-f5"))` and
must be enabled explicitly on a test `InferenceSession`. It stages evidence
before the existing scratch substitution is cleared and publishes it only
after outer route sampling succeeds. Failed attempts discard pending evidence.
The trace reads the substitution without changing it or affecting solver
counters, diagnostics, schemes, projections, or routing.

## Evidence

Focused tests cover repeated source-backed quantified/recursive uses, a
synthetic mixed Q/R scheme with both recursive bound relationships, and a
late route-exit failure followed by successful retry. Trace-enabled and
trace-disabled source runs compare solver observations. The mixed case asserts
one captured record per route with exact use-ID order, avoiding vacuous binder
checks.

Checks passed:

```text
RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 --lib tests::shadow_f5 -- --test-threads=1
# 5 passed
RUSTC_WRAPPER= cargo check -p yu-solver --no-default-features
git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/tests/shadow_f5.rs
```

An initial Cargo invocation was blocked before compilation by the configured
sccache wrapper; rerunning with `RUSTC_WRAPPER=` passed. One test attempt
revealed that cloned constraint batches share collection query counters. The
enabled/disabled fixtures now use isolated collections built from the same
source-backed HIR and compare exact use identities.

## Limits

This is evidence of what current F5 does, not a successor rule or semantic
interpretation. It does not establish source `beta`/`Slots(beta)`, profile or
endpoint ownership, or correspondence to successor Q/R identities. Broad
suites and cross-session row identity were not checked. Bottom fast-path
capture and an outer sample-overflow witness remain uncovered.
