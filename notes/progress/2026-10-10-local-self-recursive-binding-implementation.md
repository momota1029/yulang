# Local self-recursive binding implementation checkpoint

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Mode: M2 cross-layer implementation
Authority: [local self-recursive binding](../design/2026-10-10-local-self-recursive-binding.md) and approved q1/a1

Implemented the reviewed parameterized local-function recursion slice. HIR
temporarily binds the function's own `HirLocalId` during its initializer, then
retains the existing restore-and-publish boundary. Candidate source scheduling
tracks active initializer roots and emits ordinary `Link` actions for recursive
occurrences, including references inside nested helpers. `Work::Install`
remains after initializer actions. Recursive links do not route through a
`LocalScheme`; later uses retain ordinary capture and freshening. No
default/public inference route or new admission rule changed.

The producer added HIR and candidate regressions for local identity, parameter
and outer shadowing, sequential scope, plain-value and forward-reference
controls, same-root recursive links, nested helpers, monomorphic recursive
constraints, later independent integer/Function uses, annotation/effect
boundaries, and failed-session discard/reconstruction. Independent semantic
review found no production issue. Independent conformance review found one
P2 evidence gap: the annotation-triggered conflict did not prove shared root
identity. The test was repaired to assert that direct and nested recursive
`Action::Link`s both target the same `Action::Install` initializer before
installation; the finding was closed by delta review.

## Verification

Producer focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib local_self_recursive_binding -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_local_self_recursion -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib local_self_recursion_tests -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement recursive_definition_is_fresh_at_external_uses -- --test-threads=1
```

The focused tests passed with counts 4, 5, 2 and 1. After the test-only repair,
the internal kernel filter passed again with 2 tests.

The primary also ran the adjacent existing invariants:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib local_scheme_publication_rollback_preserves_prior_slots_and_retries -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib natural_local_capture_keeps_live_late_integer_bounds_and_shared_older_images -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement independent_local_uses_have_distinct_value_and_effect_images -- --test-threads=1
```

All three passed. The owning cross-layer check passed without warnings:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-hir -p yu-solver --all-targets --all-features
```

Scoped `git diff --check` passed. Measurement budget: zero samples / zero
processes.

## Remaining scope

This checkpoint does not close zero-header lambda-valued initializers, local
mutual recursion, complete Call, effect hygiene, soundness/principality,
public/default inference migration, or F5 replacement. Full inference
replacement remains active.
