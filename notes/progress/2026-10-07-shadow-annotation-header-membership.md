# Shadow annotation and call header membership

Date: 2026-10-07
Baseline: `283592aa9f83b480660067d1f4c51bd0690fb0c1`
Status: implemented default-off source identity plumbing; regression review passed with a minor coverage repair
Claim class: exact root-header membership borrowed through annotation and pending-call views
Authority: user-authorized shadow structural/evidence plumbing only
Semantic and production inference authority: none

## Result

`RawAnnotation` now retains optional `RawHeaderParameter` membership by joining
its existing validated `ParameterAnnotationIncidence` binder through the
already constructed exact root-header map. `PendingSourceCallRegistration`
also borrows the `RawCall` header membership already retained for the exact
callee use. No source identities or registration rows are synthesized.

The focused test uses two annotated root parameters and an unannotated root
parameter, each present as a direct call target. It checks source annotation
order, exact occurrence/position/incidence/header references, membership on
all three call rows, the empty existing annotation-incidence inventory for the
unannotated parameter, foreign-artifact rejection, and every unchanged
per-application premise reference. Empty annotation inventory is asserted only
as structural inventory for this syntax; it is not used as a semantic
annotation-absence rule.

The regression reviewer found one minor gap because the first fixture only
exercised annotated callees; the primary repaired it with the unannotated root
parameter call and reran the focused tests. No independent delta review was
run on this test-only repair. The exact retained projection does not support
annotated nested Lambda parameters today; changing that source envelope is
outside this slice.

Annotation interpretation remains `PendingTypedPortAndProfile`. This change
does not infer an active boundary, permission, role, typed port, `beta`/Slots,
admission, protection, or inference result. Production lowering and solver
routes remain untouched.

## Review and verification

The regression auditor found no blocking or major finding in the bounded
identity joins, public observers, or sibling call paths. Its minor test finding
is described above. No semantic interpretation or production conformance was
reviewed.

Checks run:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_annotation_header_membership --test shadow_raw_structural_inventory --test shadow_derivation -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core -p yu-solver
rustfmt --edition 2024 --check --config skip_children=true crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_annotation_header_membership.rs
git diff --check
```

The three selected integration targets passed 21 tests total. The feature-off
check passed. One Cargo process ran at a time, with at most two build jobs and
one test thread. No broad workspace suite, benchmark, performance sample,
Oracle execution, annotation interpretation, or production route was
exercised.

The first run of the new target exposed a test-only call to a nonexistent
`BinderId::name` accessor. The test was rewritten to use the already retained
root-header parameter index; the final focused run above then passed.
