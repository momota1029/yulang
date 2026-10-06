# Shadow unary declaration root

Date: 2026-10-06
Status: default-off shadow structural slice; independently reviewed
Baseline: `2d378d0cf84b110e034d792d680f94b9369ad90d`
Implementation authority: explicit user authorization for settled shadow
structure/identity plumbing; no production inference authority

## Change

For the existing direct-leaf overlap `my f x = x` and `my f x = 42`, the
shadow artifact now retains an artifact-owned declaration `Form::Lambda` in
addition to the original body expression. Its declaration binder is distinct
from the parameter binder and is appended only after successful body
projection, so the declaration name cannot become visible in its own
initializer. `Skeleton::body()` continues to return the original leaf.

The added Lambda uses the exact source `BindingStatement` occurrence, the
existing parameter identity, no captures, and
`PendingTypedCaptureProviderReceiverAndSemanticDischarge`. The tests check
source ranges/locators, declaration/parameter distinction, body and use
identity, artifact branding, unbound self-reference, and rejection of adjacent
forms outside this direct-unary-`my` slice.

No production HIR/F5 route, ordinary application typing, Function membership,
effects, profile, `beta`/`Slots(beta)`, receipt, admission, solver, or semantic
discharge was added. The declaration Lambda records syntax structure only.

## Authority and test-contract review

Pre-write exact-conformance review passed for the bounded direct-leaf
projection and specifically authorized the two HIR/F5 binder-count updates.
The tests retain the original parameter, body, source, constraint, and solved
provenance assertions. This change adds one declaration binder and one Lambda
to those two shadow inventories; it does not change any current production F5
fact or result.

Post-write compiler-referee and regression reviews found no blocking, major,
or minor issues. Reviewed scope covered the complete three-file diff, shadow
scope/reference validation, body and binder accessors, pending premises,
feature isolation, and affected tests. Broader suites and semantic/Oracle
parity were not checked.

## Verification

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow -- --test-threads=1` — 35 unit and 1 integration test passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential shadow_and_current_f5_preserve_ -- --test-threads=1` — 2 tests passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core` — passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --features shadow` — passed.
- `rustfmt --edition 2024 --check` on the three changed Rust files — passed.
- `git diff --check` — passed.

The implementation adds one binder and one Lambda to each admitted artifact,
plus bounded header inspection and lexical validation. No production hot path
or performance measurement is involved; zero samples were taken.

## Remaining gates

Ordinary Apply, source contracts/profiles, typed incidences, call-view
formation, actual receiver and receipt, Q-independent admission, attachment,
soundness, principality, source adequacy, and production cutover remain open.
The shadow source body still has the pre-existing four pending call judgments
where an Apply occurs. This slice establishes no equivalence with current
inference beyond the separately measured source/provenance cases.
