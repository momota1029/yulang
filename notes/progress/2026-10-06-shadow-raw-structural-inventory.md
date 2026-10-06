# Default-off shadow raw structural inventory

Date: 2026-10-06
Baseline: `57386e8011bbaebd1f5abd7df762e1ca17f0cfc2`
Status: independently compiler-referee- and regression-reviewed M2 shadow implementation; production inference unchanged
Authority: user's explicit authorization for shadow structural/identity/evidence plumbing with unresolved judgments left pending
Semantic authority: none added

## Result

The shadow core can now consume the complete set of expressions already
retained by HIR, rather than only the body-reachable exact captured-call
candidate. `Skeleton::retained_expressions` exposes branded expression
identities with their borrowed forms; `expression_offset` validates identity
before providing a storage address. The raw core arena borrows each form
verbatim and preserves the designated body identity separately. This retains
declaration Lambdas that are present in the expression inventory outside that
body.

Each retained Apply receives only its own existing pending rows, filtered by
exact `ExprId` while preserving their original order and multiplicity. An
immediate resolved `Use` callee retains its existing binder/use incidence.
Capture metadata is attached only after validating the existing lambda-body
Apply, direct callee use, captured binder, use position, and artifact identity.
Unavailable, malformed, mismatched or cross-artifact joins reject the whole
arena before publication. Missing optional capture metadata is not interpreted
as semantic capture absence.

The new representation preserves the six current HIR `Form` variants and
introduces no `Result` wrapper, Value/Computation classification, typing,
callable role, annotation interpretation, invocation, source acceptance, or
premise discharge. The earlier exact-source `IncompleteDerivation` projection
and its `Result` behavior remain unchanged. No production inference path was
modified.

## Independent review

The compiler referee found no semantic, identity, atomicity, or authority-boundary
finding in the frozen implementation diff. The regression auditor found one
minor test gap: the raw core test checked direct-use incidence presence but did
not assert the incidence belonged to that exact call and callee. The primary
closed it by asserting exact application, binder and occurrence identity, and
adding nested `f (f x)` coverage with the same binder and distinct `UseId`s.
The focused core target passed after this repair. No further review was needed
for this test-only delta.

## Verification

Producer checks on the frozen implementation:

- `RUSTC_WRAPPER= cargo test -p yu-hir shadow_retained_expression_inventory -j 2` — 2 passed.
- `RUSTC_WRAPPER= cargo test -p yu-core --features shadow --test shadow_raw_structural_inventory -j 2` — 2 passed; rerun after the primary's direct-use assertion repair — 2 passed.
- `RUSTC_WRAPPER= cargo check -p yu-core -j 2` — passed with shadow disabled.
- `rustfmt --edition 2024 --check --config skip_children=true` on the five implementation paths — passed.
- `git diff --check` on the implementation and the final test-only repair — passed.

The initial HIR Cargo attempt with configured `sccache` stopped before
compilation (`Operation not permitted`); clearing `RUSTC_WRAPPER` allowed the
focused command to pass. No broad suite, Oracle execution, benchmark or
performance measurement was run.

## Exact limits

This adds structural inventory and identity crosswalks only. It does not
construct the original `F_cb`, `beta`/`Slots(beta)`, typed paths, profiles,
`nu,K,D`, call-view realization, receipt/receiver evidence, or original
signature licensing. No `FVIEW`-to-`SRC` edge closes. Soundness, principality,
source adequacy, exhaustive production membership/admission, and production
cutover remain open.
