# Shadow source-view premise locator

Date: 2026-10-06
Status: implemented, focused-test verified, independently regression-reviewed
Baseline: `393b77b64cef03e74b3f1e76adb22c2aac5c981d`
Authority: default-off experimental shadow structure only

## Result

`CapturedCallInput::source_view_premise_locator()` provides a borrowed view of
the upstream requirements for the selected nested `apply/step` source
topology. It lists six unresolved categories: a compatible complete original
profile; independently typed invocation and whole-row carrier/prefix/resumption
interpretation; jointly scoped original constraints; source-slot callback
boundary inputs and typed paths; independent initial caller/provider/world
admission; and source seed/refined relation existence and coverage.

The locator borrows the already validated structural input. It creates no
invocation/profile identity, typed evidence, receipt, receiver, Flow, `Q`
result, source acceptance or `SourceViewInst`, and asserts none of those
premises exists. The existing seven `PendingPremise` rows are unchanged.
Production lowering, solver behavior and semantic rules are untouched.

## Verification and review

The implementer ran the focused command
`RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir shadow_source_view_premise_locator -- --test-threads=1`;
both tests passed. Rustfmt check and `git diff --check` passed. No broader
suite, production path, or semantic differential was run. The test pins exact
input borrowing, all six inventory entries, unchanged pending rows, rejection
of foreign artifact identities, and absence of the selected topology in two
unrelated source forms.

A regression auditor inspected the exact three-path delta against the
baseline and found no regression issue. The review notes one coverage limit:
other captured fields rely on whole-input borrowing and existing sibling
tests rather than individual assertions in the new tests.

The wrapper is constant-size and borrowed, with a static inventory and no
allocation or traversal. It is not a producer for any listed premise. The
original complete profile, typed invocation/admission, source relation, and
all soundness, principality, adequacy and production gates remain open.
