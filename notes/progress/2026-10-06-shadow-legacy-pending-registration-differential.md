# Frozen old-infer call provenance to pending registration differential

Date: 2026-10-06
Baseline: `c783fb42f2f43aa965e8be59db8dfa3199905562`
Commit: `2230aa22d`
Status: regression-audited shadow-only structural differential; no findings
Authority: user-authorized differential plumbing; Frozen Oracle is historical evidence only

## Result

The existing frozen old-infer application provenance fixture for
`my apply f = { my step x = f x; step }` now joins the same historical source
application to `PendingSourceCallRegistration`. The test verifies one source
Apply, exact current HIR use/binder/argument/capture identity, whole argument
Name root, original seven per-call pending rows in order, and exact
`CapturedCallInput` plus the unchanged seven HIR locator categories.

The captured old root scheme remains opaque historical metadata. This compares
source ownership and identity plumbing; it proves no successor scheme/effect
parity, semantic call view, source adequacy, soundness, principality, or
production behavior. No Oracle was run for this change, and no Oracle semantics
are premises.

## Verification and review

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_legacy_application_provenance -- --test-threads=1` — 1 passed.
- `rustfmt --edition 2024 --check --config skip_children=true crates/yu-core/tests/shadow_legacy_application_provenance.rs` — passed.
- `git diff --check -- crates/yu-core/tests/shadow_legacy_application_provenance.rs` — passed.
- Independent regression-auditor review: PASS; existing source-span, pending-preservation and byte-mutation checks remain intact, with no semantic equivalence claim.
- One Cargo invocation; zero performance samples. Broad suites and semantic inference differential were not run.

## Remaining gates

The successor still has no semantic inference result for this call. Original
contribution/slot/profile formation, independent admission, role resolution,
soundness, principality, source adequacy and production cutover remain open.
