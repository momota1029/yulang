# Pending source-call registration view

Date: 2026-10-06
Baseline: `3e294397ac83d3bb211041ced459686f43d3f58e`
Status: frozen, spec-audited default-off shadow reference plumbing; no findings
Authority: user-authorized shadow/experimental lane; no semantic or production authority

## Result

The shadow-gated raw core arena now offers `PendingSourceCallRegistration`, a
borrowed projection over the exact validated source-call input, the source
Apply, that Apply's ordered existing pending rows, and its optional lexical
capture incidence. It reuses the HIR-owned join and adds no duplicate registry
or identity namespace.

The seven-entry `SourceViewPremiseLocator` remains a separate topology-specific
inventory. Core retains the HIR `CapturedCallInput` only when its call, use,
outer binder, capture lambda, captured binder, occurrence and capture position
all match the same raw call. The locator delegates to that existing input only
for that matching registration. Ordinary direct calls do not inherit those
seven requirements. Grouped callees receive no direct-use registration;
computed callees retain only their immediate direct-use inner call where
present. No absent registration or annotation is interpreted semantically.

This exposes existing references for a future experimental producer. It does
not form a call view, classify a formal, construct a slot/profile/typed path,
interpret effects, discharge premises, invoke successor inference, or alter
production routing.

## Verification and review

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_raw_structural_inventory -- --test-threads=1` — final run: 7 passed.
- `rustfmt --edition 2024 --config skip_children=true crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_raw_structural_inventory.rs` — passed.
- `git diff --check` — passed.
- Independent spec-auditor review: PASS, no findings in scope. It checked topology scoping, separation of the seven locator categories from per-call rows, identity joins, no Q dependence, and no semantic absence inference.
- The focused test command was invoked three times: the first test import needed correction; the second revealed an unsupported nested-block fixture in the new test; the final supported fixture set passed. No HIR behavior or existing expectation was widened or weakened.
- Production isolation: the core shadow module remains feature-gated; no production inference route changed.
- Three Cargo invocations total, each bounded to two build jobs and one test thread; zero performance samples. Broad suites, feature-off build and inference parity were not run. No Oracle execution.

## Remaining work

The view has no semantic consumer yet. The original contribution/slot rule,
complete profile, independent admission, role resolution, soundness,
principality, source adequacy and production cutover remain open. A later
successor-versus-current-infer differential needs a real successor semantic
result; this structural test does not claim that parity.
