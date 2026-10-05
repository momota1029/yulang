# Exact nested-candidate CST/shadow lexical differential

Date: 2026-10-06
Baseline: `92634f7b55bc6aaf3b7350d06e84247e777e79e4`
Status: M1 test-only shadow slice; independently spec-reviewed, no findings
Scope: `my apply f = { my step x = f x; step }`

## Result and authority

`crates/yu-hir/src/tests/shadow_source_core.rs` now contains a private source
projection that reads binding/header ownership and block sequencing directly
from the retained CST. It builds source locators from parent paths and raw
child ordinals, resolves each identifier through a separate lexical
environment, and associates the inner ordinary call through the existing
source chain association. The test normalizes shadow identities back to
retained CST locators and compares the exact outer Lambda, sequential Bind,
local Lambda, Apply, returned Use, and capture-use incidence.

The source and shadow projections share parsing; they do not share binding
order, artifact brands, or the shadow projector. Exact kinds/ranges and
occurrence paths are checked. Authority is the Authoritative nested-block
source addendum §§1–3. The frozen Oracle provides no premise or authority.

Both closure correspondence markers and all four call premises remain
pending. This differential establishes lexical source/shadow structure only;
it does not establish production HIR or infer parity, typed capture or
provider/receiver transport, receipt formation, O/A, Q-independent
registration, joint `(nu,K,D)`, soundness, principality, or source adequacy.

## Review and verification

- Pre-write and post-write `spec_auditor` review: no findings.
- `RUSTC_WRAPPER= cargo test -p yu-hir --lib tests::shadow_source_core::shadow_source_core_nested_candidate_matches_independent_cst_projection -- --exact` — 1 passed, 51 filtered out.
- `git diff --check -- crates/yu-hir/src/tests/shadow_source_core.rs` — passed.
- No production code, shadow projection, shared synthesis type, or semantic expectation changed. No broad suite or performance measurement was run.

Remaining source-formation and typed-capture obligations are unchanged.
