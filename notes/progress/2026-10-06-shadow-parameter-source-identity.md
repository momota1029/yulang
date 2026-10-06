# Shadow HIR parameter source identity

Date: 2026-10-06
Status: implemented, focused-test verified, independently regression-reviewed
Baseline: `f551bac00adaa4fe7e8676f0bbeaee616674078c`
Authority: default-off experimental source identity plumbing only

## Result

The opt-in HIR source-identity sidecar now retains the exact accepted
`IdentifierPattern` node for each existing unary `HirParameterId`. The borrowed
shadow artifact joins that parameter ID to its parse-branded `PositionId` via
`parameter_source_position`. It uses the source key captured while the original
header node is available; it does not reconstruct identity from a spelling,
range, ordinal or nearby syntax node.

Focused structural tests cover repeated parameter names in separate
bindings, equality between ordinary and opt-in HIR lowering, equality with the
shadow skeleton's retained binder position, foreign HIR and parse rejection,
missing sidecar and missing parameter mapping. The method exposes source
identity only. It creates no `beta`/`Slots(beta)`, role, annotation meaning,
profile, typed path or inference judgment, and does not expand current lowering
acceptance.

## Facade inventory synchronization

The feature-on core facade test had stale counts after HIR added already
reviewed pending-only formal-use and directional-protection requirement rows.
Before repair, the focused test observed 14 rows where the facade expected 8
for two direct-use Applies, and 7 where it expected 4 for the nested captured
call. The test now asserts 14 and 7 and checks all seven per-call categories
in their HIR emission order. Existing call-identity and semantic
non-discharge checks remain. These rows remain unresolved metadata, not
semantic consequences.

## Verification and review

Passed focused checks:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow source_identity_correspondence -- --test-threads=1` — 6 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_feature -- --test-threads=1` — 3 passed after synchronizing facade expectations (the pre-repair run had the two stated count failures).
- Rustfmt checks on both changed Rust files and `git diff --check` passed.

A regression auditor reviewed the parameter identity implementation and
found no blocking or major issue within the HIR sidecar, ownership/parse
branding and neighboring-call-site scope. A separate regression review
confirmed the 14/7 facade inventory and per-call premise ordering against the
HIR producer and sibling HIR tests. A pre-write spec audit approved the
expected-output synchronization as a correction to stale structural metadata;
no semantic rule, premise row or production path changed.

Broader package/workspace suites, feature-off checks, semantic source
adequacy, production inference and inference differential behavior remain
unverified. This slice advances source-identity plumbing only; soundness,
principality, complete source generation and production cutover remain open.
