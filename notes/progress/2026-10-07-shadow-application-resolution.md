# Opt-in resolved application structure for the shadow lane

Date: 2026-10-07
Baseline: `327c3a72ec8fed7b67321fe5f9e909dc06167190`
Status: implemented M2 shadow slice; compiler-referee review passed; regression minor findings repaired and focused checks passed
Claim class: exact source/occurrence structure for one leaf-only application
Semantic and production inference authority: none

## Result

The new opt-in `yu_hir::shadow::lower_module_with_shadow_applications` retains
one ordinary `MlArgument` or `CallTail` application with identifier/integer
leaf operands as `ResolvedExpr::Apply`. The application, callee and argument
have distinct occurrence identities. The application occurrence joins to its
exact tail node; leaf occurrences join to their exact source nodes. Existing
`ScopeStack` and namespace resolution construct operand `NameResolution`.

Every retained Apply carries an `UnsupportedExpression` diagnostic, and
unresolved/ambiguous operand diagnostics remain attached. Evaluation and
generalization classify Apply as unsupported. The solver collection path emits
no application facts or Function recipe for it. The enum variant and solver
refusal arms are unconditional to keep consumers exhaustive under Cargo feature
unification; only the experimental producer entrypoint/helper is shadow-gated.

Default `lower_module` and `lower_module_with_source_identity` still return the
existing error shape and diagnostic for these applications, with equality
between those two paths. Unsupported nested, grouped, multi-argument,
annotated, block and computed shapes fall back atomically before child
occurrence allocation, name resolution, diagnostic insertion or sidecar
registration.

This changes the public HIR enum surface by adding a structural variant, while
default lowering never emits it. The opt-in path does not claim source
acceptance or application typing. No callable role, entry, effect, Function
interface, endpoint, `beta`, profile, Q result, scheme, or inference result is
produced. Soundness, principality, source adequacy and production cutover remain
open.

## Review and repair

The M2 compiler-referee review found no correctness issue in identity
ownership, atomic publication, diagnostics, solver refusal or feature
unification. The regression review found two minor test gaps: the solver test
did not first establish that its input retained Apply, and unsupported-shape
tests did not assert the absence of a source-sidecar identity. The primary
added those assertions. The reviewed implementation itself did not change.

## Verification

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --test shadow_application_resolution -- --test-threads=1` — 3 passed after the minor test repairs.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 shadow_application_collection_remains_unsupported_without_facts -- --test-threads=1` — 1 passed after the minor test repair.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver` — passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver --features yu-hir/shadow` — passed, covering HIR shadow feature unification without solver shadow features.
- `rustfmt --check --edition 2024 --config skip_children=true` on the HIR module, shadow facade and new HIR test — passed.
- `git diff --check` on all four implementation/test paths — passed.

No broad suite or performance measurement was run. The validation only covers
the opt-in leaf-only shape, direct solver refusal, and the stated HIR feature
configurations.
