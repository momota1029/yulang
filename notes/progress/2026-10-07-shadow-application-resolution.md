# Opt-in resolved application structure for the shadow lane

Date: 2026-10-07
Baseline: `327c3a72ec8fed7b67321fe5f9e909dc06167190`
Nested HIR extension baseline: `1870b1330160e83b71756f60300900f3e2ff4545`
Nested core crosswalk baseline: `0741c32217f8f90296c4e497ab4d4d9644e120c0`
Status: implemented M2 shadow slice plus leaf and one-level nested HIR-to-core crosswalks; reviews passed; focused checks passed
Claim class: exact source/occurrence structure through pending core projection for leaf and bounded nested applications
Semantic and production inference authority: none

## Result

The opt-in `yu_hir::shadow::lower_module_with_shadow_applications` retains a
leaf-only ordinary `MlArgument` or `CallTail` application and, for a `CallTail`,
one ungrouped nested unary application in its argument. Each source call has a
distinct `ResolvedExpr::Apply` occurrence; call occurrences join to their exact
tail nodes, and operand occurrences join to exact source nodes. Existing
`ScopeStack` and namespace resolution construct operand `NameResolution`.

The nested preflight accepts `f(f 1)` and rejects deeper, grouped, multi-argument,
annotated, block and computed shapes before publishing identities or
diagnostics. Operand names and ranges come from the unique identifier/integer
payload token while the full expression node remains the source identity key,
so leading whitespace and comments do not alter lexical resolution.

Every retained Apply carries an `UnsupportedExpression` diagnostic, and
unresolved/ambiguous operand diagnostics remain attached. Evaluation and
generalization classify Apply as unsupported. The solver collection path emits
no application facts or Function recipe for it. The enum variant and solver
refusal arms are unconditional to keep consumers exhaustive under Cargo feature
unification; only the experimental producer entrypoint/helper is shadow-gated.

Default `lower_module` and `lower_module_with_source_identity` still return the
existing error shape and diagnostic for these applications, with equality
between those two paths. Unsupported nested shapes fall back atomically before
child occurrence allocation, name resolution, diagnostic insertion or sidecar
registration.

This changes the public HIR enum surface by adding a structural variant, while
default lowering never emits it. The opt-in path does not claim source
acceptance or application typing. No callable role, entry, effect, Function
interface, endpoint, `beta`, profile, Q result, scheme, or inference result is
produced. Soundness, principality, source adequacy and production cutover remain
open.

## HIR-to-core crosswalk

The follow-up M1 test `opt_in_leaf_application_joins_exact_shadow_and_pending_core_identities`
uses `my apply x = x(x)` from one `ParsedFile`. It joins the opt-in HIR Apply
and both distinct operand occurrences to the exact shadow CallTail and
Identifier positions, verifies the two Use records share the parameter Binder,
and follows the same Apply/operand identities through `RawStructuralArena`
and `PendingStructuralProjection`. Borrowed per-call pending rows remain
attached. The ordinary and identity-only routes retain equal HIR and
diagnostics, including `UnsupportedExpression` on this call. The test's
positive output remains structural and pending; it does not establish a typed
invocation, inference parity or semantic discharge.

The nested extension retains `f(f 1)` as two Apply nodes, with separate
occurrences for both calls and all three operands. Whitespace and block-comment
variants preserve the same parameter resolution. Each call carries its own
`UnsupportedExpression`; the enclosing call also retains the nested error ID.
The nested case `my apply x = x(x 1)` also has a focused HIR-to-core crosswalk:
outer `CallTail` and inner `MlArgument` occurrences map to distinct Raw
`Form::Apply` nodes and distinct projected `PendingApply` nodes. Their direct
callee Uses remain distinct while sharing the same source Binder. Each RawCall
borrows its own pending registration rows through projection. Default and
identity-only lowering still agree and retain Error bodies. This checks only
source structure and pending evidence, not semantic or inference parity.

## Review and repair

The M2 compiler-referee review found no correctness issue in identity
ownership, atomic publication, diagnostics, solver refusal or feature
unification. The regression review found two minor test gaps: the solver test
did not first establish that its input retained Apply, and unsupported-shape
tests did not assert the absence of a source-sidecar identity. The primary
added those assertions. The reviewed implementation itself did not change.

For the nested extension, the M1 compiler-referee found a MAJOR: slicing an
`IdentifierExpression` range included leading trivia in the name. One repair
extracts the unique payload token while preserving node identity and adds
whitespace/comment regressions. A fresh compiler-referee delta review closed
that finding with no residual issues in its dependency cone.

## Verification

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --test shadow_application_resolution -- --test-threads=1` — 3 passed after the minor test repairs.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 shadow_application_collection_remains_unsupported_without_facts -- --test-threads=1` — 1 passed after the minor test repair.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver` — passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver --features yu-hir/shadow` — passed, covering HIR shadow feature unification without solver shadow features.
- `rustfmt --check --edition 2024 --config skip_children=true` on the HIR module, shadow facade and new HIR test — passed.
- `git diff --check` on all four implementation/test paths — passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_current_inference_correspondence opt_in_leaf_application_joins_exact_shadow_and_pending_core_identities -- --test-threads=1` — 1 passed.
- `rustfmt --check --edition 2024 --config skip_children=true crates/yu-core/tests/shadow_current_inference_correspondence.rs` — passed.
- The compiler-referee and regression-auditor reviews of the M1 test found no correctness issues; regression review's minor scope-comment mismatch was repaired in the companion test comment.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --test shadow_application_resolution -- --test-threads=1` — 5 passed, including nested identities, trivia resolution, atomic rejection and unchanged default/identity-only routes.
- `rustfmt --check --edition 2024 --config skip_children=true crates/yu-hir/src/module.rs crates/yu-hir/tests/shadow_application_resolution.rs` — passed.
- `git diff --check -- crates/yu-hir/src/module.rs crates/yu-hir/tests/shadow_application_resolution.rs` — passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_current_inference_correspondence opt_in_nested_application_joins_exact_shadow_and_pending_core_identities -- --test-threads=1` — 1 passed; outer and nested call identities and their separate pending rows reach flat pending core projection.
- `rustfmt --check --edition 2024 --config skip_children=true crates/yu-core/tests/shadow_current_inference_correspondence.rs` and focused `git diff --check` — passed.

No broad suite or performance measurement was run. Direct solver refusal was
verified for the earlier leaf-only shape; the nested crosswalk stops at
pending core structure and has no solver parity claim. Production inference,
typing, semantic acceptance and all soundness/principality/source-adequacy
gates remain open.
