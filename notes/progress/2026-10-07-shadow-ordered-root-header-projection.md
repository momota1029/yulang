# Shadow projection of ordered root declaration headers

Date: 2026-10-07
Baseline: `8ea3accb8819420f69749ae2abdbc5499369203c`
Branch: `research/simple-sub-intrusion`
Status: frozen default-off shadow implementation; compiler-referee and regression review passed after a test-coverage repair
Claim class: retained source syntax/identity projection with pending semantic judgments
Authority: user-authorized experimental lane only; no language or production authority

## Result

The shadow HIR now retains the exact root statement, binding header, name,
ordered parameter `BinderId`s and body `ExprId` for supported source skeletons.
The core raw arena validates and borrows that record. Its additive
`PendingStructuralProjection::from_raw_with_header` entrypoint can project the
approved two-parameter source shape while the existing `from_raw` entrypoint
continues to require a retained unary Lambda.

For each exact direct-Use application, the raw call may expose its membership
in the retained root header parameter list. This is separate from
`RawParameterDeclaration`, which identifies an existing Lambda owner. Neither
relation classifies a semantic formal or constructs a callback slot. No
synthetic binder, Lambda, currying order, application stage, typed endpoint,
callable role, `beta`, `Slots(beta)`, annotation interpretation, profile,
admission or inference result is produced. Ordered annotation occurrences,
per-call pending rows, and validated capture joins remain borrowed as before.

The new projection now covers the root declaration structure of
`my apply f x = f x` without choosing how its header elaborates into Function
interfaces. Existing unary and exact-candidate consumers keep their prior
entrypoints and behavior.

## Review and verification

Independent review:

- `compiler_referee`: no blocking, major or minor findings. Confirmed same-
  artifact identity, atomic rejection, distinct syntactic header membership vs
  Lambda ownership, and unchanged semantic premise boundaries.
- `regression_auditor`: no blocking regression. Its minor request for explicit
  unary, captured-outer, grouped and computed callee coverage was repaired in
  focused tests; primary delta inspection found no remaining coverage issue.

Focused checks on the final code and test diff:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow_source_core -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_derivation --test shadow_raw_structural_inventory -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core
rustfmt --check --edition 2024 crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_source_core.rs crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_raw_structural_inventory.rs crates/yu-core/tests/shadow_derivation.rs
git diff --check
```

Results: 15 HIR tests, 10 derivation tests, 10 raw-inventory tests, the
default-feature-off core check, formatting and whitespace checks passed. The
first Cargo attempt failed before compilation when sccache could not execute
`rustc -vV`; clearing `RUSTC_WRAPPER` allowed the constrained rerun. Two
intermediate test drafts asserted incorrect relationships between header and
Lambda bodies/premise counts; those assertions were corrected at the test
owner, and the final focused runs passed. One Cargo process ran at a time, with
two build jobs and one test thread. No performance samples were taken.

Unverified: broad workspace tests, parser behavior outside the retained
skeleton envelope, production inference, semantic differential results,
source adequacy, soundness, principality, generalized SCC interface formation
and production conformance. This slice closes none of the DAG's open semantic
gates, including `SIG_RULES` or `ORIGINAL_ASSOC`.

## Changed paths and integration

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/tests/shadow_source_core.rs`
- `crates/yu-core/src/shadow_derivation.rs`
- `crates/yu-core/tests/shadow_raw_structural_inventory.rs`
- `crates/yu-core/tests/shadow_derivation.rs`

No manifests, expected outputs, production inference route or authoritative
design files changed. No Frozen Oracle premise or execution was used.

Commit packet: exact implementation scope above; producer baseline
`8ea3accb8819420f69749ae2abdbc5499369203c`; proposed message
`feat(shadow): retain ordered root declaration headers`. The primary owns Git
integration and the shared task record.
