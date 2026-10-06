# Shadow pending-application source-use identities

Date: 2026-10-07
Baseline: `035f7f8e97f5544ccd028bd1f167b83054134fdc`
Status: implemented default-off structural view; compiler-referee review passed
Claim class: exact ownership and occurrence projection from retained application rows
Authority: user-authorized shadow identity/evidence plumbing only
Semantic and production inference authority: none

## Result

When `shadow-f5` retains a pending application row, that row now also retains
the existing optional enclosing `DefinitionRootId`. `None` records a
top-level expression. `ConstraintBatch::shadow_pending_application_source_uses`
borrows every retained direct Name operand as a distinct
`PendingApplicationSourceUseRef`, in retained row order and then callee before
argument order. Each reference preserves the original row and operand
position, enclosing root, exact HIR occurrence and unchanged `NameResolution`.
Unresolved and parameter resolutions remain visible as their existing
variants.

This is lexical source-use evidence only. It does not mint `DefinitionUseId`,
add production SCC edges, classify a callable/formal/import, assert complete
dependency coverage, or prove the application typing rule. Every row retains
`ApplicationTypingRuleUnresolved`; the existing production SCC inventory,
facts, counters, finalized schemes, errors and ordinary refusal remain
unchanged. Soundness, principality, source adequacy and production cutover
remain gated.

## Review and verification

One independent compiler-referee M1 review passed. It checked owner and
occurrence identity, row/operand ordering, exact resolution preservation,
default-off containment and the absence of semantic or production inference
claims. The focused coverage checks repeated parameter operands as separate
occurrences under one binding, both operand positions, and a top-level
unresolved callee with no enclosing root.

Checks run:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --lib shadow_application_collection_remains_unsupported_without_facts -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver
rustfmt --edition 2024 --check --config skip_children=true crates/yu-solver/src/shadow_f5.rs crates/yu-solver/tests/shadow_f5_differential.rs
git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/shadow_f5.rs crates/yu-solver/tests/shadow_f5_differential.rs
```

The differential target passed 4 tests; the focused library test passed 1
with 449 filtered; feature-off solver check, formatting and whitespace checks
passed. There were four sequential Cargo invocations because the first new
baseline comparison used a clone whose retained capacities differ. The
repaired test recollects the same HIR and compares finalized schemes by
`alpha_eq`. At most one Cargo process ran, with two build jobs and one test
thread. No broad suite, old-infer application equivalence, Oracle behavior or
performance measurements were run.

The additive shadow sidecar stores one optional root identity per retained
application. The borrowed query scans retained rows and allocates no
collection. No performance samples were taken. Grouped/computed expression
coverage and resolved/ambiguous Name variants lack new focused fixtures; the
view only projects rows the existing collector already retains.
