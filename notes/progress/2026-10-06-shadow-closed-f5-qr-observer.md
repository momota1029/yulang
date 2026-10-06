# Shadow view of closed current F5 Q/R schemes

Date: 2026-10-06
Status: implemented; compiler-referee and regression review complete
Baseline: `d986792c7964c52498d258e5eb09f65fffbb565a`
Authority: user-approved default-off shadow/experimental lane; no semantic adoption
Mode: M2 cross-layer observer; one implementer, compiler-referee and regression review

## Result

The existing `shadow-f5` feature now exposes a borrowed view of the finalized
current F5 schemes retained by `SolvedModule`. A lookup begins from the exact
HIR-owned `DefinitionRootId` and retains its finalized scheme owner. Q and R
identity comparisons are qualified by that root and the exact scheme instance,
so equal local ordinals in different member schemes remain distinct. Recursive
records expose both existing closed lower/upper endpoint handles through the
same borrowed scheme view. The source bridge delegates to the existing exact
HIR/raw-CST identity check.

This inventories current F5 output only. Q/R ordinals remain scheme-local; the
observer does not equate them with source `beta` or `Slots(beta)`, infer a
successor generalized interface, or connect annotations to typed profiles.
Use-time freshening and its binder-to-live-row correspondence remain
unobserved. The retained endpoint IDs are arena-branded, and `ClosedValueSchemeView`
validates arena ownership rather than membership in one particular scheme; the
API does not claim to enforce typed endpoint/profile ownership.

The observer is feature-gated, borrow-only, and allocation-free. It adds no
solver operation, generalization, freshening, publication change, production
query accounting or default-feature behavior. A review finding that repeated
recursive endpoint queries would revalidate all scheme bounds was repaired by
retaining the already validated borrowed view in each `RecursiveRef`; endpoint
inventory traversal is linear in the number of recursive binders.

## Checks and review

```text
RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 tests::shadow_f5 -- --test-threads=1
RUSTC_WRAPPER= cargo check -p yu-solver
rustfmt --edition 2024 --check crates/yu-solver/src/shadow_f5.rs crates/yu-solver/src/tests/shadow_f5.rs
git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/shadow_f5.rs crates/yu-solver/src/tests/shadow_f5.rs
```

The focused feature-on tests pass 2/2, and the feature-off package check
passes. Both reviewers found no blocking, major or minor correctness finding;
the compiler-referee confirmed the endpoint-membership limitation is explicit,
and the regression auditor found no changes to existing production APIs,
fixtures, diagnostics or call sites. No Cargo package-wide test suite or
performance measurement was run. The asymptotic repair was verified by source
inspection, not timing.

## Next boundary

Exact use-time Q/R freshening is discarded when `InstantiationScratch` is
cleared. A future observation slice would have to capture the existing
substitution at its owning route boundary and publish evidence atomically only
after successful route completion. That would characterize current F5
execution only; it would not prove the successor's freshening rule or source
adequacy. Source profile formation, typed incidence, comparison-independent
admission, soundness, principality and production cutover remain open.
