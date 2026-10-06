# Shadow source identity correspondence

Date: 2026-10-06
Status: implemented in the default-off shadow lane; compiler-referee and regression review complete
Baseline: `6505a5c70`
Scope: parse-branded source-node identity between raw-CST shadow positions and selected production HIR identities
Semantic and production-inference authority: none

## Result

`ParsedFile` now mints a private parse brand preserved by `Clone`. Its
`source_root()` and branded descent expose exact node keys composed from that
brand, the retained green allocation identity, and the node start coordinate.
The source producer boundary does not accept arbitrary Rowan nodes. The
coordinate is used only as part of exact Rowan node identity; diagnostic
ranges, spelling and independent traversal ordinals are not used as joins.

Under the existing default-off `yu-hir/shadow` feature, an experimental
lowering entry point records source keys for declaration roots and retained
integer/identifier leaf occurrences while the exact syntax nodes are still
available. `ShadowArtifact` retains a checked source-key-to-`PositionId`
index. Its queries reject foreign HIR artifacts, foreign parses, missing
source evidence and ambiguous keys distinctly. Published keys retain green
allocations and parse identity, not red Rowan nodes; compile-time `Send + Sync`
assertions pass.

Ordinary HIR lowering leaves the source sidecar absent. The shadow lane adds an
iterative syntax walk and temporary maps when source correspondence is
requested. Existing HIR expression, binder, use and inference meanings remain
unchanged. No solver/SCC API consumes this bridge yet.

## Verification and review

Focused checks passed:

```text
RUSTC_WRAPPER= cargo check -p yu-hir --features shadow -j 2
RUSTC_WRAPPER= cargo check -p yu-hir -j 2
RUSTC_WRAPPER= cargo test -p yu-hir --features shadow source_identity_correspondence -j 2 -- --test-threads=1
RUSTC_WRAPPER= cargo test -p yu-syntax source_node_keys_ -j 2 -- --test-threads=1
RUSTC_WRAPPER= cargo test -p yu-hir --features shadow occurrence_index_rejects_ambiguous_zero_width_cst_handles -j 2 -- --test-threads=1
rustfmt --edition 2024 --config skip_children=true --check crates/yu-syntax/src/full_parse.rs crates/yu-syntax/src/lib.rs crates/yu-hir/src/module.rs crates/yu-hir/src/shadow.rs crates/yu-hir/src/lib.rs
git diff --check
```

Coverage: four HIR correspondence tests, two syntax key tests, and one
existing HIR ambiguity test. They cover same-parse clones, a separately
parsed/reused Green root, exact declaration/use joins, repeated uses,
foreign-HIR/foreign-parse rejection, absent sidecars, synthetic occurrences,
and key/map ambiguity handling.

The compiler-referee found no correctness or authority-boundary findings.
The regression auditor found no concrete regression. One low-severity coverage
limit remains: zero-width key collision and shadow-map ambiguity are exercised
in separate tests, not by one `ParsedFile` containing a synthetic duplicate
tree flowing through the entire join. Existing ordinary tests also do not
exercise successful integer lookup, cloned-HIR lookup, or every unsupported
expression family. These are coverage limits, not evidence of a failed join;
the public APIs return `AmbiguousSource`/`MissingSource` rather than guessing.

An initial Cargo invocation failed because the configured sccache returned
`EPERM`; disabling `RUSTC_WRAPPER` made every listed focused check pass. One
Cargo process ran at a time, with two jobs and one test thread. No broad suite,
workspace/core/solver test, performance sample or production differential was
run.

## Gate boundary and remaining work

This is source-occurrence identity plumbing only. It does not establish
callback roles, complete Function membership, `beta`/`Slots(beta)`, typed
paths, owner/receiver/provenance semantics, generalized SCC interfaces,
recursive Q/R identity, or use-time freshening. The existing SCC observer does
not yet consume this correspondence. Soundness, principality, source adequacy
and production cutover remain open.

The syntax crate adds one small `Arc` brand allocation per parsed product.
Source-key traversal/index construction is opt-in; the default HIR path does
not build its identity sidecar or source-node map. No performance measurements
were taken.
