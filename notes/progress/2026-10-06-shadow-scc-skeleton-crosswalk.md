# Shadow SCC to skeleton identity crosswalk

Date: 2026-10-06
Status: M1 shadow-only implementation; compiler-referee reviewed with no findings
Baseline: `b26087ce26bc2e77f41709a1e7b58bc4c73c2db6`
Authority: current F0–F2 topology plus existing default-off shadow identities
Implementation authority: structural correspondence only

## Result

The current `SccTopology` observer can now perform checked borrowed lookups
from an already represented current definition/use source identity into an
existing shadow Lambda/Bind/Use identity. The HIR crosswalk builds one index
over the bounded skeleton and returns explicit absence for source positions
that have no structural projection. Solver joins retain collection, HIR,
parse, position and skeleton identity checks; they do not match by spelling,
path, ordinal or range.

The change does not assign nested SCC ownership, alter the current SCC graph,
create a generalized interface, infer dependencies, discharge pending
premises, or route production inference. SCC membership/order and production
behavior remain unchanged.

## Verification and review

Focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow_source_core -- --test-threads=1
# 12 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-scc-observer shadow_scc_observer -- --test-threads=1
# 8 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-hir -p yu-solver
rustfmt --edition 2024 --config skip_children=true --check crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_source_core.rs crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
git diff --check -- crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_source_core.rs crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
```

The independent compiler-referee review covered the full four-file diff,
F0–F2 authority, lookup/validation paths, feature gates and relevant tests. It
found no blocking, major or minor issue. Broader suites, semantic parity and
successor SCC/generalized-interface correspondence remain unverified. One
Cargo process ran at a time with two build jobs and one test thread; no
performance measurements were taken.

## Changed paths

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/tests/shadow_source_core.rs`
- `crates/yu-solver/src/shadow_scc.rs`
- `crates/yu-solver/src/tests/shadow_scc_observer.rs`

The primary owns task/theory-record synchronization and Git integration.
