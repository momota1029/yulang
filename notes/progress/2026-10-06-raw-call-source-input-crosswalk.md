# Raw Call source-input crosswalk

Date: 2026-10-06
Baseline: `1868c9bee71cf6759b7d85542ab7374d1078ab7d`
Commit: `55009b27f` (shadow implementation; shared-record synchronization follows)
Status: compiler-referee-reviewed shadow-only reference plumbing
Authority: user-authorized successor shadow lane; no semantic or production authority

## Result

`RawCall::source_use_input` now carries the existing HIR `SourceCallUseInput`
for immediate resolved `Use` callees. Core validates the exact Apply, callee,
argument, binder, use occurrence, source position and retained parameter
annotation incidences before publishing `RawStructuralArena`. Duplicate joins
and failed identity joins reject the whole optional arena. Grouped and computed
callees keep their ordinary raw Apply/pending representation and receive no
source-use input association. Existing ordered pending rows and capture joins
are unchanged.

This is an HIR-to-core reference crosswalk. It constructs no formal
classification, `F_cb`, `beta`/`Slots(beta)`, typed path, owner/receiver,
contribution, receipt, admission, protection or solved result. Empty annotation
iteration establishes neither absence nor completeness. All unresolved call
semantics remain premises for later work.

## Verification and review

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_raw_structural_inventory -- --test-threads=1` — 6 passed.
- `rustfmt --edition 2024 --config skip_children=true crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_raw_structural_inventory.rs` — passed.
- `git diff --check` — passed.
- Independent compiler-referee review: PASS, no findings. It checked exact identity joins, grouped/computed callee exclusion, annotation association, pending order, capture behavior and atomic construction.
- Production isolation: `yu-core` shadow modules are feature-gated; default features remain empty. No production inference routing changed.
- One focused Cargo invocation, two build jobs, one test thread; zero performance samples. Broad suites, feature-off build, semantic inference parity and production conformance were not checked.

## Remaining gate

The original source-owned contribution typing and association judgment remains
open, as do exhaustive attachment/licensing inversion, complete profile,
independent admission, soundness, principality, source adequacy and production
cutover. This plumbing gives a future producer the already validated source
references without supplying those rules.
