# Shadow pending Apply to endpoint-skeleton crosswalk

Date: 2026-10-08
Baseline: `2a767bed13df5c31930c6b773d827b8c94d6c9e3`
Status: implemented test-only M1 structural differential; compiler-referee PASS
Authority: user-authorized default-off shadow identity/evidence plumbing
Semantic and production inference authority: none

## Change

The existing solver differential now joins each retained pending Apply row to
the raw core endpoint-skeleton view through the shared parse artifact and exact
HIR occurrence position. It checks the source Apply, callee and argument
identities, all eight ordered structural bookkeeping labels, the original
seven application premises, and the required direct-callee source registration.

For nested `x(x 1)` and grouped `x (x 1)`, the differential also checks that
solver-retained outer/inner order agrees with the actual expression topology.
The outer argument-value/effect labels remain keyed to the outer Apply, while
the inner whole-Apply-value/effect labels remain keyed to the inner Apply.
Every application stays `ApplicationTypingRuleUnresolved`; solver counters
remain unchanged.

The labels are source-structure bookkeeping only. No typed endpoint, path,
Function role, `beta`/`Slots(beta)`, call view, contribution, shared `xi`,
admission or inference result is inferred. Production HIR, constraints,
solver behavior and ordinary application refusal did not change. This is a
cross-layer structural differential, not old-infer semantic parity.

## Review and verification

Independent compiler-referee M1 review passed with no findings. Reviewed file
SHA-256:

```text
crates/yu-solver/tests/shadow_f5_differential.rs
3d079a7a0f54fdd0d24935d73dcc26c9617df3f0de3299189696c9e914c913e0
```

The review covered the changed endpoint crosswalk, premise preservation,
outer/inner discrimination and unresolved-state assertions. It did not certify
production semantics or inference correctness.

Focused checks:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-solver/tests/shadow_f5_differential.rs
git diff --check -- crates/yu-solver/tests/shadow_f5_differential.rs
```

The differential target passed 4 tests. One Cargo process ran with two build
jobs and one test thread; no benchmark or resource sample was taken. No broad
suite was run.

## Remaining boundary

Typed `p0`, callable role/entry, source-produced `beta` and `Slots(beta)`,
complete contribution and receiver invocation, original shared `xi`, and
`ORIGINAL_ASSOC` remain unresolved. Production cutover remains forbidden until
soundness, principality and source adequacy close. The next implementation
slice should consume only a theorem/rule premise that has been independently
adjudicated; the next theory action remains independent original
slot/contribution introduction.
