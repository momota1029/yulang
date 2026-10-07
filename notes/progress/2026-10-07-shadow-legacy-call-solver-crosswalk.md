# Frozen legacy application to successor shadow solver crosswalk

Date: 2026-10-07
Status: implemented test-only shadow differential; regression-auditor review passed
Yulang3 baseline: `7423c12ac1269049a9159b5bb4355f761991d19c`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: user-authorized default-off shadow lane; Oracle contributes historical identity evidence only

## Result

Added `crates/yu-solver/tests/shadow_legacy_local_application_provenance.rs`
to join the recorded Frozen Oracle old-infer application capture to the same
current source occurrence, shadow HIR local-binding sidecar, Core pending
projection, and collected/solved application row for:

```text
my apply f = { my step x = f x; step }
```

The test keeps the historical `ExprId`, `RefId`, `DefId` and displayed scheme
opaque. It checks the captured old application and callee spans after removing
the documented 20-byte implicit prefix, then joins those bytes to the current
Apply, captured outer `f`, local `step` binding, inner `x` parameter, returned
`step` use, and distinct callee/argument Uses. The same identities are traced
through the structural Core projection and the single pending solver row
before and after solve.

The ordinary HIR route still reports `UnsupportedExpression`; collection has
no semantic facts; the row remains
`ApplicationTypingRuleUnresolved`; all seven source-call and source-view
premises remain present. This is an identity and refusal-boundary differential,
not inferred-type parity, source acceptance, or semantic validation of the
historical implementation.

## Review and verification

An independent regression auditor reviewed the exact test and direct
source/HIR/Core/solver dependency cone. No blocking, major or minor findings
were reported. The review did not reproduce the historical Oracle run or
certify its semantic rules.

Focused verification passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=/tmp/yulang-legacy-shadow-crosswalk-target \
  cargo test --locked -p yu-solver --features shadow-f5 \
  --test shadow_legacy_local_application_provenance -- --test-threads=1
# 1 passed

rustfmt --edition 2024 --check crates/yu-solver/tests/shadow_legacy_local_application_provenance.rs
git diff --check
```

Artifact SHA-256: `91452cb80f3cd51a9317779825973e4e077d6c0ccce50eac03d211022ec1eb42`.
No production code, dependency, manifest, semantic premise or default inference
path changed. No broad test suite or performance sample was run.

## Remaining gates

The source producer for original `beta`/`Slots(beta)`, typed `p0`, owner and
complete invocation contribution under one original `xi=(nu,K,D)` remains
open at `ORIGINAL_ASSOC`. Q/R successor correspondence, source adequacy,
soundness, principality and production cutover remain open. The current task
record `tasks/current.md` was not edited because its staged and worktree
versions contain large conflicting changes; the exact durable task-status
synchronization remains deferred until that index ambiguity is adjudicated.
