# Shadow structural computation-core arena

Date: 2026-10-06
Baseline: `843f78ccaae0eac1a49838b54cf2a3863aa0b8a9`
Branch: `research/simple-sub-intrusion`
Status: independently reviewed default-off experimental structure; no semantic or production inference authority
Scope: exact approved `apply/step` source only
Review: `compiler_referee` PASS; `regression_auditor` PASS after closing one minor mutation-test coverage finding

## Result

The default-off `yu-core::shadow_derivation` consumer now builds an immutable
eleven-node flat arena from the validated HIR `CapturedCallInput` for exactly:

```text
my apply f = { my step x = f x; step }
```

It borrows the original expression, binder, use, capture, and closure-correspondence
identities. The arena follows the Authoritative nested-block structure:

```text
lambda(f,
  bind(step,
    result(lambda(x,
      pending_call(result(name f), result(name x)))),
    result(name step)))
```

`PendingCall` retains the current application obligations, exact lexical capture
incidence, and unresolved source-view inventory. The result is explicitly
incomplete. It has no inferred endpoint, type, effect, role, profile, slot,
typed receipt, owner/receiver relation, successful invocation, runnable result,
or acceptance judgment. Unsupported source shapes and foreign/mismatched
captured-call identities return no arena. No production HIR, inference route,
expected output, or default feature changed.

## Verification and review

Focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_derivation -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --features shadow
rustfmt --edition 2024 --check --config skip_children=true crates/yu-core/src/lib.rs crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_derivation.rs
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --no-default-features
git diff --check -- crates/yu-core/src/lib.rs crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_derivation.rs
```

The focused integration target passed two tests. Structural mutations for
dropping the argument, replacing captured `f`, or invoking returned `step`
are distinguished. A same-artifact trailing-whitespace case independently
tests exact-source rejection; a separate foreign-artifact case tests branded
identity rejection. Existing pending inventories are compared before/after.

The compiler-referee found no semantic-boundary or arena-invariant findings.
The regression auditor found one minor test that masked the exact-source gate
with foreign identity rejection. The test now uses its own validated input for
the whitespace variant; the regression delta review closed that finding.

Verification used at most two Cargo build jobs and one test thread. No broad
suite or performance measurement ran. The arena is fixed-size for this one
candidate and borrows identities rather than cloning or minting them.

## Remaining gates

This is source-indexed structural core construction, not a typed computation
derivation or old-infer differential. The Function call-view, typed capture,
profile, receipt, source admission, complete-row nonemptiness, semantic
discharge, soundness, principality, source adequacy, production conformance,
and cutover remain open. The core tree can serve as an input to future source
registration and theorem work, but supplies none of those missing judgments.
