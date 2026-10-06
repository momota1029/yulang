# Shadow call-source occurrence crosswalk

Date: 2026-10-06
Baseline: `d07fa561c15e66875aefb4092827a7030e736a81`
Status: default-off experimental source plumbing; independently regression-reviewed with no blocking or major findings
Scope: read-only accessor over retained `Form::Apply` occurrences
Implementation authority: authorized shadow identity/evidence plumbing only; no call semantics

## Change

`Skeleton::application_source_occurrences()` lazily enumerates retained Apply
expressions as `ApplicationSourceOccurrence`. Each view exposes the existing
artifact-branded expression ID, raw CST position ID, source form, callee
expression ID and argument expression ID. It creates no new call ID, role,
typed path, `J_call`, `beta`/profile, receiver, receipt, owner or evidence.
Existing per-call pending premises and production inference routing are
unchanged. `yu-core` re-exports this HIR-owned view only through its shadow
facade.

The accessor scans the retained expression arena when iterated, uses constant
auxiliary storage, and clones one existing `Arc` brand per yielded expression
ID. It is an experimental source crosswalk, not a hot-path solver operation.
No performance measurements were run.

## Focused coverage

Three focused HIR tests check:

- the approved nested captured-function candidate, including its callee and
  argument uses and unchanged pending call/capture premises;
- inner and outer calls in a grouped composition expression;
- both `MlArgument` and `CallTail` source forms, exact source ranges, and
  foreign-artifact rejection.

The independent regression review inspected the four leased paths, found no
blocking or major issue, and confirmed the pending premise inventory and
production route are unchanged. It noted no direct mixed flat-chain/zero-call
iterator test; the iterator has no shape-specific branch, and existing tests
cover the underlying flat-chain projection.

## Verification and limits

Passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_call_source_occurrences -- --test-threads=1
rustfmt --check --edition 2024 --config skip_children=true crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_call_source_occurrences.rs crates/yu-hir/src/lib.rs crates/yu-core/src/shadow.rs
git diff --check -- crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_call_source_occurrences.rs crates/yu-hir/src/lib.rs crates/yu-core/src/shadow.rs
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --features shadow
```

The focused test ran 3 tests with 54 filtered. The two `yu-core` checks cover
default features and the shadow re-export. No broad suite or Frozen Oracle
execution was used. This crosswalk establishes no source-generation O,
admission, capture-attachment A, typed call relation, soundness, principality,
source adequacy or production conformance.
