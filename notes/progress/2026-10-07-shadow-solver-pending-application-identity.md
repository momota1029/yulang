# Shadow solver boundary: pending application identity

Date: 2026-10-07
Baseline: `39f00ce1eeb84a71df333c4cb10771137c95491e`
Status: default-off structural slice and HIR-to-core-to-solver differential join implemented, focused-verified, compiler-referee and regression reviewed
Authority: user's authorization for shadow/experimental identity and evidence plumbing
Semantic authority: none added
Implementation: `crates/yu-solver/src/lib.rs`, gated by `shadow-f5`; test-only `yu-core/shadow` dependency for cross-layer identity coverage
Review: compiler_referee PASS with one test-only direct-use identity coverage gap repaired and focused test rerun; regression_auditor PASS on the source-core differential addition

## Slice

`ConstraintBatch` now keeps a `PendingApplicationOccurrence` sidecar for each
retained Apply encountered on the opt-in `shadow-f5` collection route. Each row
retains the exact HIR occurrence IDs for the Apply, callee and argument, plus
the existing direct `NameResolution` when the operand itself is a Name. An
explicit `ApplicationTypingRuleUnresolved` state prevents this identity record
from being mistaken for an inferred call judgment. The walk is iterative and
borrows the retained HIR tree; it does not reconstruct source IDs.

The collector's existing outcome is unchanged. Apply bodies remain
`CollectedBodyStatus::Error`; the sidecar emits no application facts, Lambda
recipes or operand components. Existing definition-root components remain
present. Types, effects, Function ports, callable roles, annotations-to-port
mapping, `beta`/`Slots(beta)`, call-view registration, source admission and
semantic acceptance are not inferred here. The HIR-only collector also has no
shadow `UseId`, so this row retains exact Name occurrence/resolution instead
of synthesizing one.

The focused differential test starts from one `ParsedFile`, sends it through
the opt-in HIR lowering, the production lowering boundary and the shadow
artifact, then joins each pending solver row's Apply/callee/argument HIR
identity to the corresponding source-core positions. It also joins each
direct callee to the source `UseId` and Binder and distinguishes the two
nested call uses. Production refusal is checked by error kind; the test does
not certify exact diagnostic text or span. Its structural joins are not
inferred-result parity.

The differential test now carries that join through `RawStructuralArena` as
well. For each pending solver row it locates the exact source Apply node,
checks the raw pending registration's application and `UseId`, then confirms
that the HIR parameter identity, source Binder and retained Lambda parameter
declaration are the same syntactic owner. The new `yu-core` dependency is
dev-only and enables only its existing `shadow` facade. This closes structural
correspondence for the bounded `my apply x = x(x 1)` fixture; it does not infer
that the binder is semantically applicable as a function or supply any typed
port/profile/receipt evidence.

## Review and verification

The compiler referee inspected the feature boundary, source identities,
nested traversal, collection refusal, root bookkeeping, test strength and
cost. No blocking or major findings remained. An earlier minor test gap compared
`NameResolution::Parameter` through its weaker equality implementation, which
checks only the ordinal. The primary repaired the assertion to compare full
`HirParameterId` identity in both outer and nested callee cases; this changes
test validation only, not the sidecar implementation. The follow-up
compiler-referee review found one additional minor test gap: same-binder nested
calls did not assert that the raw registration retained the same `UseId` and
application expression as the solver row. Those exact identity assertions
were added and the focused test rerun.

Checks run:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 shadow_application_collection_remains_unsupported_without_facts -- --test-threads=1` — 1 passed; 449 filtered. The integration-test filter selected 0 tests.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver` — passed with the feature off.
- `git diff --check -- crates/yu-solver/src/lib.rs` — passed.
- `rustfmt --emit stdout --edition 2024 --config skip_children=true crates/yu-solver/src/lib.rs`; changed lines inspected against the formatted output. Existing unrelated formatting drift was preserved.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential pending_solver_applications_join_exact_shadow_call_and_use_occurrences -- --test-threads=1` — 1 passed.
- Same focused test rerun after checking the raw `UseId` and application-expression joins — 1 passed.
- `rustfmt --edition 2024 --check --config skip_children=true crates/yu-solver/tests/shadow_f5_differential.rs` and `git diff --check` — passed.

No broad suite, inferred-result comparison, performance sample, Oracle run,
production routing change or Git mutation was made. The test-only dependency
adds `yu-core` with `shadow` to `yu-solver`'s dev dependencies and the matching
Cargo.lock entry. The new
sidecar is not successor/current-infer parity. Ordinary application typing,
source adequacy, soundness, principality and production cutover remain open.
