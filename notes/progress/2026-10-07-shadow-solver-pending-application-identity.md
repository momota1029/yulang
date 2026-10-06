# Shadow solver boundary: pending application identity

Date: 2026-10-07
Baseline: `39f00ce1eeb84a71df333c4cb10771137c95491e`
Status: default-off structural slice implemented, focused-verified, compiler-referee reviewed
Authority: user's authorization for shadow/experimental identity and evidence plumbing
Semantic authority: none added
Implementation: `crates/yu-solver/src/lib.rs`, gated by `shadow-f5`
Review: compiler_referee PASS; one test-only parameter-identity weakness repaired and focused test rerun

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

## Review and verification

The compiler referee inspected the feature boundary, source identities,
nested traversal, collection refusal, root bookkeeping, test strength and
cost. No blocking or major findings remained. A minor test gap compared
`NameResolution::Parameter` through its weaker equality implementation, which
checks only the ordinal. The primary repaired the assertion to compare full
`HirParameterId` identity in both outer and nested callee cases; this changes
test validation only, not the sidecar implementation.

Checks run:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 shadow_application_collection_remains_unsupported_without_facts -- --test-threads=1` — 1 passed; 449 filtered. The integration-test filter selected 0 tests.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver` — passed with the feature off.
- `git diff --check -- crates/yu-solver/src/lib.rs` — passed.
- `rustfmt --emit stdout --edition 2024 --config skip_children=true crates/yu-solver/src/lib.rs`; changed lines inspected against the formatted output. Existing unrelated formatting drift was preserved.

No broad suite, current-inference comparison, performance sample, Oracle run,
manifest change, production routing change or Git mutation was made. The new
sidecar is not successor/current-infer parity. Ordinary application typing,
source adequacy, soundness, principality and production cutover remain open.
