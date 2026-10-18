# r17 revision 8 — exact v1 research entry lease

This is a lease-only amendment to r17 rev7. The goal, source identities, reviewed design, success predicate, proof status, resource cap and remaining allocation are unchanged. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0.

Frozen semantic design: `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md` SHA-256 `276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54`. The source-linked `h_arg`, q, m0, FieldBoundV1, q-Allowance edge, ordinary typed drain and transactional rollback remain mandatory. The prior exact code lease was incomplete because the reviewed design requires an explicit opt-in research entry.

## Added exact write lease

Add `crates/yu-solver/src/shadow_apply.rs` to the existing implementer lease solely for:

- one explicit `CandidateInference` v1 research-only entry;
- the minimum private setup/dispatch path needed to select that entry and enable the reviewed v1 source constructor/consumer.

The ordinary `solve` entry and production/default inference remain v1-disabled. No global toggle, default behavior change, public behavior widening, generic preflight bypass, or unrelated refactor. Calling the v1 entry is not source evidence or a license. It must still derive the exact retained `h_arg` from the source path and pass all reviewed checks.

The existing lease remains on `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_effect.rs`, and additive `crates/yu-solver/tests/candidate_operation_catch.rs`. No other path is writable. If the minimal entry cannot be implemented within this exact path, stop and report the owner; do not expand further. The fresh compiler review covers this entry together with the exact source/consumer diff before one focused solver test.

## Resources

No reset or added time. The 420-second code allocation from rev7 includes this entry lease. Remaining after code: compiler review 180 seconds plus one focused solver run/integration/state 240 seconds. Astra remains 0. The previous revision is immutable.
