# r17 revision 9 — private v1-mode dispatch seam

This is an exact-path lease amendment to r17 rev8. Goal, semantics, reviewed design, source-linked success predicate, parent proof status, and remaining resource allocation are unchanged. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0.

Frozen design: `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md` SHA-256 `276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54`. r17 rev8 adds the explicit `CandidateInference` v1 research entry in `shadow_apply.rs`. Before edits, the implementer identified the minimal batch dispatch seam: `ConstraintBatch::collect_candidate_mode_scoped` in `lib.rs` constructs `candidate_source::Plan`, so a separate opt-in v1 mode cannot reach the collector without changing existing `scoped_experiment` behavior.

## Added exact write lease

Add `crates/yu-solver/src/lib.rs` to the same implementer lease solely for:

- a private v1-mode field/constructor on the minimum batch input;
- the minimal forwarding of that mode to `candidate_source::Plan`.

The v1 flag is independent of `scoped_experiment`. Existing `solve` and `solve_scoped_experiment` always pass v1-disabled. Only the explicit v1 research entry can select it. No Action meaning, ordinary collection behavior, default, production API, global toggle, or unrelated code changes.

The full exact lease is now `candidate_source.rs`, `candidate_effect.rs`, `shadow_apply.rs` (explicit v1 entry and minimum setup only), `lib.rs` (private v1 dispatch field/constructor and forwarding only), and additive `tests/candidate_operation_catch.rs`. All source-linked `h_arg`/q/m0/FieldBoundV1, native typed drain, transaction rollback, no-cast, and no-runtime-input requirements remain mandatory. If any further path is needed, stop for a fresh lease delta before writing it.

## Resources and verification

No reset or additional time. The existing 420-second code allocation includes this `lib.rs` seam. Remaining after code: independent compiler review 180 seconds and one focused solver run/integration/state 240 seconds. Astra 0. Fresh compiler review covers the whole lease before the focused solver test. The ordinary entry stays v1-disabled; a test or design pass does not close the parent theorem or Phase R.
