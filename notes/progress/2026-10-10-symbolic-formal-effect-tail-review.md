# Review: symbolic formal effect tails

Date: 2026-10-10
Reviewed artifact: `symbolic-formal-effect-tail-integration.md` and its three leased implementation/test files
Baseline: `e62a4a07f`
Reviewer: independent compiler referee
Mode: M1 bounded Simple-sub source-inference slice

## Finding and closure

The first review found one major issue: formal annotations and whole-definition
annotations allocated the same named effect tail in separate maps. This broke
the approved paired-formal binding environment. The repair makes annotation
contexts use the same definition-scoped effect-name map as formals while
preserving operation-local maps.

The new whole-annotation/formal regression avoids incidental body flow by
returning an unrelated pure callback, then injects a concrete lower into the
shared tail and verifies that it reaches the captured returned Function effect
fiber. A rollback regression verifies a failed whole-annotation route preserves
the preexisting formal-tail mapping. The delta review closed the major finding
and found no new blocking or major issue within this scope.

## Verification and limits

The primary reran the owning filters serially with both candidate features,
offline, `-j 2`, and one test thread:

- `cargo test ... --lib formal_and_whole_annotation` — 1 passed.
- `cargo test ... --lib formal` — 9 passed.
- `cargo test ... --test candidate_annotated_function_formals` — 10 passed.

The full commands, timeout and `RUSTC_WRAPPER=` setting are recorded in the
[implementation delivery](2026-10-10-symbolic-formal-effect-tail-integration.md).

Uninspected: concrete formal `[E]` construction and subtraction, closed-empty
formal annotations, contextual propagation/replay, complete Call, public owned
schemes, default entrypoint migration, and F5 replacement. The review is not a
full hygiene or soundness/principality certification.
