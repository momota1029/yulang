# r17 revision 10 — bounded source-linkage implementation continuation

This resource amendment preserves the frozen r6 design, r9 exact write paths, fixed goal, success predicate, parent theorem quantifiers, and review/test gates. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0. The existing partial v1-entry/mode plumbing is preserved as unreviewed work; it is not counted as a source acceptance or consumer milestone.

Frozen design: `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md` SHA-256 `276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54`. Exact current code paths are unchanged: `candidate_source.rs`, `candidate_effect.rs`, `shadow_apply.rs` (explicit opt-in research entry/minimal setup), `lib.rs` (private v1 mode/Plan forwarding), and additive `tests/candidate_operation_catch.rs`. No other paths are authorized.

## Reconciled resources

No reset. Previous total cap 4560s, charged/reserved 4140s, remaining 420s. Add one 1200-second Luna code continuation: new cap **5760s**, charged/reserved **4140s**, remaining **1620s**. The new 1200s is reserved solely for completing the exact source-linked producer/consumer. Preserve the existing independent compiler review 180s and focused solver run/integration/state 240s. Astra **0**. No automatic renewal.

## Required integrated milestone

Complete the retained `h_arg` derivation from `LocalSource`: exact `u_ping` in the same catch scrutinee, same resolved operation declaration and arm, lexical continuation binder ID `k`, the `k response` Apply whose callee resolves to that binder, the actual argument occurrence resolving to the response definition, and its body operation `u_outer`. Carry this derivation in the source Action and through q/m0/FieldBoundV1. Match the actual lower native `AnnotationMember` to that same `u_outer` source derivation; do not infer it from operation origin, family, or type alone. Store the q-owned upper, enqueue its ordinary typed native edge, drain it, and expose a receipt only on successful completion with record/edge rollback on failure.

The `operation_v1_catch_source(..)->false` placeholder cannot be changed to unconditional `true`; admission must be backed by the complete exact derivation. Keep normal solve and solve_scoped_experiment v1-disabled. The r6 source-linkage and native consumer invariants remain binding.

## Stop and verification

Implement the complete static Phase-S vertical as one coherent slice, not helper-only milestones. If any new semantic decision or path beyond the exact lease becomes necessary, stop that seam for Luna. Once the integrated code and additive source-driven negative controls are frozen, stop the writer; a fresh compiler reviewer inspects the exact diff; repair any blocking issue; only then run the one focused solver test. Runtime Phase R and full parent theorem remain open regardless of this milestone.
