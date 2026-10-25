# LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r3 outcome

Status: **ACCEPTED / CLEAN within the frozen formal-obstruction scope.** The current Call transition relation admits a reachable, typed View-wrapped Force head with no successor. This identifies a formalization obstruction; it does not establish source reachability or close the parent semantics/type-inference goal.

## Frozen claim and evidence

- r3 contract: `tasks/agent-loop/sprints/call-progress-obstruction-20261025-r3.md`, SHA-256 `1a32aed55bf4db354e7d4ce69d08f8bfe5c596743f359f771fcd26feade98e71`.
- Baseline: `2ed4a20a6`; final review activation checkpoint: `3d044faff`.
- P reachability source: `notes/theory/lean/YulangClosure/CallViewedForceReachability.lean`, SHA-256 `ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c`.
- Q no-successor source: `notes/theory/lean/YulangClosure/CallViewedForceStuck.lean`, SHA-256 `71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9`.
- Composition source: `notes/theory/lean/YulangClosure/CallProgressObstruction.lean`, SHA-256 `8dc8b1b72c952dc45c431fb965a438b700dc86902a68b8d77a3de0b7d47858b7`.
- Exact signature/axiom query source SHA-256: `c249ae83737295e01aab6c5f6397f1367c10f907ba25f22c6ebcbed0b269905d`.
- Accepted finite-typing dependency outcome SHA-256: `f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d`.

P constructs the exact Call term and five real transitions to the View-wrapped Force head. Q proves that an arbitrary state with the exact active head has no successor in the present `CallControlStep` relation, with no extra premise. Composition applies accepted finite-prefix typing to P's witness and combines it with Q. The outer typed suffix result remains distinct from the target's `Original.Ty` result index.

## Serialized Lean verification

Receipt: `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r3-verification.jsonl`, SHA-256 `8b12d15870fe7334775d2f18ffb0f274a4900b91028f24abad7a983f7f2ac380`.

Four invocations ran serially in contract order: P, Q, composition, and exact signatures/axioms. Every invocation exited 0 and did not time out. The receipt records complete stdout/stderr, inputs, and outputs. Output hashes:

| Module | `.olean` | `.ilean` |
|---|---|---|
| P | `b8ab2f039ef0601d7744cb8849649c798b436ad59b8996d93344af7b4346a205` | `79ccd5da77d41818cab9490addc81c20c60932a8fae05f980fc01ca88ed313ea` |
| Q | `955c632892cdd1fdd04770c1847a7e1e68d6f065b19c691f6f13b586609a3f0b` | `fe9071b81ece5fd4ac03d2cc0ebbe8535518bc36378f8494641e53dd3308b5af` |
| Composition | `bf3c046c24bdb9f23711a98b72153e9e22c219c542ac66ed917b51d11ff0a09b` | `1a01e6ffe257375dce224b8bfa13ba134dff0a7bf8f269533cf8e2f1719ecfa3` |

P depends on no axioms. Q, composition, and accepted prefix preservation use only `[propext]`; all are within the contract's allowed `[propext, Quot.sound]`. Query stdout SHA-256 is `e8068e25a88729a6882f54b99e7de048f07b0e7775aab7ca3dbf8e4cb649b4b5`.

Receipt row 2's UTC wall-clock end sample precedes its start sample by 0.239326 seconds. A contemporaneous system journal entry at `2026-10-25T12:58:58.219473+09:00` reports `Clock change detected`; the monotonic elapsed measurement is positive (`0.3064112749998458`). The receipt was preserved unchanged. The wall-clock samples cannot measure Q's elapsed duration.

## Independent review and adjudication

Fresh nonauthor compiler referee `/root/call_progress_obstruction_r3_review` returned **CLEAN**, with no blocking, major, or minor finding. The reviewer independently checked the exact propositions against primary definitions, all 28 transition constructors, source/output/dependency pins, the complete receipt and query, and the restricted scope. Review report: `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r3-review.md`, SHA-256 `0ca9844cfe0a1ff4ed897431eeb02b5c53efc6877f040dd27b4c5bfcce181c7c`.

The primary accepts the exact frozen claim based on the successful serialized checks and CLEAN independent review. The reviewer's timestamp observation is retained as an evidence qualification; it does not change the exit codes, monotonic duration, hashes, or theorem conclusions.

## Limits and remaining goal

This does not repair the missing viewed-Force transition. It proves a gap in the formal relation as currently defined. It does not prove source/frontend reachability, native correspondence, original Call A/B, inference A/B, semantic approval, or production readiness. These parent gates remain OPEN. Three UNKNOWN reservations remain quarantined. Sixteen unrelated untracked Force artifacts were left untouched.

Luna remains sole Git integrator. The verification and review milestones were committed and pushed on `research/simple-sub-intrusion`; this outcome and final state update are the adjudication checkpoint. No unused sprint budget carries forward.
