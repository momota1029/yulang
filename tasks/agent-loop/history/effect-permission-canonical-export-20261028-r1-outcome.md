# EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1 outcome

Disposition: **CLOSED_INCOMPLETE**. No parent, source/native, A/B, effect-hygiene, principality, termination or production gate is closed. The sprint was authorized as a continuation of the user's unchanged inference/executor goal.

## Frozen evidence

Contract: `tasks/agent-loop/sprints/effect-permission-canonical-export-20261028-r1.md`, SHA-256 `70a69a66a9367114a70970d73825942bfebfc08a2143b7288f057b76088aaf4b`.

Rust sources: `candidate_effect.rs` SHA-256 `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1`; `candidate_scheme.rs` SHA-256 `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`. Final Rust handoff `tasks/agent-loop/inbox/effect-permission-canonical-export-rust.md`, SHA-256 `ea9d9e74f383adefb120abcc619c8395404e20f41d0f1acc71764df0fba20d8e`.

Both released feature-correct focused Cargo invocations compiled and executed, then exited 101. Run 1: 60.14s, 1,664,404 KiB peak RSS, zero swaps; strict r/q observation failed with `[(19,19),(21,21)]`. Run 2: 6.40s, 1,116,748 KiB peak RSS, zero swaps; owner case failed the strict r!=q condition with `[(21,21),(23,23)]`, and delegated site join failed 0/1. Combined wall 66.54s; both invocation slots are spent. Raw receipts are retained under `/tmp/yulang-effect-permission-canonical-export-20261028-r1/rust-target/` and hashes are recorded in the frozen handoff.

The capture-row recorder reads the actual materialized graph `RowKey::Effect`, and the owner join compares each export to its own `Origin.concrete`. These checks were reached before the r=q assertion stopped the owner test. The delegated event records annotation position while the strict comparison expects nested effect-row position; the symbolic test stops there before later tail/port assertions. The frozen Rust handoff contains stale intermediate pending-run statements; the authenticated final disposition here supersedes them. No source or expected-output behavior was changed.

Lean source: `notes/theory/lean/YulangClosure/FormalPermissionExportWitnessNative.lean`, SHA-256 `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1`; final proof handoff `tasks/agent-loop/inbox/effect-permission-canonical-export-proof.md`, SHA-256 `1bbbdbc3b45936ca842259203c577623c80b05619e88fb5e1cd37079ff222140`. The sole pinned Lean 4.35.0 invocation exited 0 in 6.38s, peak RSS 968,532 KiB, zero swaps. All ten declaration types and transitive axiom sets were audited:

- No axioms: `recorded_rows_are_identity`, `run1_expected`, `run2_expected`, `run1_snapshot_rows`, `run2_snapshot_rows`.
- `[propext, Quot.sound]`: `run1_decode`, `run2_decode`.
- `[propext]`: `changed_q_rejected`, `wrong_concrete_rejected`, `same_wrong_set_both_rejected`.

These remain conditional mathematics. Only diagnostic row-pair lists are instantiated; decode theorems require successful `decodeValue` and matching retained entries. Actual native extraction/snapshot authenticity, source-wide realization and nontrivial r!=q remain OPEN. Existing decoder and its audited dependencies are unchanged.

## Independent review

Fresh non-author read-only integrated review: `tasks/agent-loop/inbox/effect-permission-canonical-export-final-review.md`, SHA-256 `4961ea42bb3ad09579ecf0bff2899af1b2d229cb4067d86dfcbc3d9508c687d8`; prior Rust-only review remains at `tasks/agent-loop/inbox/effect-permission-canonical-export-review.md`, SHA-256 `61f6a21373c352533bfd772bb81711dc2968aa7012548d11f40f4dc3a97d7523`.

Integrated verdict **CLOSED_INCOMPLETE**. The required nontrivial r!=q source observation is absent and q→r has no effect on either observed identity pair. The delegated-site recording uses annotation position instead of nested effect-row position, causing the strict join failure and allowing same-annotation rows to be grouped too broadly. The reviewer verified all Rust and Lean handoff hashes/receipts; all 32 Lean frozen-manifest entries matched. The three independent capture/concrete joins are soundly placed but do not close the required successful source evidence.

For the required falsifiers: a changed q is rejected against fixed captured-row data (but q→r is unexercised at r=q); identical wrong export concrete sets are rejected against fixed per-origin metadata; wrong owner wrappers and omitted origins are excluded by exact owner/count checks; swapped ports are excluded by per-origin source/path and node identity. Some later explicit swap assertions were not reached, and no mutation tests ran. Lean mutation results are fixed-input mathematics, not native observation. The receipt details each conclusion and axiom audit.

## Next seam

Exact native extraction and snapshot authentication for the same Context/State/code/entries/node inputs remain the first source-to-observation bridge. The next bounded work must find an authentic ordinary-source construction with r!=q, preserve the actual materialized row as independent evidence, fix delegated recording to retain the nested row site plus enclosing occurrence/path, and complete the strict per-origin capture/export/port joins. Preserve the checked decoder and all frozen failure artifacts. Any new Cargo or Lean execution requires a new sprint contract and fresh exact leases; all attempts in r1 are spent.
