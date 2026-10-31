# R12 outcome — EFFECT-PERMISSION-HELPER-FRAMES/20261029-r12

**Status: `CLOSED_COMPLETE_CONDITIONAL`.** This closes the bounded transcription and R11 application packet. It does not close a Rust execution, native, original-parent or production gate.

## Frozen result

- Contract SHA-256: `7c7573abd1778414300f78b7b0271d5d3479b7f3e9c296a343bfb51c6102ecd4`.
- Input manifest SHA-256: `057f4dafaa51ab8343a090de4f789adf2bce1d4e8db08d630551cb1d013f9a8c` (133 entries).
- Source handoff: `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-source.md`, SHA-256 `e270f74164f29816f5823687afc431617843b49ae7e28ffb06bc942d5a8e385b`.
- Accepted proof artifact: `tasks/agent-loop/history/artifacts/FormalPermissionHelperFrames-r12.lean`, 15,691 bytes, SHA-256 `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-helper-frames-r12-proof.md`, SHA-256 `63fde25dc4aec460338d127ef6e2c625d2016e9b60c17860a45b4e89c1c63b55`.
- Amendment 01 SHA-256: `94661003e31471dd4bdfcf1e96b0e789a9441e2d7c69bdb009f668e7f443f868`.

## Verification and review

Audit 1 was preserved: Lean build failed before theorem audit because of record-update syntax and the reserved identifier `prefix`; it emitted no theorem types or axiom reports. The failure was not a mathematical counterexample.

The sole authorized repair flattened three record updates and consistently renamed `prefix` to `priorPermissions`. Audit 2 used a fresh 16-file project copy with no `.lake`, the pinned Lean 4.35.0 toolchain and all nine public roots. It exited 0 in 15.51 seconds, with maximum RSS 973,036 KiB. The combined audit wall time was 28.43 seconds. The complete plan, copy receipt, raw stdout, stderr, status and resource output are under `/tmp/yulang-effect-permission-helper-frames-20261029-r12/`; frozen audit receipt SHA-256 is `2e956b992197d52f70f956b13997bbd9559938211edbee1121c3a43520e16168`.

All nine declarations have complete printed types and transitive axiom audits:

| Declaration | Transitive axioms |
|---|---|
| `operation_preserves_allocator` | none |
| `operations_preserve_allocator` | none |
| `nonempty_operations_frame` | none |
| `reservation_projection` | `propext` |
| `permission_append_delta` | none |
| `concrete_port_prefix_delta` | none |
| `ordered_concrete_port_delta` | none |
| `tree_frames_from_operations` | `propext` |
| `exact_tree_r9_from_operations` | `propext`, `Classical.choice`, `Quot.sound` |

Fresh nonauthor review: PASS for the conditional operation transcription and same-witness R11 application; zero blocking, major or minor compiler-correctness findings. Review handoff SHA-256: `2d3c0d6f4176757ee38c26ecf4efc8dfb6e453775b7760a26c0aa03f347c0dde`.

## Exact accepted boundary

The Lean model transcribes the listed field updates, proves allocator preservation for its `HelperOp` programs, separates the designated permission append from frames, and derives local `HelperFrames` for nonempty modeled calls. `exact_tree_r9_from_operations` applies accepted R11 to the same constructed output and derivation witness under explicit R11 reservation and R12 `TreeOperations` premises.

This does not connect `TreeOperations` cuts to a single execution state. Their `Cut` entry equations and model programs are premises. Actual Rust helper-return correspondence, a complete retained-path-to-relative-path mapping, primitive and alias authenticity, reservation availability, publication/native authenticity, the original parent, effect hygiene, consumer residual, soundness, principality, termination and production remain **OPEN**. The theorem establishes no Rust execution or production result.

## Next admitted dependency

Following the sprint-end selector recommendation, the next proposed packet is `EFFECT-PERMISSION-CONNECTED-CUTS/20261029-r13`. Its fixed question is to derive R12's cuts from one threaded operation-model state and prove an explicit full-path-to-relative-path map while preserving owners, occurrences, rows, operands, allocation identity and sibling distinctions. Permission appends remain distinct ordered mutations. This advances model connectedness only; actual Rust execution linkage and all parent/production gates remain OPEN.
