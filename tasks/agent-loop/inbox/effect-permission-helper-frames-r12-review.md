# R12 independent review handoff

Sprint: `EFFECT-PERMISSION-HELPER-FRAMES/20261029-r12`

**Verdict: PASS for the conditional R12 operation transcription and R11 application.** No blocking, major or minor compiler-correctness findings.

## Frozen inputs authenticated

- Revision 2 artifact: `notes/theory/lean/YulangClosure/FormalPermissionHelperFrames.lean`, SHA-256 `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.
- Proof handoff SHA-256 `63fde25dc4aec460338d127ef6e2c625d2016e9b60c17860a45b4e89c1c63b55`.
- Amendment 01 SHA-256 `94661003e31471dd4bdfcf1e96b0e789a9441e2d7c69bdb009f668e7f443f868`.
- Source handoff SHA-256 `e270f74164f29816f5823687afc431617843b49ae7e28ffb06bc942d5a8e385b`.
- Attempt 2 plan SHA-256 `5f591bded5132e01f6da0fe02c3d1194e5b2db156445b363549cc54f2e66c8ee`; copy receipt SHA-256 `e1cefe9a1ffae4f1569254db5af27e1afce1fb9e60a44f960e8ced6e13bed1f3`; audit receipt SHA-256 `2e956b992197d52f70f956b13997bbd9559938211edbee1121c3a43520e16168`.
- The 133-entry input manifest, 16 copied project files, seven tool entries and four raw audit output files have zero mismatches.

## Findings

Revision 1 to revision 2 changes only three record-update layouts and consistently renames `prefix` to `priorPermissions`. All nine public theorem statements remain unchanged modulo this binder and field-label renaming. No constructors, assumptions, operations or retained paths changed.

Audit stdout contains nine complete theorem types and nine transitive axiom reports. Lean 4.35.0 exited 0 in 15.51 seconds; maximum RSS was 973036 KiB. Axioms: none for `operation_preserves_allocator`, `operations_preserve_allocator`, `nonempty_operations_frame`, `permission_append_delta`, `concrete_port_prefix_delta` and `ordered_concrete_port_delta`; `{propext}` for `reservation_projection` and `tree_frames_from_operations`; `{propext, Classical.choice, Quot.sound}` for `exact_tree_r9_from_operations`.

`HelperOp` excludes permission append; `pushPermission` and concrete preparation give a separate append delta. Nonempty call programs derive local frames. The final theorem applies R11 with the same constructed output and derivation witness.

## Remaining boundary

`Cut` entry equations and `TreeOperations` supply model states and programs without linking execution between cuts or to allocator `a`. Actual Rust helper-return correspondence, a complete retained-path-to-relative-path map, primitive and alias authenticity, reservation availability, and publication remain OPEN. This review supports only the conditional operation transcription and R11 application; it establishes no native authenticity, original-parent closure or production readiness.

Review role: fresh nonauthor `compiler_referee`, read-only. No Lean, Lake, checker, tests or Cargo were run by the reviewer; no files were edited by the reviewer.
