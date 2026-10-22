# Sprint R328 — Console result row and playground CLI regressions

Revision 2 adds a narrowly scoped integration-test lease after package-wide tests exposed two CLI assertions not exercised by the lib suite. Revision 1 remains unchanged history.

Current evidence: playground lib tests pass 45/45. Package tests pass library/bin stages but two of 23 CLI integration tests fail. One `--intrusion` conditional-conflict case reports an unexpected error; `intrusion_flag_observes_actual_source_associations` reported `StructuralProjection` before the selected-source traversal fix and must be rerun.

Exact leases: `tools/inference-playground/src/lib.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, `tools/inference-playground/tests/cli.rs`, this contract, R328 note, and current sprint state. `crates/yu-hir/src/module.rs` is frozen after the selected-root prelude fix.

Print the unexpected stderr in the conditional CLI test, reproduce against the exact `CARGO_BIN_EXE_yu-playground`, and repair the underlying path while preserving the requirement that conflicts withhold all output. Re-run the complete package test before returning to the Console result-row trace. Continue solo, with no agents. Existing R328 cap is not reset.
