# Sprint R203 — Test-only lineage readback compile repair

Status: CLOSED, primary-only bounded repair and validation.
Branch / baseline: `research/simple-sub-intrusion` / `b0e45b7a5f3bc90279c6abdb31001f697244a6c9`.
Authority: unchanged computation-forwarding preservation parent §§1, 6–7 and R183-FRONTIER-COVERAGE-1. No inference semantic or production gate change.

## Outcome

Repair the `yu-solver` feature-test compile failure at the existing private `candidate_extrusion::Key` debug-format site with the minimal `Debug` derive. Then validate the already-written test-only Capture-fiber lineage readback once. The readback only reads existing relation source sets, BoundAdmission, BoundEmission, checking occurrence, and Capture snapshot records; it adds no solver-state storage or production API. Apply observed missing fields to R183 without treating the fixture as universal proof.

Success evidence: the targeted test runs and prints an exact table for captured relations 53, 56, 57 and 62, or fails with a source-qualified report naming the first unavailable relation/admission/emission/source event. No retry after the validation invocation fails.

## Exact boundary

Exact allowed edits: this contract, `tasks/agent-loop/current.json`, `crates/yu-solver/src/candidate_extrusion.rs` (test-only `Debug` derive), `crates/yu-solver/src/candidate_context.rs` (test-only source-event accessor), `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (test-only query), and `notes/theory/2026-10-21-r203-capture-fiber-lineage.md`. Scratch only under `target/r203-capture-lineage/`, removed at closeout.

One Cargo process maximum: the targeted `yu-solver` library test with `shadow-apply-candidate`, output captured. It passed once after adding the test-only `Debug` derive. The observation is limited to the R187 fixture and does not close R183 or any production gate. No other tests, no production path changes, and no subagents. R202's failed invocation was not repeated: this validation followed an intervening source fix and was a new bounded run. Solo primary per user instruction. Budget 600 seconds, no carryover. Preserve original quantifiers and all gates.
