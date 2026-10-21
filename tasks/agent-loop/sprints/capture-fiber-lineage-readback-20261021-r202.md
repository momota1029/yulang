# Sprint R202 — Capture fiber lineage readback

Status: CLOSED, targeted query failed during test compilation.
Branch / baseline: `research/simple-sub-intrusion` / `b0e45b7a5f3bc90279c6abdb31001f697244a6c9`.
Authority: unchanged computation-forwarding preservation parent §§1, 6–7 and R183-FRONTIER-COVERAGE-1. No inference semantics or production gate changes.

## Outcome

Add a test-only, read-only accessor for the source event IDs already stored on a candidate relation, then inspect the R187 relay Capture snapshots against existing BoundAdmission, BoundEmission, physical readback and checking-occurrence records. No solver-state retention, allocation, or production API addition. Determine whether the four known relay Capture relations have source event sets and exact bound admission/emission chains, and report coverage gaps without treating endpoint equality as proof.

Success evidence: one bounded table keyed by exact `BoundKey + relation`, with source event/checking key, admission cause/coverage, emission admission ID/physical slot/readback, and Capture snapshot coverage. Missing links remain explicit. This fixture does not settle the universal parent.

## Exact boundary

Read the frozen R201 receipt and exact source owners below. Write only this contract, `tasks/agent-loop/current.json`, `crates/yu-solver/src/candidate_context.rs` (test-only accessor), `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (targeted test), and `notes/theory/2026-10-21-r202-capture-fiber-lineage.md`. Scratch only under `target/r202-capture-lineage/`, removed at closeout.

One Cargo process maximum: targeted `yu-solver` library test with `shadow-apply-candidate` and output capture. No retries after invocation failure. No production code path change, no other tests, and no subagents. Solo primary per user instruction. Budget 600 seconds, no carryover. Preserve all theorem quantifiers and gates.
