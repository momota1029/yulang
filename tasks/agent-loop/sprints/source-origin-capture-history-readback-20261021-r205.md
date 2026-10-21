# Sprint R205 — Source-origin and Capture history readback

Status: ACTIVE, primary-only test observation.

## Goal

Continue the user's original Yulang proof and sample-coverage goal by adding the smallest read-only view needed to determine whether R203's four relation rows carry retained source Origins or source-drain receipts. Parent and exact R183 gate remain unchanged.

## Exact authority and files

Baseline `76b3a628a` on `research/simple-sub-intrusion`. Read `notes/theory/2026-10-21-r183-source-to-capture.md` §6, the frozen R183 result and R203/R204 notes. Exact editable files: this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (test-only print of existing Origin and source-drain data), `notes/theory/2026-10-21-r205-source-origin-capture-history.md`, and `tasks/agent-loop/current.json`. Do not modify production paths or frozen R183 artifacts. No subagents.

## Validation boundary

One Cargo process maximum: run the existing targeted R187 Capture-lineage test once, with output captured under `target/r205-source-history/`. No retry after invocation. Remove scratch output at closeout. This reads retained Origin/source-drain records and maps event IDs to existing checking occurrences; it does not claim completeness or source/native proof.

## Decision

Report whether each captured relation's own origins and its admission's processing relation retain a source occurrence or drain receipt. Identify whether the next missing edge is source emission, relation propagation, or observer coverage. A fixture result cannot prove the universal R183 frontier law or certify a counterexample.
