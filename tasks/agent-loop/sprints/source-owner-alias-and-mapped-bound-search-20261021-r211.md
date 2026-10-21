# Sprint R211 — Source-owner alias and mapped-bound search

Status: ACTIVE, primary-only readback.

## Goal

Resolve the precise remaining R183 bridge from R210: whether source slot-4 owner Effect(10) has an authenticated canonical/shared representative in the relay Capture, and whether a retained bound links that representative to FreshUse image Effect(32).

## Exact scope

Read R183 §§2–3, 6 and R205–R210 notes. Edit only this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` with test-only representative, captured-bound and route-input reads, `notes/theory/2026-10-21-r211-source-owner-alias-search.md`, and current.json. No production changes or frozen R183 edits; no subagents.

## Validation

One targeted test process maximum with output under `target/r211-source-owner-alias/`; remove scratch at closeout. No retry. Query `candidate_intrusion::State::rep` for the exact source endpoints and enumerate captured effect bounds through their graph row keys, relation IDs and snapshots. Report exact path if present; otherwise identify the remaining source/native owner.
