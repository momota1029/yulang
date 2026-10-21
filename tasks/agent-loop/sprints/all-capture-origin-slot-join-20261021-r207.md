# Sprint R207 — Capture snapshot to source-slot join

Status: ACTIVE, primary-only test observation.

## Goal

Continue the original forwarding-preservation proof by checking whether the same Capture route contains the required source Lambda slot 4 alongside the now-authenticated Name slots 1/2. Preserve the original source domain and quantifiers.

## Exact scope

Read R183 §§2, 3, 6; R205/R206 notes; the R187 fixture and existing local source observation. Edit only this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` with a test-only enumeration of all relevant Capture snapshots and matching Origins/slots/completion, `notes/theory/2026-10-21-r207-capture-origin-slot-join.md`, and current.json. No production behavior, no frozen R183 artifact edits, no subagents.

## Validation

One targeted `yu-solver` test process maximum, captured under `target/r207-capture-origin/`; remove scratch at closeout. Join captured relation IDs to matching physical bound rows, every retained Origin and its source expression/local slot, and separate source-drain completion status. No retry.

## Outcome

Report whether slot 4 is in this route's Capture frontier, and name the first missing edge if it is not. A fixture result is not universal proof and cannot close R183 by itself.
