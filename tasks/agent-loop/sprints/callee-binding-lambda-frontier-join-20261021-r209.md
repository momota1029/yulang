# Sprint R209 — Callee binding Lambda and capture frontier

Status: ACTIVE, primary-only test observation.

## Goal

Join Apply occurrence 18's exact local callee ID to its `LocalSourceBinding`, identify the binding initializer Lambda and slot-4 Origin, then inspect Capture row decisions for both bound endpoints. This prevents attributing a caller Lambda to the provider route. Original R183 scope and quantifiers remain unchanged.

## Exact scope

Read R183 §§2–3, 6 and R205–R208 notes. Edit only this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (test-only callee/binding/Lambda and Capture-row query), `notes/theory/2026-10-21-r209-callee-binding-frontier-join.md`, and current.json. No production changes, no frozen R183 artifacts, no subagents.

## Validation

One targeted `yu-solver` test process maximum, output under `target/r209-callee-frontier/`, then remove scratch. No retry. Join by exact `HirLocalId`, not spelling or endpoint equality. Report the candidate route's captured representative, level, boundary, non-generic and local flags for the slot-4 bound endpoints. This is fixture-specific evidence, not closure of R183.
