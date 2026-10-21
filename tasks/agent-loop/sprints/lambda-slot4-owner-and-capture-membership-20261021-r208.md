# Sprint R208 — Lambda slot-4 owner and Capture membership

Status: ACTIVE, primary-only test observation.

## Goal

Resolve R207's exact remaining fixture question: find the effect-result slot 4 for the local `relay` Lambda, identify its relation/source bound and physical admission/emission, and check membership in the same provider Capture route. Preserve the original R183 quantifiers and open status.

## Exact scope

Read R183 §§2–3 and 6, plus R205–R207 notes. Edit only this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` with a test-only lookup of the Lambda slot-4 Origin/admission/emission and route Capture membership, `notes/theory/2026-10-21-r208-lambda-slot4-owner.md`, and current.json. No production changes, no frozen R183 artifacts, no subagents.

## Validation

One targeted `yu-solver` test invocation maximum, captured under `target/r208-lambda-slot4/`; remove scratch at closeout. No retry. Report an absent source slot separately from a present but uncaptured bound. This fixture observation cannot close R183.
