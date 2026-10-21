# Sprint R210 — Provider row map and slot-4 frontier path

Status: ACTIVE, primary-only test observation.

## Goal

Continue R183's exact same-provider frontier question after R209 joined the local `relay` binding, its completed Lambda slot-4 Origin, physical bound and route membership. Inspect the actual captured Function graph/port rows and fresh row map for Effect(10)/Effect(31), then search the retained route inputs for a compensating same-use path.

## Exact scope

Read R183 §§2–3, 6 and R205–R209 notes. Edit only this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (test-only graph node/row map and source-bound route query), `notes/theory/2026-10-21-r210-provider-row-map-frontier-path.md`, and current.json. Do not edit production behavior or frozen R183 artifacts. No subagents.

## Validation

One targeted test process maximum with output under `target/r210-provider-row-map/`; remove scratch at closeout. No retry. Correlate exact route index, graph root and Function ports, requested/canonical Capture rows, fresh images and source relation 71. Report a finite authenticated path if present, or retain the exact missing bridge; do not treat a source-emitted omitted fiber alone as a theorem counterexample.
