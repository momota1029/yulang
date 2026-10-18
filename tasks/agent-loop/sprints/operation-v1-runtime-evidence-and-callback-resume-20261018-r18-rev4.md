# r18 revision 4 — repair compile errors exposed by the focused target

This amendment retains every r18 revision 1–3 claim, quantifier, source domain, success predicate, semantic constraint, production boundary and parent scope. The r2 delta passed independent artifact review, but the authorized focused Cargo target failed to compile before running tests. This is a new-code compile failure, not a known formatting or CI issue and not evidence about runtime behavior.

## Fixed repair outcome and exact edits

Correct only the three compile errors exposed by `cargo test -p yu-playground --test runtime_resume`:

1. In `Machine` construction inside `RuntimeProgram::start`, initialize the trace from `self.operation_v1`, not `self.program.operation_v1`.
2. In the source catch-argument join, keep the Apply argument `Label` distinct from the looked-up `Code`; retain the exact argument code's `SourceSite`.
3. Make `Label` equality available for identity comparison within the same retained code arena, without broadening source equality or matching semantics.

No semantic changes, source fixture/expected-value edits, guard removal, test weakening, formatting-wide changes, or edits to `lib.rs`, the tests, solver, proof or source artifacts are authorized. The r3 distinct-Apply checks, exact closure/environment/invocation joins, negative control, both bounded function-response gates, existing `local_grant`, live handler/arm conditions, and final Completed42 gate remain unchanged.

The focused target may be rerun only after this frozen compile repair receives a CLEAN independent delta review. If it compiles and runs, report its actual individual results. If compilation fails elsewhere or a source/runtime gate fails, stop at the first new boundary; do not weaken the original fixture or success condition. Parent theorem remains OPEN, original conditions closed 0.

## Exact continuation lease

Write lease:

- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation-r4.md`

The r2 tests, r2 handoff, `lib.rs`, continuation runtime, solver files and proof artifacts remain frozen/read-only. The old hashes and CLEAN r2 review remain valid for that earlier snapshot only. Freeze exact new hashes and stop before checks; Luna assigns the same independent compiler reviewer for a fresh delta review of this repair. Only a CLEAN result permits the single focused target `cargo test -p yu-playground --test runtime_resume`.

## Resource amendment

The prior 3900-second cap stays fully charged; no unused time is restored. This continuation adds 600 seconds, for cap 4500 and 4500 conservatively charged when issued: compile repair 120, independent delta review 180, focused target/integration/state 300. Astra remains 0. No automatic renewal or carryover.

## Stop conditions

Stop at the first of: frozen repair handoff, 120-second repair reservation consumed, independent review BLOCKING, the focused target's next failure boundary, or total 4500 seconds charged. Keep all prior frozen snapshots and findings. A green focused target establishes only this research runtime path, never parent theorem closure or production readiness.
