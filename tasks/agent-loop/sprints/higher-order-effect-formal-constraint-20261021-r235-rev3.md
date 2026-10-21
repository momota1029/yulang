# R235 rev3 — Exclude test-only replay observations from retained-byte accounting

Status: ACTIVE_SOURCE_AUDIT; Luna solo primary. No subagents or independent
review. This revision supersedes rev2's incomplete accounting adjustment while
preserving its frozen diagnosis and result.

## Fixed parent outcome

The R235 higher-order effect behavior is implemented at baseline `1ba9fa441`:
a formal callback annotated `int -> [io] int` rejects an actual
`int -> [state] int`, while the compatible callback remains accepted. Original
Simple-sub, R71/R72, semantic approval, independent review and production remain
OPEN.

## Test accounting correction

`ReplayDrainObservation` and `replay_drain_observations` exist only under
`#[cfg(test)]`. The candidate context's retained-byte budget models compiler
state in ordinary builds, so its test-only trace capacity must be excluded from
both `State::bytes()` and test-only `enumerated_bytes()`. The 11 initial
enumeration mismatches came from counting the trace in the former but omitting
it from the latter. After adding it to the enumerator, 125/127 context tests
passed; the remaining two showed that failed test routes can retain trace-vector
capacity, which is instrumentation storage rather than compiler state.

Remove only the `#[cfg(test)]` trace-capacity contribution from
`replay_operation_bytes()` and the temporary matching enumerator contribution.
Do not change trace contents, production replay state, resource assertions,
solver semantics or samples. Success: all candidate-context tests pass when the
separately reproduced long-running test is skipped, and no production resource
counter includes test-only allocations. Any remaining mismatch or production
path change falsifies this diagnosis.

## Exact authority and lease

- `crates/yu-solver/src/candidate_context.rs` — symmetric accounting exclusion
  for the test-only observation vector.
- `tasks/agent-loop/sprints/higher-order-effect-formal-constraint-20261021-r235-rev3.md`
- `notes/theory/2026-10-21-r235-higher-order-effect-formal-constraint.md`
- `tasks/agent-loop/current.json`

No other source/test path is leased. Keep the original theorem quantifiers and
all R71/R72 parent claims unchanged and OPEN.

## Verification and stop conditions

Run the focused candidate-context group with only
`queued_relation_equality_transport_retains_context_ancestry_and_retry`
skipped, `cargo test -p yu-playground`, the sprint static check and
`git diff --check`. Keep the full solver suite and the long-running test OPEN;
this test-instrumentation correction does not claim to resolve either one.
