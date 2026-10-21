# R235 rev2 — Formal effect boundary and test-only replay accounting

Status: ACTIVE_SOURCE_AUDIT; Luna solo primary. No subagents or independent
review. This revision adds one test-only accounting correction discovered while
investigating the incomplete `yu-solver` library suite.

## Fixed parent outcome

Preserve the R235 source behavior: a formal callback annotated
`int -> [io] int` rejects an actual `int -> [state] int`, while the compatible
`[io]` callback remains accepted. The bounded candidate-path implementation is
already present at baseline `1ba9fa441`; original Simple-sub, R71/R72, semantic
approval, independent review and production remain OPEN.

## New in-sprint outcome

The exact candidate-context test group currently reports 11 retained-byte
assertion mismatches. In `candidate_context::State::replay_operation_bytes`,
`bytes()` includes the capacity of the `#[cfg(test)] replay_drain_observations`
vector. The test-only `enumerated_bytes()` omits that same allocation. The
observed mismatches are multiples of that vector's element capacity.

Count this test-only vector in `enumerated_bytes()` and verify the full
candidate-context group except the separately reproduced, long-running
`queued_relation_equality_transport_retains_context_ancestry_and_retry` test.
Do not change production accounting, replay behavior, assertions, language
semantics, or source examples. A failure after the correction, a capacity delta
not explained by this field, or a new production-path mismatch falsifies this
bounded diagnosis and keeps the solver-suite gate open.

## Exact authority and lease

- `crates/yu-solver/src/candidate_context.rs` — test-only byte enumerator only.
- `tasks/agent-loop/sprints/higher-order-effect-formal-constraint-20261021-r235-rev2.md`
- `notes/theory/2026-10-21-r235-higher-order-effect-formal-constraint.md`
- `tasks/agent-loop/current.json`

No other source/test path is leased. Keep the original theorem quantifiers and
all R71/R72 parent claims unchanged and OPEN.

## Verification and stop conditions

Run the focused candidate-context test group with the known long-running test
skipped, then the authorized `cargo test -p yu-playground` regression suite,
the sprint static check and `git diff --check`. Do not retry the full library
suite until the exact remaining failure surface is understood. Keep the
individual long-running test and full solver suite status OPEN. This is a
bounded solo implementation result, not independent review or proof closure.
