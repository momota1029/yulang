# R252 — correct the contravariant effect row premise

Status: ACTIVE; solo primary, no delegated workers.
Baseline: `c24714228`; user clarification supersedes the R235 higher-order mismatch premise.
Resource envelope: 900 seconds, no carryover.

## Outcome

In a contravariant effect position, a concrete annotation such as `[io]` denotes
an open row `[io, 'e]`. An actual `[state]` callback therefore does not violate
the formal. Preserve the direct positive annotation mismatch control, while
accepting `[state]` callbacks for unused, called and inline higher-order formals.

Remove the closed `Allowance([io])` bound previously added to negative concrete
formal effect ports. Preserve `FormalPermission` so the concrete family still
serves the formal's local handler role. Mark R235's contradictory outcome,
falsifiers and interpretation superseded.

The ordered tuple source carrier added in R251 has no candidate inference or
runtime tuple implementation yet. Add explicit refusal arms in candidate
inference and runtime compilation so the workspace builds without treating a
tuple as Unit, Group or a function.

## Exact write paths

- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/tests/cli_higher_order_effect_mismatch.rs`
- `tools/inference-playground/tests/runtime_module_expressions.rs`
- `tasks/agent-loop/sprints/higher-order-effect-formal-constraint-20261021-r235.md`
- `notes/theory/2026-10-21-r235-higher-order-effect-formal-constraint.md`
- `tasks/agent-loop/sprints/negative-effect-row-open-tail-correction-20261021-r252.md`
- `notes/theory/2026-10-21-r252-open-effect-tail-correction.md`
- `tasks/agent-loop/current.json`

## Checks and falsifiers

Run the corrected CLI regression, the negative-formal permission unit test,
`cargo test -p yu-playground`, `cargo test -p yu-hir --lib`,
`python3 tools/agent_sprint.py check`, and `git diff --check`. Compare formatter
output with `HEAD` because these Rust files contain existing formatting drift.

Falsifiers: a negative `[io]` annotation rejects an actual `[state]` callback;
the direct positive annotation control stops reporting the real mismatch; a
concrete formal permission is lost; or Tuple reaches candidate/runtime code by
being silently mapped to another constructor. Source/native proofs, independent
review, tuple inference/evaluation and the original Yulang2 samples remain open.
