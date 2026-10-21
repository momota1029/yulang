# R235 — Preserve higher-order formal effect constraints

Status: ACTIVE_SOURCE_AUDIT; Luna solo primary, no subagents or independent review.
Branch / baseline: `research/simple-sub-intrusion` / `d09d4e4c9`.
Parent: unchanged Simple-sub inference and computation-forwarding obligations; R71/R72 remain OPEN.

## Fixed outcome

A source formal annotated `int -> [io] int` rejects an actual `int -> [state] int` function, just as a direct top-level annotation assignment already does. Preserve ordinary inference and the existing exact playground examples. Trace the authentic source formal, Local/module use, Function ports, effect bounds and conflict consumer; fix the owning candidate inference path without a source-shape rule or changed language meaning. Add a source regression for the mismatch and a compatible callback control. Apply the result to R71/R72 only where its exact premises match; no parent theorem closure from this local fix.

Reproduction evidence at baseline: direct `my good: int -> [io] int = bad` rejects a `[state]` body; both higher-order forms `my accept (f: int -> [io] int) = 0; my main = accept bad` and `my accept (f: int -> [io] int) = f 0; my main = accept bad` are candidate-accepted when `bad` performs `state::put`. A matching `[io]` callback is also candidate-accepted. All are ordinary candidate CLI invocations; scoped mode has the same outcomes.

## Exact lease and authority

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_effect.rs` — negative nested formal effect boundary construction.
- `crates/yu-solver/src/candidate_extrusion.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/shadow_apply/local_source_observation.rs` — same-instance source/consumer probe only.
- `tools/inference-playground/tests/cli_higher_order_effect_mismatch.rs`
- `tasks/agent-loop/sprints/higher-order-effect-formal-constraint-20261021-r235.md`
- `notes/theory/2026-10-21-r235-higher-order-effect-formal-constraint.md`
- `tasks/agent-loop/current.json`

Only this bounded candidate solver path and its test may change. No new syntax, source restriction, principal/production claim, or semantic decision is authorized. No Yulang2 sample or expected output changes. Keep the full Simple-sub theorem and all parent gates OPEN unless separately proved and independently reviewed.

## Evidence, falsifiers and checks

A fix must make the exact incompatible higher-order sources reject for the actual `[state]` versus `[io]` conflict, and keep matching effects accepted. Trace the source Apply and its callback argument through the constructor-generated Function/Effect children and the conflict consumer; do not add a one-off rejection at the source form. Include a negative test showing direct annotation behavior remains intact and a positive higher-order runtime-compatible control. Falsifiers: conflict is absent, attributed to an unrelated source, matching callback rejects, effect rows are compared in the wrong direction, or any current embedded playground sample changes behavior.

Run focused solver/tool regression, `cargo test -p yu-playground`, `npm run check` in `web/playground`, sprint static check, 57 tooling tests and `git diff --check`. Budget cap 3600 seconds, no carryover. At this solo boundary independent review is unavailable; report the implementation as unreviewed candidate work and keep parent/production gates open.
