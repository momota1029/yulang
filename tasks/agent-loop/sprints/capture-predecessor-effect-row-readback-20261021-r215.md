# R215 — Capture predecessor effect-row readback

Status: ACTIVE, solo primary, test-only source observation.
Baseline: `fe4a52606`; branch `research/simple-sub-intrusion`.

## Parent question

R213 records source relation 71, `Effect(10) <= Effect(31)`, as a completed
Lambda slot-4 owner absent from the same local relay Capture graph. This packet
checks the decisive owner boundary: when Capture visits canonical Effect(31),
does the solver's raw `effect_bounds[31].direct_lower_rows` contain Effect(10)?

- If yes, the owner edge exists in the Capture input and the defect lies in
  graph traversal or route serialization.
- If no, source relation emission and the solver's stored effect-bound relation
  diverge before Capture; the candidate frontier witness needs a different
  interpretation and the source/accumulation owner becomes the next target.

This is candidate implementation evidence only. The original forwarding
preservation theorem, source/native bridge and production gates remain OPEN.
No solver decisions, samples or semantics may change.

## Exact scope and leases

Read baseline: the frozen R213 witness and R212 inventory. Exact write paths:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs` (test-only Graph initializers)
- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- this contract, `tasks/agent-loop/current.json`, and one result note under
  `notes/theory/`.

Baseline source SHA-256 values:

- `candidate_scheme.rs`: `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25`
- `shadow_apply.rs`: `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4`
- `local_source_observation.rs`: `534b466f62062f2744d6a40021f05f2dfa2ebb41d939d65ff3997714e15aa199`

Only `#[cfg(test)]` readback fields/output may be added. Capture a bounded copy
of raw lower/upper effect-row adjacency at the moment each effect row is first
visited. Query the existing R187 relay route, print the row 31 snapshot and
whether it contains 10, then assert the observation is complete and keyed to
canonical Effect(31). Do not infer a conclusion from absence if the row was not
visited or the bounded output truncated.

## Verification and limits

The first invocation reached compilation but failed because two existing test
Graph literals lacked the new test-only field. After adding that field, the
command passed, but Rust's test harness captured the required `println!`
snapshot. The `--nocapture` Cargo invocation then passed, but the command
output was truncated before the R215 line. Extract the test binary and run only
`local_source_observation` once, filtering output to the R215 record so the
bounded row decision is observable:

`RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate local_source_observation`

One test process, no parallel build. Budget 240 seconds, no carryover. No
subagents per the user's standing constraint; dispatcher use is unavailable in
this solo session, so this bounded primary-owned question is selected directly
from R213's named missing owner. Stop after the row-31 predecessor decision is
recorded. A passing test proves only that the instrumentation ran.
