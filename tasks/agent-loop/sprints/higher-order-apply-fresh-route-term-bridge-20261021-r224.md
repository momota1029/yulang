# R224 — Apply demand to LocalFreshRoute term bridge

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, no subagents.
Baseline: `ea452b0f3` on `research/simple-sub-intrusion`.
Parent: original computation-forwarding preservation theorem; R71 and R72 remain OPEN.

## Question

R223 found the actual `loop` route source Effect(41) -> local route Effect(69), the repeat callback formal source Effect(31) -> route Effect(57), and Apply 26's argument endpoint/native demand. No `ReplayDemandRow` or explicit `local_callee` witness joined them. Determine whether `RetainedFreshUseMaps.terms` in the internal candidate scheme already maps those exact LocalFreshRoute function nodes to the Apply 26 native argument/demand or the callback `f z` consumer's terms. Preserve owner, source occurrence, function port, polarity, native term identity, and any intervening relations.

## Bounded method

Add one focused test-only observation in `crates/yu-solver/src/candidate_scheme.rs` using the exact accepted R221 fixture in ordinary candidate mode (`collect_candidate_mode`, with scoped experiment disabled). This module can inspect retained FreshUse term maps without adding production instrumentation. Compare terms by arena identity and source-node/function-port ownership; do not infer a bridge from matching row ordinals. If no join exists, state which producer map or consumer edge is missing and distinguish it from the namespace-limited route-row observations in R223.

## Exact paths and checks

- `crates/yu-solver/src/candidate_scheme.rs`
- this contract
- `notes/theory/2026-10-21-r224-apply-fresh-route-term-bridge.md`
- `tasks/agent-loop/current.json`

Run the focused R224 test and `cargo test -p yu-playground` if interpretable. Finish with `python3 tools/agent_sprint.py check`, `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`, `git diff --check`, serialized state size, exact-path commit and push. 600 seconds, no carryover. Solo primary; no independent review claimed. Keep the parent theorem, R71 and R72 OPEN unless their original obligations close.
