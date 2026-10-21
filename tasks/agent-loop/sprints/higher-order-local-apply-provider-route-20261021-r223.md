# R223 — Local Apply provider route into higher-order formal

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, serial fallback because the user's no-subagent instruction overrides the default dispatcher/parallel lanes.
Baseline: `d79c07773` on `research/simple-sub-intrusion`.
Parent: original computation-forwarding preservation theorem; R71 raw canonical fiber coverage and R72 later-occurrence source consumer remain OPEN.

## Question

R222 established that available `CandidateSourceCall`/native observations do not expose an edge from the actual `loop` argument of `repeat loop` (occurrence 26) to callback formal `f` (Apply 19); this is not a semantic counterexample. Inspect the exact local Apply construction and retained `LocalFreshRoute` structure to determine whether the application path already contains a reconstructible, occurrence-specific correspondence from the actual argument's function components to the registered callback formal's rows and the loop Lambda slot-4 relation.

Success requires a concrete path with source occurrence, local binding/use identity, source and instantiated row identities, polarity/function ports, and every existing FreshUse/Replay/transport witness. A row-number match or mismatch alone is not sufficient. If the path is absent, identify the first missing producer/consumer record and a falsifier for any proposed reconstruction.

## Evidence and implementation lane

Use the exact accepted R221 source already embedded in the test fixture. Reuse ordinary `CandidateInference::solve(hir)` and private retained graph state reachable from the test module. Trace `LocalSourceForm::Apply` for `repeat loop`, its `ApplySourceInput` (`local_callee`, `argument_value`, `argument_effect`), native `CandidateApplyRecipe`, the local routes for the actual `loop` and callee `repeat` Names, the formal `f` function component in the repeat scheme, and the loop Lambda slot-4 origin through its later local route. Add only focused test-only observation in `crates/yu-solver/src/shadow_apply/local_source_observation.rs`; no production behavior, theorem premise, semantics, or public API changes.

## Exact paths and checks

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- this contract
- `notes/theory/2026-10-21-r223-local-apply-provider-route.md`
- `tasks/agent-loop/current.json`

Run the focused R223 test and `cargo test -p yu-playground` when the trace remains interpretable; finish with `python3 tools/agent_sprint.py check`, `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`, `git diff --check`, serialized current-state size, exact-path commit and push. 600 seconds, no carryover. Solo primary, no independent review claimed. Preserve R71/R72 and parent theorem as OPEN unless their original obligations are actually closed.
