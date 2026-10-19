# R78 surface readiness

Date: 2026-10-19  
Sprint: `effect-hygiene-executable-method-role-20261019-r78`  
Contract SHA-256: `bf68454c19a7b4cfe5168355e0e5fb73beec069ad57dd53678258a66f26dfcab`  
Status: design artifact in progress; no implementation authority

## Current surface and next path

- Parser: syntax-v0 already represents `.identifier` as `FieldTail`; standalone `role` and `impl` declarations have their own CST nodes.
- Source/HIR: R76/R77 retain exact parser-owned field, role and impl positions. The R77 receiver/role proof is conditional on its pinned snapshot. The only focused R77 command failed on a trivia-inclusive source range expectation; do not trim that range. Its error-category collapse also remains for a separately activated revision.
- Local source: `LocalSourceForm` includes `Apply`, `Name`, `Lambda`, `Block`, `Catch`, literals and related forms; it does not include field access, method dispatch, or role/impl selection.
- Playground: `Instruction::Apply` is executable. It receives local-source forms and runtime evidence; it is provisional and does not establish ordinary Call source formation or production semantics.
- Method/role decision: the concrete proposal is in `notes/design/2026-10-19-r78-executable-method-role-pilot.md`. Role body and impl description are parse structure today. Their new lookup and implementation meaning needs independent review and explicit user approval.

## Effect hygiene direction

The parallel proof lane follows three pinned existing source cases: `unit_payload_empty_call_pattern_selects_its_arm`, `a_different_operation_arm_does_not_preempt_the_exact_operation`, and `selected_operation_arm_runs_outside_its_shallow_handler`. It separates local permission, actual request/inflow, ordered arm selection, continuation use, and outward runtime request. Runtime forwarding is not treated as a static residual-type theorem. The parent hygiene obligation, its universal quantifiers and all A/B gates stay open.

The proof lane is capped at 900 seconds and stops at the first exact constructor/consumer gap. C1 suffix reconstruction, storage/fiber inventories, tests, probes and builds are outside this sprint.

## Gate to runnable source behavior

1. Fresh compiler/source and spec/design reviews must have no unresolved blocking/major issue.
2. User decides whether to adopt the draft method/role semantics.
3. A new implementation contract grants exact parser/HIR/index/inference/playground paths and expected outputs.
4. The source-to-ordinary-application path and outward effect behavior receive bounded proof and focused verification.

Until then, `receiver.method(args)` remains syntax with pending field-tail meaning; no method dispatch is implemented or claimed.
