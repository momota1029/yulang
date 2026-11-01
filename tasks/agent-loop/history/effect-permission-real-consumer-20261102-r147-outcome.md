# R147 outcome — effect consumer boundary reviewed

## Result

R147 is **ACCEPTED as bounded source/native boundary evidence**. The independent reviewer rederived the result from 20 authenticated inputs and found no additional major or minor compiler-correctness issue.

At the pushed baseline `3560df97dab02744da10e897c73c1cf94118f4ee`, source-created scope/input IDs use append indices. `ScopeInventory::fresh` appends copied images above the pre-copy cut; transformer and demand coordinates use the same FreshUse `ScopeRemap`. This supports the below-cut invariant for represented transformer/demand IDs. It does not bound or encode a separate incoming native state.

The actual Rust path reaches an ordinary allowance decision: `candidate_context_execute_relation` calls `candidate_apply_effect`, which inserts/replays row bounds or reaches `candidate_check_effect_operand`. That decision checks effect-family membership in an allowance, follows an allowance tail, or reports mismatch. Catch-related effects can share this worklist. Catch construction propagates scrutinee and arm effects outward, while `candidate_catch_operation` builds continuation/effect constraints. The admitted path shows no scope-sensitive Catch subtraction and no incoming `ScopeState` transport.

The first missing bridge is a source-owned incoming contribution/protection state, bounded at allocation, transported with the same FreshUse map, and joined to a protection-sensitive effect/Catch decision while preserving contribution attribution. The review treats this as an OPEN premise, not a reachable counterexample. The original A/B claims, full source/native theorem, semantic approval, and production readiness remain OPEN.

## Frozen evidence

- R146 source handoff: `effect-permission-native-support-invariant-r146-source.md`, SHA-256 `9c940ab56ccd182299833fe93b41701619d600b62c15f3af21b9b94659b694ef`.
- R146 proof handoff: boundary-deviation receipt, SHA-256 `96cc0701900dc43349b527fae4a6c288a2f50687bc2a1a817796e8aa48513ba0`; all substantive observations remain withheld.
- R147 source handoff: SHA-256 `d4f20f0f47d64b35416053c1f3be86daba197113b60acfb17ebf2cde9a3793ef`.
- R147 proof handoff: SHA-256 `f12a4cdbfe27bccb5a9a617ad40f775e7896b7c8b644f440a4b8c43f0de6a010`.
- Independent review: SHA-256 `b9bcd8bf2bebca4b063bcef24e8b9094eb40c525db0cbe48930631aab47316ed`.
- No compiler or test execution occurred. `python3 tools/agent_sprint.py check` passed as static protocol evidence only.
- No Rust, Lean, runtime, environment, cache, scratch, checkout or worktree changes were made. Pre-existing dirty/quarantined paths remain untouched.

## Integration disposition

The reviewed deliverable is a research checkpoint; no production change is supported by this result. Primary may stage only the exact R146/R147 records, these handoffs/review/outcome, and compact `current.json`, then commit and perform a normal fast-forward push. No force push. Any later production repair requires new exact authority and evidence for the missing state/consumer bridge.
