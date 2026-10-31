# Outcome — EFFECT-PERMISSION-CONSUMER-RESIDUAL-20261028/r1

**Status: CLOSED_INCOMPLETE.** Luna adjudicates this as outcome (4): the exact source-demand/provider and consumer-extraction bridge remains unestablished. The independent reviewer rejects Rust handoff rev1's stronger “fixture expectation defect” classification. The empty native census is bounded evidence, not proof that the protected expectation is false or that a solver defect exists.

## Objective and evidence

The sprint investigated the original effect-hygiene consumer failure without changing its source fixture, expected output, original `r != q` obligation, or production semantics. Its contract is `tasks/agent-loop/sprints/effect-permission-consumer-residual-20261028-r1.md`, SHA `a2d8b9a7aef7a142559370d9f5bd10d8fe0ee6d68f9bb4938d4167a11a86da7e`.

The retained fixture passes a stateful callback to a recursively self-calling function, then syntactically uses `left 0` after pattern matching the function's result. The source does not yet establish that `left` is the passed callback. The cited approved local-self-recursion rule is local-binding/HirLocalId scoped; this fixture's `my f` is module-level, so it does not settle the module-definition recursion route. Tuple-case construction projects the scrutinee result, while Apply records argument and result endpoints separately. The required source-owner bridge is still missing.

The one released focused Cargo invocation used the exact 280-entry input inventory, rehashed independently with zero mismatches. It reached the preserved consumer assertion with the unresolved `r != q` assertion isolated. The test-only returned-effect census was empty. Result: exit 101, 59.64 seconds, 1,671,032 KiB peak RSS, zero swaps. Raw stdout SHA `909397e3e687dc3a81ddc31c6d390e8f2097507b5620c58f38a097859dd21f46`; stderr `fcc2dda80f9ad3b6476a40854013d14b24edea4e6db275e958057480130ee54b`; status `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`; time `463dbc0d3112b2c98909a7b55ab16cee5bcb42890f25707176d92af395a9527b`. Inventory SHA `a1785f08ca2fc0a2fbdae0e1dd1d1345e41c8d2db36180bc912f163def7560f0`; argv SHA `dc6226de053d1987403ced78894d0c3bdb0c5f2ef942259246d1b0422ef10197`; launcher SHA `3bbc32d269f0483af5753c6c5f9706b623a886d521e8a830257fca5fcbb605bc`.

The fixture has no Catch/handler, so it supplies no observed permission-subtraction event. The exported formal permissions are metadata; N-Subtract-Elim still requires an actual source demand, same-contribution transport, a typed local consumer, eligibility and selection/removal evidence. No such residual conclusion is accepted.

The proof lane constructed no Lean theorem and ran no Lean invocation. It found no applicable accepted theorem that supplies source contribution inflow, handler subtraction or returned-computation residual membership. Its frozen handoff keeps those premises explicit.

## Independent review and source boundary

Fresh reviewer receipt: `tasks/agent-loop/inbox/effect-permission-consumer-residual-review.md`, SHA `505463444165018764e3b4680b58a624f43da7eeeccd2db6489d6ed4d5088691`.

The reviewer independently verified all six artifact pins, every inventory entry, all invocation receipt hashes, the reached assertion and empty census. It accepts these bounded observations, rejects “fixture expectation defect” as unsupported, and retains only “source/provider bridge not established.”

The reviewer could not authenticate the entire source delta against predecessor SHA `6f20ac00deb2f5a84f57a0cf54cf9ceb64f2de5a90d15cc371240d9de68dfa3b`: no baseline byte file was present and reversing the isolated entry/census/helper flags did not reproduce that hash. This is an unresolved provenance limitation, not evidence of a production-path change. Current `candidate_effect.rs` is SHA `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`; `candidate_scheme.rs` remains at `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`. No source change is accepted for integration. The test-only census remains provisional and Luna owns later cleanup or replacement under a reviewed exact source scope.

Frozen lane handoffs: Rust `tasks/agent-loop/inbox/effect-permission-consumer-residual-rust.md`, SHA `c873113f179634be7f9e29e90eea95f717bd50f4ceb314c239379e488ce8b1fe`; proof `tasks/agent-loop/inbox/effect-permission-consumer-residual-proof.md`, SHA `7437b723ac103af620dd35dd348ec78fbd82c176eb9893b4acf0578da9b817db`. Their “fixture expectation defect” and source-demand statements are superseded by this adjudication where they overstate the evidence.

## Closure boundary

No original parent, H/A/B, consumer-hygiene, source/native, unequal transport, principality, termination or production gate closes. No semantic or expected-output change is authorized. No second Cargo invocation or Lean invocation ran. All authors and reviewer stopped; no Git operations occurred. The next exact source task is to establish the module-definition recursive Definition/Call/result-to-pattern route and a same-contribution extraction interpretation, or identify its first missing transition. A source-linked real handler is separately required before making a subtraction claim.
