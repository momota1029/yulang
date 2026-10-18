# r18 closeout — same-HIR operation callback runtime path

Status: `ENDED-PARTIAL-REVIEWED`; fixed research outcome achieved. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN, original quantified conditions closed **0**.

## Result

The explicit research-only path now carries the successful static `FieldBoundV1` receipt from the exact retained HIR into runtime. In the focused source, the handler evaluates `k response`; the raw saved continuation returns the exact response closure; a distinct surrounding source Apply invokes it with its captured environment while the outer catch remains live; its callback operation reaches the actual outer arm and execution completes with integer `42`. The runtime receipt is withheld unless these facts share the exact source/candidate and dynamic invocation evidence.

`continuation_apply`, `response_invocation_apply`, and `callback_apply` remain distinct source identities. A same-closure/different-Apply negative control does not mint a receipt. Existing `local_grant`, both bounded Function-response checks, ordinary and scoped defaults, failure/exhaustion rejection and the final Completed42 gate are preserved. This is a one-source Phase-S-to-Phase-R research milestone; it is not a proof of general correspondence or production readiness.

## Review and test record

- Fresh integrated r1 review found a blocker: runtime compared the outer closure invocation with the inner `k response` Apply. The focused test was correctly gated and not run.
- The r2 repair separated the Apply identities and added exact closure/environment/invocation-owner evidence plus a different-Apply negative control. Independent review: **CLEAN**.
- The first focused compile attempt exposed three new type/reference errors before any tests ran. This was not treated as a known formatting/CI failure.
- The bounded r4 repair corrected only those three errors. Independent delta review: **CLEAN**.
- `cargo test -p yu-playground --test runtime_resume`: **17 passed, 0 failed**. This run establishes acceptance and runtime `local_grant` for the fixed research specimen, including Completed42 and negative/failure controls.
- `python3 tools/agent_sprint.py check`: PASS (static state consistency only).

Proof artifact `2026-10-18-operation-v1-runtime-resume-correspondence.md` remains a conditional baseline audit, not a proof of the runtime implementation or parent theorem. No original A/B quantifier, soundness, principality, termination, F1/FK1 or N-Transport condition is closed.

## Frozen implementation and handoffs

```text
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b  tools/inference-playground/src/lib.rs
d33b61740c256c18664450e909301d19a41c33e568523f648428e329a0bf7e11  tools/inference-playground/src/runtime/program.rs
ef3cba5f89789e393e31ceeb7175f1ca1be6f250f71a150001f9b9fd6ba56f19  tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3  tools/inference-playground/src/runtime/continuation.rs
459e53b822ac37d260970c94d7dc1b0287085117fa2203fbbc21da5ebfd367f9  tools/inference-playground/tests/runtime_resume.rs
b17e267b8d9ffe688b031eb1969e6de8200ffa8ee458f6aa9d54d3f7d2450bc1  tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation.md
284cc470652d017fd4eea2b36fe109368c50138dfcfebb1449f76529bdf8c0e9  tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation-r2.md
67d2e0d1cc3b448ac1214f9b349263ec8cea3cbdb864dacb0ad248d7d251fc60  tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation-r4.md
```

All implementation authors and reviewers are STOPPED. The r18 cap is 4500 seconds, fully conservatively charged; Astra 0. Primary integration and Git are Luna-owned. The research code and handoffs are ready for a coherent checkpoint; quarantine replay drafts and Python cache remain excluded.

## Next parent-facing outcome

The next selected outcome is the actual `Install(g) -> Capture/FreshUse -> g()` path: prove and implement that the captured `q/m0/FieldBoundV1` is remapped to the authentic FreshUse, consumed at that use's own native edge, and joined to the executed `g` and live outer handler. Falsifiers include acceptance of another FreshUse's receipt or a remapped lower/upper/scope targeting a different use. This remains a research candidate until independent review; parent closure stays zero.
