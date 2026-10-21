# R229 — Callback formal, provider port, and WorkBound owner

R229 extends the exact R221 source trace in `r221_higher_order_loop_callback_reachability`. It establishes a candidate source/native owner chain for the registered callback formal and its body demand in the same solve instance. This is owner evidence for one accepted source, not a proof of the parent theorem, R71, or R72.

## Owner chain observed

The callback Apply at HIR occurrence 19 selects the formal-use registration whose index and recipe position are both 2. Its registered parameter ID is the callback Lambda's parameter ID, and the Lambda is occurrence 16. The registration's native root is positive live value `Term258`.

Lambda occurrence 16's FormalAnnotation fact at slot 44 has `Term258` as its lower endpoint and the registered source annotation domain `Term331` as its upper endpoint. The same Lambda's constructor fact at slot 2 has a positive function lower term whose argument port is exactly `Term331`; its upper endpoint is the value component owned by Lambda occurrence 16. Thus the source annotation domain is tied to both the exact registered formal root and its owning Lambda argument port.

Provider Apply occurrence 26 is reached through the authentic `repeat` local, whose initializer is that same Lambda and whose local identity is the registered parameter's binding. The exact provider callee Name is occurrence 27 and resolves to the same local ID. Its retained `LocalFreshRoute` maps the captured positive function's argument node to the provider replay's expected callback function `Term377`. The route's slot-zero fact restores the route graph root to the exact source Name component. The mapped argument node is a negative function node, and the same `Term377` is the upper negative-function endpoint of provider replay relation 363.

The annotation domain `Term331` and provider expected term `Term377` are distinct term identities. The owner chain therefore crosses the explicit `repeat` LocalFreshRoute map; equality of the pre-route source term would be the wrong join. The focused assertion finds exactly one retained positive-function node whose mapped argument is `Term377`.

The callback body's Apply at occurrence 19 has slot-zero source fact `Term258 <= Term340`: the same registered formal root is the lower endpoint, and its native demand is `Term340`. The R221 source grouping attributes that Apply to the relevant WorkBound processing. The production work event selects raw key `EffectRow(21), Positive <= EffectRow(31)` and operation `NegativeFunction(Term340)`, so the selected Work::Bound consumes the exact body demand. The existing trace also retains the exact source-Apply owner for this callback WorkBound event.

## Evidence and limits

The new assertions are test-only and live in the existing same-instance R221 trace. They check registration identity, source provenance facts, LocalFreshRoute identity and mapped graph nodes, provider replay relation 363, and the production WorkBound event. The focused command passed:

```text
cargo test -p yu-solver --features shadow-apply-candidate --lib r221_higher_order_loop_callback_reachability -- --nocapture
```

`cargo test -p yu-playground` passed on the final R229 source tree. The sprint static check and all 57 `test_agent_sprint.py` tests passed; `git diff --check` passed. The package run emitted existing compiler warnings, with no test failures.

No production owner representation or semantic change was added. No independent review was run. This observation does not establish `Term340`'s required inequality against provider expected `Term377`, a required slot-4 alias-changing fiber, or general coverage for arbitrary source programs and schedules. R221's exact source still has no slot-4 merge/copy. R71, R72, the original quantifiers and the parent computation-forwarding theorem remain OPEN. The next useful proof obligation is an authentic required-fiber lineage to a later source-owned Work::Bound and an independently justified consumer, followed by the general quantifier-preserving proof.
