# R241 — Live-root propagation and Apply correspondence

Status: partial constructor result; unreviewed. Parent and R71/R72 remain OPEN.

## Fixed question

Does a provider Function or required bound admitted after an internal same-SCC Module use route through its live target root propagate to the existing use row? Does the typed Function comparison at that use join the same source Apply's actual argument effect, AE/RE demand and output? Incoming graph/FreshUse and retained Local routes remain separate.

Parent and dependency pins, exact scope, falsifiers and write leases are in `tasks/agent-loop/sprints/simple-sub-live-root-apply-correspondence-20261021-r241.md` (SHA-256 recorded in current state).

## Internal route and incremental Apply join

`Action::Module` for an active same-SCC use calls `route_candidate_open_use`, then `route_internal_inner` constructs the exact pair `ValueRow(target_root) <= ValueRow(use_value)` and `route` admits it under that `DefinitionUse` occurrence before `constrain_live_value` drains it. This is a shared live-row relation; this route does not instantiate a captured graph or FreshUse.

The source planner records every component's level at `Work::Visit`. A definition root Lambda is visited at level 1; its body is visited at the same level. A block visits each local initializer at `level + 1`, so a Module Name within such an initializer can be higher-level than its provider root. The live-row constructor handles both orientations, with a meaningful distinction:

* If `use_level <= root_level`, `candidate_apply_value` stores the route as an upper row on the root. A later positive Function bound at the root replays against that direct upper row. A Function already at the root is replayed when this route is inserted.
* If `use_level > root_level`, it stores the root as a direct lower row on the use. By itself, that one-sided row does not establish a universal promise that later root bounds wake through the route.

For an actual Apply of that Module Name, source construction retains one `CandidateRelation::Apply` and `ApplySourceInput` at the Apply expression occurrence. `admit_candidate_fact` checks that the source input's callee, argument, argument-effect, result and application-effect endpoints are the exact endpoints in that relation. It builds the negative Function demand from the actual argument value, actual argument-effect component, a fresh invocation-result-effect row and actual Apply result row, then admits `callee-positive <= demand-negative` at the same Apply occurrence.

This concrete consumer closes the late-provider gap in either row-level orientation. When the route is represented as a lower root row on the use, inserting `use <= demand` replays that row and generates `root <= demand`. When the route is represented as an upper use row on the root, a root Function that is already present is replayed into the use; if it arrives later, the new root lower bound replays the stored use upper row, after which the use's Apply demand is met. Typed-pair dispatch and bound replay drain to quiescence before each source action returns. This proves the route-before-provider and provider-before-route orders for this concrete Apply chain, subject to successful admissions and the retained source identities. It does not prove that every internal Module route without an actual Apply consumer propagates every future bound.

At the positive Function / negative demand comparison, `dispatch_live_item` emits the exact children:

```text
Argument:       demand.argument <= provider.argument
ArgumentEffect: demand.argument_effect <= provider.argument_effect
ResultEffect:   provider.result_effect <= demand.result_effect
Result:         provider.result <= Apply.result
```

The source Apply argument effect is the `argument_effect` stored in its `ApplySourceInput`; the invocation demand uses that exact component. Its result is the source Apply's `result` component with negative polarity. The source Application effect receives the callee-computation effect and the fresh invocation-result-effect via the two candidate effect admissions owned by the same Apply recipe. Thus the AE/RE comparison is joined to this Apply occurrence and its source endpoints, rather than inferred from an endpoint-equal row. This is the exact live-route/Apply square available to the R239 parent mapping.

## Remaining boundary

This is a source-constructor correspondence candidate, not parent closure. Applying it to the parent still requires the original typing/admission hypotheses and the R239 conditional result at the actual provider Function ports. A same-SCC Module use that is not consumed by this actual Apply pattern is outside the proved join. Incoming graph/FreshUse and retained Local routes remain separate. No source-qualified counterexample was constructed; the level asymmetry above is a reason to keep the consumer premise explicit, not evidence of an implementation violation. R71/R72 and the whole forwarding induction remain OPEN.

No production, implementation, test, build or sample claim.
