# R228 — Provider argument to local-route owner path

Status: exact source/native owner path established for the R221 provider actual argument. No production change. R71, R72, and the parent computation-forwarding theorem remain OPEN.

## Source and native correspondence

The cfg(test) audit `r228_provider_argument_local_route_owner_path` uses the exact R221 source in ordinary candidate mode. Provider Apply occurrence 26 has a `LocalSourceIndex` argument whose HIR Name is occurrence 28. That Name resolves to the same `HirLocalId` owned by `LocalFreshRoute` occurrence 28. The Apply's `provider.argument_value` points to candidate endpoint component position 55; the native argument is `Term452`, a positive `LiveVariable` whose ordinal equals `live_components[55].ordinal` (28).

The route root is `Term409`. Its exact slot-zero `ConstraintStore` fact links that root to `batch.component_term_at(argument_position)`, and the route context relation is 355 (`ValueRow(42) <= ValueRow(28)`). The route's FreshUse replay dependency is relation 356, with lower relation 237 and upper relation 355. Its upper input is `ValueRow(42), Negative <= ValueRow(28)`.

Provider Apply source-origin relation 357 names the exact checking occurrence 26. FunctionPort Argument Swap derives relation 362 from 358. Replay relation 363 combines route replay 356 with relation 362; its inputs are `ValueRow(28), Positive <= PositiveFunction(Term413)` and `ValueRow(28), Negative <= NegativeFunction(Term377)`. The resulting typed pair is `Term413 <= Term377`. `Term413` is the LocalFreshRoute graph function node, so the exact provider actual-argument endpoint reaches the replay's actual callback function node through the owned route and replay dependencies.

This closes the R224 gap for the **provider actual-argument owner seam**: the source argument use, local route, candidate endpoint, native live row, restoration fact, and Apply replay are joined by explicit owner evidence rather than a shared term shape.

## Limits and failed broader check

This does not connect callback formal registration to the provider expected/formal path, establish the callback body WorkBound demand (`Term340`), produce the required alias-changing merge or later Work::Bound copy, or prove fiber lineage, source/native soundness, R71/R72, or the parent theorem. R221 remains an exact-source case with no slot-4 alias-changing merge/copy.

The focused R228 test passed. The `candidate_scheme::` module filter still has four failures: `active_outer_root_two_helper_uses`, `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting`, `replay_constructor_lineage_observes_rejected_cross_route_authentication`, and `retained_demand_transport_authenticates_distinct_uses_and_rejects_wrong_use_or_root`. The latter three report existing assertion mismatches in route/replay fixtures; the first reaches `IdentityExhausted`. I have not established whether these fail on the baseline, so they are recorded as unresolved suite failures, not attributed to R228. The package-level `cargo test -p yu-playground` passed on the final tree.

No production field or admission check was retained: the attempted production representation caused candidate scheme failures and was reverted. The committed code change is only the cfg(test) audit.
