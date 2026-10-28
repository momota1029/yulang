# R17 amendment 01 — executable observer coverage boundary

Status: **ADMITTED BY LUNA** as contract revision 2. This amendment supersedes only the R17 success and row-logging clauses quoted below. It does not change R17's objective, source snapshot, Cargo command, feature, test, expected output, semantic behavior, budgets, or parent scope.

## Reason and preserved claim

The frozen R17 revision-1 candidate calls the existing observed authenticator only after native-call and copied-port lookup succeed. Those two `continue` paths are silent. The observed core emits no event for a route whose FreshUse identity does not match. For a matching route, its first failed guard returns `None` from the whole function, so later routes are not visited. Therefore R17 revision 1's requested classification of every matching route and every skipped row exceeds what its authorized diagnostic call can observe.

Preserve the original objective at row granularity: identify the actual replay rows and report the first guard reached by the existing authenticator for each invoked row, while making every pre-call skip and early return explicit. Do not claim that routes after the core's first rejection were visited or classified.

## Revised allowed implementation delta

The only write remains the same leased `candidate_scheme.rs` per-row replay loop. Preserve the revision-1 call arguments and returned evidence. Add test-log records only:

1. one row-start line with call, FreshUse, child/lower/upper relation IDs, root;
2. explicit `SKIPPED_NO_NATIVE_CALL` and `SKIPPED_NO_COPIED_PORTS` outcomes on the existing skip paths;
3. each existing observer event `(owner, route, stage)` for the invoked row;
4. one row-end line with the number of observer events and result class (`ACCEPTED` or `NONE`). If the authenticator returns `None` with zero events, classify that row as `NO_MATCHING_FRESH_USE_ROUTE`; if it returns `None` after a rejection event, report that the existing core stopped at the first rejected matching route and later routes are `NOT_VISITED_AFTER_EARLY_RETURN`.

No authentication guard/order, route-selection behavior, evidence, fixture, output expectation, solver behavior, production source, feature, dependency, manifest, or lockfile change is authorized. Preserve all pre-existing assertions.

## Revised bounded success and review

A complete result contains an explicit row-start/outcome record for every replay row observed by the fixture, and identifies whether authentication was skipped, found no matching route, accepted, or stopped at the first rejected matching route. It reports later routes as unvisited where the existing core short-circuits. The source handoff must not infer an absent route from a missing callback without establishing that the authenticator was invoked.

The independent pre-run reviewer must authenticate the R16-derived baseline manifest and verify that the complete R17 candidate diff remains confined to this loop, with no decision or fixture changes. The one exact Cargo command and resource limits in base contract revision 1 remain unchanged. The same worker grants and path leases remain; no budget resets. Existing rev1 implementation and source handoffs remain immutable historical receipts; any resumed write uses the next sequential handoff revision.
