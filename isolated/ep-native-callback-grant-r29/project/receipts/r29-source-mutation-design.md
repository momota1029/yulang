# R29 Rust source-only repair receipt — revision 2

Status: SOURCE-ONLY; no mutation, compilation, test or runtime check has executed. R1's three precompile review findings have concrete test/source repairs in the frozen candidate, pending fresh independent exact-hash source review. This file is a design receipt, not the required runtime mutation receipt.

## R1 findings and source repairs

1. **Query-time Grant/liveness:** `Machine::propagate_request` clones the actual invocation descriptors and a separate `(invocation_id, active)` guard projection immediately before evaluating the actual `local_grant` call. Both are test-only request-owned snapshots. `validate_callback_route_evidence` receives them as separate arguments, authenticates the selected query guard row against the descriptor snapshot, and replays local Grant against that active query-time state. The post-`ReceiverReturn` invocation remains inactive; the validator does not reactivate or change it. The positive route asserts a true query guard, accepts the unchanged certificate, and asserts the final descriptor is inactive.
2. **Dynamic Catch identity:** after `validate_handler_installation` succeeds on the selected live frame, the machine retains a separate test-only `selected_catch_installations` source vector with the actual dynamic occurrence, Catch source site, owner, resolved operation, selected arm and live-frame authentication. Candidate `RequestConsumerEvidence` retains only an index to that vector plus emitted candidate fields. `validate_dynamic_catch_consumer(candidate, selected_source, event)` takes the independent source record separately and checks candidate handle, source site, authentication, owner, resolved operation and arm against it. The candidate JSON serializes that source record separately.
3. **Construction-bound mutation:** the candidate observation bound is mutated while the independently retained request vector remains untouched. The harness creates one later authentic test-only observation using the selected execution in the same `Receiving`. If selected ordinal is `n`, the original bound is `n+1`; the later observation has ordinal `n+1` and bound/updated `next_observer` `n+2`; the candidate mutation sets bound to `n+2`, so the old inequality `bound <= next_observer` is true (`n+2 <= n+2`). Exact candidate-to-request-snapshot comparison must reject it.

## Changed-target callback cases

All callback cases use `rejected_mutation`, which asserts target presence, an actual before/after difference, and rejection before a receipt row is created.

- Wrong invocation owner, formal/receipt, typed use/result view, event/origin and resolved effect remain targeted against source-store validators.
- Wrong dynamic installation changes `handler_id` and `installation_occurrence` together to the same nonexistent ordinal; the two candidate fields remain internally equal and must fail against the separate selected-frame record.
- Wrong dynamic owner changes both candidate owner fields to `ModuleRun`; they remain internally equal and must fail against the selected invocation owner.
- Wrong selected arm changes both candidate arm fields to the companion's distinct parse-owned node; they remain internally equal and must fail against the callback's selected live frame.
- Wrong resolved operation substitutes the companion's write operation and must fail against the selected frame's actual callback operation.
- Wrong query-time guard changes the candidate active bit while leaving both independent query-time snapshots untouched.
- Construction-bound mutation follows the `n`, `n+1`, `n+2` construction above and leaves the request snapshot untouched.

## Companion cases retained

The seven R28 owner/frame/request mutations remain unchanged: wrong positive node index; deleted required boundary; borrowed/fresh disposition; disconnected write lineage; changed no-op target guard; wrong request occurrence; dropped replay boundary. They remain distinct from callback Grant evidence.

## Owner and boundary map

- `Receiving::observe` assigns actual observer ordinal and next-bound; `Observation.observer_bound` and its initializer remain `cfg(test)` only.
- `Machine::propagate_request` reads the live `Frame::CatchReturn`, calls `validate_handler_installation`, selects its resolved arm, and calls actual `local_grant` using `request.observations`, request event, installation owner, live invocations and resolved family.
- The test-only request evidence separately retains the exact observation vector, invocation descriptor snapshot, and active-guard projection from immediately before that Grant call.
- Receiving joins callback result, typed use, formal/name/result receipts, actual execution-table occurrence, request snapshot, query-time liveness and recomputed Grant.
- The separate machine selected-installation vector records the validated live Catch frame's dynamic occurrence/source/owner and the selected resolved operation/arm. Candidate Catch fields are compared against it before serialization.
- The companion route retains only its template/owner/frame/write request owners. No companion field supplies callback permission, observation or Grant evidence.

No fixture, solver, HIR, production runtime decision, dependency, expected output, or lockfile changed. Selected-main assertions remain `1` and `23`, but neither result is established by execution in this source-only stage.
