# Module FreshUse retained native transport implementation handoff

Sprint-ID / contract revision and SHA-256: `module-use-retained-native-transport-20261017`, revision 2, `b193043d56e60af7bfea4f8de7310a1230ae39546df70455bc4fa4b788184604`.

Assignment-ID / handoff revision: `MODULE-USE-RETAINED-NATIVE-TRANSPORT-IMPLEMENTATION-20261017` / revision 3 (bounded accounting repair).

Parent gate: original Yulang inference/execution theorem, unchanged source domain, A/B claims, quantifiers and source/native correspondence. This implementation removes only the module FreshUse remap-retention prerequisite; original theorem conditions closed: **0**.

Baseline / direct dependencies: sprint baseline `9f8a03bdf`; implementation assignment began at `b2b827b48` with the exact `candidate_scheme.rs` input pin below. Contract and all ten frozen input pins were SHA-256 checked before writing and matched. Current branch state was `edadb58d4` (assignment-state checkpoint) at start.

Role / author / runtime: `implementer`, `/root/module_freshuse_retention_implementation`, current session, Luna/high requested. Observed model and effort metadata: UNKNOWN. No descendants.

Exact leased paths, sole author:

- `crates/yu-solver/src/candidate_scheme.rs` — implementation and one focused regression test.
- `tasks/agent-loop/inbox/20261017-module-use-retained-native-transport-implementation.md` — this handoff.

## Outcome

The module-only private `freshen_candidate_graph_retained` helper returns the constructed `FreshUse` with its reconstructed root and leaves its exact crosswalk capacity charged as transition scratch. The existing `freshen_candidate_graph` entry point retains its original `(Term, Vec<RowKey>)` signature and scratch-reset/projection behavior for other callers. Both paths share a private construction/restoration core. After all existing module bound-restoration work, the same `FreshUse::into_retained_parts` used by the local route moves rows and all eight non-row fields into the committed `FreshRoute`: `scope_remap` (all three maps), `scoped_relations`, `context_use`, `terms`, `effect_operands`, `bundle_remap`, `context_remap` and `evidence_remap`. The map record remains private. It is published with the same use ID and Graph after routing succeeds. Existing route-vector rollback truncates and drops the record; session destruction drops it with its owning `GraphState`.

`RetainedFreshUseMaps::bytes` is reused unchanged. `GraphState::refresh_bytes` now counts every committed module route's remap capacities, in addition to Graph and row capacities. Route vector capacity charges `size_of::<FreshRoute>()`, including the inline retained-record headers/scalar. For the transition, let S be caller scratch at capture entry, G the captured Graph capacity, and F the returned row plus remap capacities. The retained helper enters with S+G and adds F, so pre-transfer scratch is S+G+F. The checked transfer subtracts G+F while retained accounting adds route-vector growth, G and F, leaving exactly S. A cfg(test) assertion checks `state.scratch_bytes == entry_scratch` immediately before the prepublication resource sample. The preceding revision subtracted only F and incorrectly left G in scratch while adding G to retained. Reservation, checked arithmetic and resource sampling precede publication. A failed route follows the existing rollback and availability path.

Added focused regression `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting`. It executes a minimal module with repeated identity uses, asserts actual module route row/term/evidence crosswalk dimensions, checks the retained-map capacity sum, and compares incremental retained accounting against a full owner recount. No source admission, inference rule, diagnostic, API, classifier, expectation or candidate publication boundary changed intentionally.

## Cost and evidence

Proposed/checked cost categories, without physical allocator claims:

- Persistent per committed module route: `FreshRoute` inline size increase (counted in route-vector capacity) plus `RetainedFreshUseMaps::bytes()` for six backing vector/hash-map capacities and the three `ScopeRemap` map capacities. Rows remain charged once through their existing vector capacity. `context_use` and all map headers are inline in `FreshRoute`.
- Transition: the same row/non-row backing-capacity sum is charged once as `scratch_bytes` while the completed `FreshUse` awaits route publication, then moved to retained accounting. Existing temporary construction arrays are not retained by the new route record.
- Existing Graph/session/context/native payload owners remain separately charged. The capacity model does not measure allocator bucket/control bytes or physical allocator overhead; no benchmark or asymptotic improvement is claimed. Storage grows with the summed retained capacities of committed module uses.

Source-to-native correspondence remains structural: the exact maps produced by `prepare_candidate_fresh_use` for the module use survive with its Graph and rows. They do not authenticate source field ownership, classify Published/Mono handles, create `Phi_u`, prove semantic adequacy, or add a map consumer.

## Checks, pins and boundaries

Frozen changed-source SHA-256: `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494`.

Frozen direct input pins, checked before edits:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `notes/design/2026-10-17-module-native-field-map-contract.md` | `1465b65979b2742de020c2bc7b44ff6fb53adefa7158d9fa3947d0b4d5923502` |
| `notes/theory/2026-10-17-module-source-handle-introduction.md` | `df0e684bad2da05741e39db12bd06bb400ad8b5b15af4116abab4df6c9df06c3` |
| `tasks/agent-loop/inbox/20261017-module-source-handle-introduction.md` | `46412c131659b8cd9621e38053dcce49916087788c9c90c5442bef51db84f4d2` |
| `tasks/agent-loop/inbox/20261017-local-use-retention-applied-correspondence.md` | `edec4fc3252351f62235ed7caaed6844c720d17e6a3805fb9f9fa9dd310e7fa4` |
| `tasks/agent-loop/inbox/20261017-local-use-retention-implementation.md` | `e78fd6cee9c1afeac740158b45084647dc495b963ddbafaad00f9f8f26b9b009` |
| `notes/theory/2026-10-17-local-use-existing-map-retention.md` | `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e` |
| Sprint contract revision 2 | `b193043d56e60af7bfea4f8de7310a1230ae39546df70455bc4fa4b788184604` |

Prior evidence reused: the private `RetainedFreshUseMaps` record and exact local-use accounting/move construction; the frozen local-use owner/capacity correspondence only as an implementation pattern. Rejected as authority: local-use semantics for module handles, source-field ownership, full `Phi_u`, or any implication that retained maps supply an authenticated source derivation.

Review findings applied: the preceding transfer omitted `Graph.bytes()` from the scratch subtraction even though the retained helper's entry scratch already included the captured Graph. Revision 3 subtracts G+F and adds the pre-sample cfg(test) equality assertion. The earlier compile-only check also exposed callers that rely on the original vector-returning helper (`candidate_effect` row indexing and `candidate_context_tests` `Vec<RowKey>` comparisons); revision 2 restored that API. This author did not rerun Cargo, build, tests or formatting under this 120-second repair lease. Luna owns focused verification and the test filter `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting`; this handoff is not proof or independent review.

Known provisional boundary: none added. The original module handle-owner gate `HINTRO-OWNER-u_id`, native source-field completeness, total `Phi_u`, root/Call, F1/FK1, N-Transport, soundness, principality and termination remain open. Next related step after Luna's checks: assign the frozen-byte proof of this implementation's exact route ownership, rollback/drop and capacity transfer. No new path or disposable scratch was created.

Budget: original allocation ≤480 seconds; compatibility repair ≤120 seconds; accounting repair ≤120 seconds (exact runtime telemetry unavailable). Writer STOP after freezing these two leased outputs. No Git mutation, user/external contact, config edit or agent launch.
