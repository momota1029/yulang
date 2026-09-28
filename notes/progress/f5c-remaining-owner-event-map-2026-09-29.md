# F5c remaining physical-owner event map

Status: updated after the reviewed family-4 owner-event checkpoint. Family 4 is
closed for the scoped `f5c_resource_probe` event slice; §34 families 2, 5, 6,
and 8 remain open. No test, matrix, preflight, benchmark, or measurement ran.

Authority: F5 §26/§34 in
[`F5 foundation`](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
the Authoritative
[`no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md),
and the current
[`no-cap scale plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).

The event categories now checkpointed are §34 family 1 (`live_variable_tables`),
family 3 (`structured_pair_memo`), family 4 (`component_expansion_memo`), and
family 7 (`generalization_scratch`). The existing sidecar calls the last
category `family6` for historical code compatibility. The remaining §34
families are 2, 5, 6, and 8:

| §34 family | Matrix lanes | Owner and current evidence | Terminal owner state |
|---|---:|---|---|
| 2 `inference_type_arena` | 18–23 | `crates/yu-solver/src/term.rs`: `BranchTermArena::independent_owner_lanes` and `with_term_events`; `crates/yu-solver/src/lib.rs`: `record_term_lanes` | Permanent term lanes remain live through `SolvedModule.store`; journals can clear or transfer. |
| 4 `component_expansion_memo` | 45–64 | Implemented and independently reviewed; see [`family-4 event checkpoint`](f5c-family4-component-expansion-memo-events-checkpoint-2026-09-29.md). | All 20 lane owners release on clear/drop; terminal current capacity and retained bytes are zero while event peak remains. |
| 5 `closed_type_arena` | 65–100 | `crates/yu-types/src/lib.rs`: `F5cResourceProbeSummary`, finalizer sampling, indexed temporary reconciliation, and capacity-state reconciliation | Finalization releases scratch/indexed lanes and transfers the permanent arena into `SolvedModule.closed_types`. |
| 6 `closed_normalization_index` | 101–128 | `crates/yu-solver/src/f5c_normalization.rs`: 13 base and 15 flat physical-index lanes, `FlatPhysicalIndexLedger::record`, `handoff_member`, and `release_after_normalizer_drop` | All index lanes reach zero after normalizer drop. |
| 8 `instantiation_substitution` | 230–236 | `crates/yu-solver/src/lib.rs`: `InstantiationScratch`, attached scratch, growth/failure sampling, and `record_instantiation_scratch_resources` | Seven lanes (five maps/sets and two vectors) reach zero at finish. |

Existing snapshots and per-owner ledgers provide current lengths, capacities,
growths, and some same-time peaks, but the matrix sidecar still does not stream
§34 families 2, 5, 6, or 8. Check each at its actual growth/release sites so a
named-boundary snapshot cannot hide a larger same-time peak.

## Next bounded slice: family 2

`inference_type_arena` has six lanes with existing `BranchTermArena` owner
observation hooks. Trace its owner IDs across reserve success/failure, journal
clear, transfer, and final `SolvedModule.store` retention; reconcile event-time
peaks with the row and terminal arena. Keep this slice separate from families
5, 6, and 8.

Other established contract locators are the term-owner event tests near
`lib.rs:29462`, the yu-types indexed-probe case near
`crates/yu-types/src/lib.rs:3537`, normalization tests near
`f5c_normalization.rs:4792`, and instantiation resource cases near
`lib.rs:27413` and `27949`. They identify existing ownership behavior; none
was run for this map.
