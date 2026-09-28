# F5c remaining physical-owner event map

Status: updated after the reviewed §34 family-6 owner-event checkpoint.
Families 2, 4, 6, and 8 are closed for their scoped `f5c_resource_probe` event
slices; §34 family 5 remains open. No test, matrix, preflight, benchmark, or
measurement ran.

Authority: F5 §26/§34 in
[`F5 foundation`](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
the Authoritative
[`no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md),
and the current
[`no-cap scale plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).

The event categories now checkpointed are §34 family 1 (`live_variable_tables`),
family 2 (`inference_type_arena`), family 3 (`structured_pair_memo`), family 4
(`component_expansion_memo`), family 6 (`closed_normalization_index`), family 7
(`generalization_scratch`), and family 8 (`instantiation_substitution`). The
sidecar retains `family5_event` for semantic family 6 because event kinds
584–611 occupy its prior numbering slot; its older `family6_event` names
semantic family 7 for compatibility. The only remaining §34 family is 5:

| §34 family | Matrix lanes | Owner and current evidence | Terminal owner state |
|---|---:|---|---|
| 2 `inference_type_arena` | 18–23 | Implemented and independently reviewed; see [`family-2 event checkpoint`](f5c-family2-inference-type-arena-events-checkpoint-2026-09-29.md). | Six event lane totals reconcile at FinishOutput; every retained owner transfers under the same ID into `SolvedModule.store` and remains live at EOF. |
| 4 `component_expansion_memo` | 45–64 | Implemented and independently reviewed; see [`family-4 event checkpoint`](f5c-family4-component-expansion-memo-events-checkpoint-2026-09-29.md). | All 20 lane owners release on clear/drop; terminal current capacity and retained bytes are zero while event peak remains. |
| 5 `closed_type_arena` | 65–100 | `crates/yu-types/src/lib.rs`: fixed aggregate current/peak and call-local aggregate peak at existing finalizer reconciliation sites; solver combines with owners stable over the indexed-finalizer call | Finalization releases scratch/indexed lanes and transfers the permanent arena into `SolvedModule.closed_types`. Architecture is resolved; event implementation remains open. |
| 6 `closed_normalization_index` | 101–128 | Implemented and independently reviewed; see [`family-6 event checkpoint`](f5c-family6-closed-normalization-index-events-checkpoint-2026-09-29.md). Thirteen base and fifteen flat physical-index lanes use same-time owner events. | All index lanes reach zero; output lanes 21–26 transfer the same IDs into staged buffers. |
| 8 `instantiation_substitution` | 230–236 | Implemented and independently reviewed; see [`family-8 event checkpoint`](f5c-family8-instantiation-substitution-events-checkpoint-2026-09-29.md). | Seven event lane totals reconcile at FinishOutput; all scratch owners release and family-8 current capacity/bytes are zero at EOF. |

Existing snapshots and per-owner ledgers provide current lengths, capacities,
growths, and some same-time peaks, but the matrix sidecar still does not stream
§34 family 5. Check its actual reconciliation sites so a named-boundary
snapshot cannot hide a larger same-time peak.

## Next bounded slice: family 5 event implementation

Follow the fixed-size aggregate architecture boundary above: update same-time
current/peak at the existing `yu-types` reconciliation sites, retain a separate
call-local peak for the synchronous indexed-finalizer call, and let the solver
combine only owners known to remain live across that call. No per-growth
cross-crate callback or growing event history is authorized by this path.

Other established contract locators are the term-owner event tests near
`lib.rs:29462`, the yu-types indexed-probe case near
`crates/yu-types/src/lib.rs:3537`, normalization tests near
`f5c_normalization.rs:4792`, and instantiation resource cases near
`lib.rs:27413` and `27949`. They identify existing ownership behavior; none
was run for this map.
