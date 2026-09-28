# F5c remaining physical-owner event map

Status: updated after the reviewed §34 family-5 aggregate-peak checkpoint. All
eight §34 families now have static owner-event or reconciliation coverage; the
full runtime fold remains unverified. No test, matrix, preflight, benchmark, or
measurement ran for this checkpoint.

Authority: F5 §26/§34 in
[`F5 foundation`](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
the Authoritative
[`no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md),
and the current
[`no-cap scale plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).

The covered event categories are §34 family 1 (`live_variable_tables`), family 2
(`inference_type_arena`), family 3 (`structured_pair_memo`), family 4
(`component_expansion_memo`), family 5 (`closed_type_arena`), family 6
(`closed_normalization_index`), family 7 (`generalization_scratch`), and family
8 (`instantiation_substitution`). The sidecar retains `family5_event` for
semantic family 6 because event kinds 584–611 occupy its prior numbering slot;
its older `family6_event` names semantic family 7 for compatibility. Family 5
uses the feature-gated fixed summary in `yu-types`, not per-owner sidecar IDs:

| §34 family | Matrix lanes | Owner and current evidence | Terminal owner state |
|---|---:|---|---|
| 2 `inference_type_arena` | 18–23 | Implemented and independently reviewed; see [`family-2 event checkpoint`](f5c-family2-inference-type-arena-events-checkpoint-2026-09-29.md). | Six event lane totals reconcile at FinishOutput; every retained owner transfers under the same ID into `SolvedModule.store` and remains live at EOF. |
| 4 `component_expansion_memo` | 45–64 | Implemented and independently reviewed; see [`family-4 event checkpoint`](f5c-family4-component-expansion-memo-events-checkpoint-2026-09-29.md). | All 20 lane owners release on clear/drop; terminal current capacity and retained bytes are zero while event peak remains. |
| 5 `closed_type_arena` | 65–100 | Implemented and independently reviewed; see [`family-5 aggregate-peak checkpoint`](f5c-family5-closed-type-arena-aggregate-peak-checkpoint-2026-09-29.md). The feature-gated fixed summary folds the current 36 lanes and retains their same-time cross-call peak. | At FinishOutput, 17 scratch and 11 indexed lanes are zero; the eight permanent arena lanes remain in the solved closed-type owner. |
| 6 `closed_normalization_index` | 101–128 | Implemented and independently reviewed; see [`family-6 event checkpoint`](f5c-family6-closed-normalization-index-events-checkpoint-2026-09-29.md). Thirteen base and fifteen flat physical-index lanes use same-time owner events. | All index lanes reach zero; output lanes 21–26 transfer the same IDs into staged buffers. |
| 8 `instantiation_substitution` | 230–236 | Implemented and independently reviewed; see [`family-8 event checkpoint`](f5c-family8-instantiation-substitution-events-checkpoint-2026-09-29.md). | Seven event lane totals reconcile at FinishOutput; all scratch owners release and family-8 current capacity/bytes are zero at EOF. |

Existing snapshots and per-owner ledgers now have a fixed aggregate high-water
for every §34 family. The row and checker still need a runtime replay to verify
the combined event order, aggregate tuples, and terminal transfers.

## Next bounded slice: full eight-family replay and diagnostic plan

Review the completed family-aware checker and the fresh process plan before any
preflight. The old 39-process campaign remains stopped; the corrected guarded
cycle companion raises its state counts to 8M/16M/32M, so include a bounded
diagnostic and host-memory monitoring. The user's standing authorization is to
continue F5c autonomously, including expanded time and memory plans, without
repeated approval pauses. Preserve the fresh review gate, written
performance-auditor justification, primary budget decision, and exact process
and host-memory monitoring records for the corrected workload.

Architecture correction: the finalizer resets `self.peak_bytes` from
`retained_bytes_before` at each attempt, so its existing
`ClosedTypeAccountingCheckpoint::peak_bytes_during_call()` is call-local. A
separate call-peak field would duplicate that evidence; the missing quantity
was the fixed cross-call simultaneous peak because the 36 individual lane
peaks may occur at different times.

Other established contract locators are the term-owner event tests near
`lib.rs:29462`, the yu-types indexed-probe case near
`crates/yu-types/src/lib.rs:3537`, normalization tests near
`f5c_normalization.rs:4792`, and instantiation resource cases near
`lib.rs:27413` and `27949`. They identify existing ownership behavior; none
was run for this map.
