# R280 owner-coverage gate STOP — INCOMPLETE

Contract `tasks/agent-loop/sprints/extrusion-entry-validity-r280.md`, SHA-256
`62f30fb184086090765fb1cb746252417090b65e98dfa083bb849dbce70a7a62`.
Worker `/root/sol_r280_extrusion_entry_validity`, coordination session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; requested Sol/high, observed model and
effort UNKNOWN. The full 300-second reservation is charged; no extension or
refund. No descendants, writes, tests, builds, probes or code edits occurred.

After all 36 R255 hashes and the separate `candidate_context.rs` pin matched,
Sol's source-interval renderer emitted nested `cfg(all(test, feature =
"f5c_resource_probe"))` fragments and `cfg(test)` forest instrumentation while
reading production function intervals. This crossed the contract's explicit
no-test-body-rendering boundary. Sol stopped immediately; no proof or source
conclusion is certified. Initialization ownership remains unclosed. Preserve
R279-r3 STOP and the external-body restriction. No proof-stage grant or output
lease is issued under R280.

Exact displayed source intervals, partial owner map and final cessation/resource
receipt are pending Sol's stop-only message; this record does not claim those
unreported details. Parent/A/B remains 0->0; R70 remains open; implementation
`NO_SAFE_CODE_SLICE`.

## Final Sol receipt

Sol's final message confirmed all reads stopped, no pending writes or descendants.
The exact partial map and boundary incident follow; no further source read was
performed to refine these intervals. The full 300-second grant remains charged;
observed post-GO clock span was 18:13:01–18:14:37 UTC (96 seconds), CPU/RSS
unmeasured.

Partial owners: `lib.rs::try_new` 10087–10474 (empty/kind-separated tables,
parameter rows, source-level initialization); `fresh_value_at_level`
10521–10546; `fresh_effect_at_level` 10552–10582; `candidate_source.rs::initialize_candidate_source_levels`
2292–2328; `candidate_intrusion.rs::representative` 119–127,
`settle_candidate_intrusion` 568–597, `merge_candidate_rows` 599–706;
`lib.rs::finish_route_transaction*` 9554–9611,
`rollback_route_transaction` 9711–10079 partially inspected; and
`dispatch_live_item` 14537–14976, with R70 branches at 14822 and 14835.
This is incomplete coverage, not an invariant proof.

First unresolved initialization supplier: actual producers of
`batch.candidate_source.component_levels` and `.parameter_levels`; formal
registration producer is also unmapped. Failure/resumption remains open:
`rollback_route_transaction` calls `state.refresh_bytes()?` at 9767 before row
restoration beginning 9807; its failure/resumption effect was not audited.
Potential required owners are `candidate_scheme.rs::refresh_bytes` (1711) and
`lib.rs::resume_typed_drain_route` (14529). No source-reachable invalid state
was shown.

The interval renderer displayed forbidden nested test fragments:
`lib.rs` 10540–10544, 10576–10580, 9771–9806, 9826–9827, 9848–9849;
`candidate_intrusion.rs` 106–118, 129–150, 606–607, 674–678, 686–690; and
within `lib.rs` 19080–19280, visible fragments 19101–19102, 19132–19139,
19233–19234, 19249–19250, 19267–19279. Truncation prevents claiming an
exhaustive narrower inventory. Treat the gate as scope-breached and invalid for
technical review; do not render those ranges again.
