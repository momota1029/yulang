# R282 — complete production-owner view for the R70 storage edge

Status: Luna preparation only until a fresh source-boundary referee passes. No
Sol proof, tests, builds, probes, Lean, Cargo, or code changes are authorized.
Parent remains the unchanged inference/evaluator soundness and Rust goal, with
the original source domain, quantifiers, Simple-sub A/B and semantics. Parent/A/B
is 0->0; R70 W and R71 remain open; implementation is NO_SAFE_CODE_SLICE.

## Fixed edge

Address only the row/level/bound/representative component of unchanged
`R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, at both production
`dispatch_live_item -> candidate_extrude` entries. Establish initialized dense
kind-separated storage from actual session entry; actual source component and
parameter level maps; fresh rows and level lowering; bounds, candidate graph
construction, forest initialization/growth, extrusion copies, selected-bound
replay/restoration, transaction rollback and every permitted resume path. No
manually fabricated native state. Leave other W clauses, `Need_D`, R71 and full
soundness open.

R281 remains INCOMPLETE/BLOCKING after a source-view review found omitted direct
owners. Preserve its frozen contract and artifacts; retain its complete 300s
charge. Its byte checks can be reused only for authenticated payload
correspondence, not coverage or cfg completeness.

## Source authority and exact view

Use the authenticated 36-path R255 manifest only, plus the already separately
authenticated `candidate_context.rs` pin
`a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`. Verify all
pins before rendering any source payload. R255 is inventory only.

Retain every valid R281 payload with exact original path, byte/char/line offsets,
file hash and payload hash. Add complete, nonoverlapping production definitions
for the omitted owners recorded by the R281 review:

- `candidate_extrusion.rs`: `candidate_begin_bound_restoration`,
  `candidate_drive_bound_restoration`, `candidate_replay_bound`;
- `candidate_scheme.rs`: `begin_candidate_fresh_bound`, complete
  `start_candidate_graph` including graph publication and forest initialization;
- `candidate_source.rs`: `begin_candidate_source`, `drive_candidate_source`;
- `lib.rs`: `begin_route_transaction_for`, `candidate_reopen_root`,
  `rollback_workspace`;
- `candidate_intrusion.rs`: `begin_candidate_extrusion`,
  `retain_extrusion_parent`, `finish_candidate_extrusion`.

For each owner derive the complete definition endpoint from source. Add the
state/type definitions and directly required internal owners for restoration
stages, source-driver resumptions, transaction snapshots/rollback, replay
completion, graph publication and forest growth. Preserve the already indexed
level-map writers, fresh allocation, `extrude`, merge, route rollback, both
dispatch branches and `candidate_context.rs` bounds/evidence owners.

Maintain a mutation-owner table for every direct callee that can affect row
existence, row kind, value/effect bounds, levels, representative forests,
restoration state, candidate graph state or transaction/resume state. Include
its complete indexed production body, or give a source-derived frame condition
that accounts for shared/interior mutable storage. Receiver spelling,
comments and bookkeeping labels are not frame proofs. Any unmapped
mutation-relevant callee blocks admission.

No registry/external body, parser/classifier, runtime or quarantined path is
permitted. Keep fixed `test=false` and feature predicates symbolic. Parse cfg
expressions structurally; omit a span only when its full predicate is false
under the production configuration. Record exact source offsets/lines, full
predicate, proof of falsity and SHA-256 for every omitted span. Preserve
interleaved test-only helpers and nested instrumentation as separate excluded
spans; never join the payloads around an omission. Ambiguous cfg ownership stops
preparation.

## Boundary gate and proof sequence

Freeze the versioned R282 ranges, exclusions, source view and byte index. The
fresh read-only source-boundary referee must authenticate all pins before
rendering any view bytes, then verify payload identity, exclusion disjointness
and cfg falsity, complete owner endpoints, mutation-owner closure and the actual
initialization supplier. This referee cannot later review the proof.

Only after boundary PASS, grant Sol/high up to 2,400s to construct the
constructor-preservation invariant and apply proved clauses at the unchanged
R70 edge. Preserve all R281 STOPs and charges. After Sol freezes, use a different
fresh independent proof referee, up to 1,200s. No stage renews or refunds a
charge.

Envelope: 4,800s total: Luna preparation/adjudication 600s; fresh boundary
referee 600s; Sol proof/application 2,400s; different fresh proof referee
1,200s. The next grant is boundary review only.

Suggested identities: `/root/r282_source_boundary_review`,
`/root/sol_r282_extrusion_entry_validity`,
`/root/r282_extrusion_entry_review`. Exact proof leases after boundary PASS:
`notes/theory/2026-11-03-extrusion-entry-validity-r282.md` and
`tasks/agent-loop/inbox/extrusion-entry-validity-r282.md`. Review receipt:
`tasks/agent-loop/history/20261103-r282-extrusion-entry-review.md`.
