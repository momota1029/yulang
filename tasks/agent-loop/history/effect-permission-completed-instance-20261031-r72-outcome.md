# R72 outcome — CLOSED_INCOMPLETE / FIXED_GATE_REJECTED

**Disposition:** the fixed R72 gate is rejected. This is a research-only checkpoint; it does not close R66, original A/B, the source/native bridge, whole-language effect hygiene, soundness, principality, termination, or production.

## Goal and achieved Rust result

R72's goal was to construct the R71 `Package` from the actual completed Rust reification view, check exact fields and order, replay successfully, and apply the same R66 witnesses under the unchanged genuine Root premise.

The frozen Rust lane constructs an owner-borrowed `InventoryCompletedInstancePrimitiveProjection` from `InventoryCompletedReificationView`, reuses the existing branded Term and separate ComponentId tables, retains ordered facts/provenance/occurrences/edges and all four endpoint observations, and compares current Value/Effect bounds and representatives. Its source validation rejects mismatched owner/table rows, omitted/reordered/substituted facts and provenance, changed endpoints and invalid coordinates, keeping `SearchLimit` distinct from `BoundMismatch`. The receiver and handoff hashes are `9dfac06c82d62eb2c012f2f8b3a5affa6a85a397429302925463ee05a5cdf282` and `e6284d0dcb146a3e41f1dff9fba0e69a784e0a80b73021c25737fe41b2009a67`.

This is source inspection only. No Cargo/build/test/formatter was run; compiled Rust and runtime/resource equivalence remain UNKNOWN.

## Proof result and review gate

The Lean author constructed a decoder and same-R66-witness application, but used all four allowed probes. The last retained Lean run exited 1 on `accepted_package_fields` and `accepted_table_fields`. Two diagnostic-directed repairs followed that run and were never checked. Final Lean bytes SHA-256: `f06912ddec14c3b0223dbf44e531ea9600f6df8318cbff0139e90a6247149cab`. Retained proof handoff SHA-256: `fefef3e32fc2b200b0e78101f0d2de7cccb77c02727dc7aea76f3bd870fbadf1`. Attempt 1 completion remains UNKNOWN. No Lean proof-pass claim is made.

Fresh source-only review (`tasks/agent-loop/inbox/effect-permission-completed-instance-r72-review.md`, SHA-256 `f5ae8c9fd71a29dc7f1879f6cde5e09b39afae04c94300b47b7c0d052c13cff2`) found:

1. **BLOCKING:** final Lean artifact has no successful kernel check; pre-repair error-recovery audits report `sorryAx` for the two failed declarations.
2. **MAJOR:** Lean input checks accept duplicated and reordered `componentPositions`; the report gives a finite counterexample. Require exact ordered equality with `componentRows.zipIdx`.
3. **MAJOR:** Lean collapses the distinct native experiment/source-view owner into a HIR artifact identity and leaves owner readbacks unbound to the selected native owner. Preserve/check distinct identities and derive readbacks through the owner/view selection; do not assume blanket faithfulness.

Further native-only fields remain outside the Lean corruption model: source-view and slice pointers, acceleration maps, completed-edge duplicate `fact_index`, pointers, and duplicated identity/lower/upper edge fields. Rust validates some of these, but R72 Lean `Edge` does not represent all of them. The review found no compiled Rust failure. Genuine R66 `Root` remains a premise, not a constructed result.

The final proof and review were source-receipt audited; R72 static checker passed. That checker is tooling consistency only, not proof or independent review.

## Runtime, storage and Git

One checkout only. R72 created no new worktree, environment, dependency/configuration change, build, Cargo output, target, cache, formatter output, or scratch directory. Lean used pinned `--stdin`; failed inputs/outputs and hashes are retained in the leased proof handoff. At 2026-10-31 08:31 UTC, a read-only process-table query found no active pinned Lean process. The attempt-1 completion itself remains UNKNOWN and its time is not refunded or treated as success.

Both authors returned STOPPED / WRITES STOPPED. Reviewer returned STOPPED / WRITES STOPPED. Exact current-state records preserve attempt-1 UNKNOWN, all 32 pending items, and existing UNKNOWN/quarantined workers and paths; no capacity override was added.

R72 is closed as **CLOSED_INCOMPLETE / FIXED_GATE_REJECTED**. The fixed gate, inputs, all four probe dispositions, source/proof handoffs, review, and open obligations are preserved. No R72 retry or automatic fifth probe is authorized. A successor packet must be separately admitted with new artifacts and an explicit sequential lease handoff.
