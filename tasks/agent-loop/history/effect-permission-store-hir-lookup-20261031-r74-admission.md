# R74 admission — store-owned admitted HIR lookup

Luna admits `EFFECT-PERMISSION-STORE-HIR-LOOKUP/20261031-R74`, contract revision 1, as the next bounded continuation of the unchanged Yulang Rust/Lean objective. The dispatcher recommended a private `ConstraintStore` lookup and independent delta review. No user semantic decision or new production authority is needed.

R73 is closed `CLOSED_INCOMPLETE_FIXED_GATE_REJECTED` at `21cf99c051dbca3450ef184396e43a01f8dae323`. Its independent review found that the frozen candidate receiver calls missing `ConstraintStore::hir_for_occurrence` at lines 1058 and 1573. R73 finite Lean evidence remains accepted within its bounded model; it is not changed or rechecked here.

Contract: `tasks/agent-loop/sprints/effect-permission-store-hir-lookup-20261031-r74.md`, SHA-256 `e20477f1fea775ca9bd2cadc32dfff883d03833a0a68d8d08974486c1d63c1c1`.
Inputs: `tasks/agent-loop/sprints/effect-permission-store-hir-lookup-20261031-r74-inputs.json`, SHA-256 `12411b44a6fa42cd6f86030df9baf8318900ede3fc96ced3588b50afe0a0d676`.

The R74 Rust author receives exactly `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_receiver.rs`, and `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-rust.md`. The source/proof auditor receives only `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-proof.md`. The independent reviewer receives only `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-review.md`, after both authors stop. No overlapping writers.

The accessor must return `(index, borrowed Arc)` from this store's exact `hirs`, first validating `occurrence_hir_positions`, then falling back through that inventory. Preserve complete artifact identity and `require_owned`; retain the returned index directly at both receiver sites. No mechanical swap to an inference-session lookup.

Fresh 2,400s: Rust 450; source/proof correspondence 450; reviewer 750; primary 750 including at least 500 closeout; Astra 0. No compiler, Lean/Lake, Cargo, builds, tests, formatter, cache, target, scratch, worktree or environment. Only source inspection and `git diff --check`. No tests are added or run.

Preserve R72 attempt-1 UNKNOWN/unrefunded time, 32 pending items, unrelated UNKNOWN/quarantined paths, and the R24 capacity override. Same checkout only; no path beyond the exact leases above.
