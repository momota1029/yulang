# R67 admission — owner-scoped qualified-read reification

Sprint: `EFFECT-PERMISSION-QUALIFIED-REIFICATION/20261031-R67`, contract revision 1, SHA-256 `bc04c56942bd1078c9415fdac5cf4c11001948255fcfd8f4473aa81f5098211f`.

Dispatcher consulted at the R66 boundary. Recommendation: reify actual borrowed `InventoryPackage` fact/provenance rows into finite owner-scoped readers and prove R65/R66 lookup commutation; no stale 2026-10-19 R67 contract reused.

Baseline: branch `yulang3`, local HEAD and verified origin HEAD `5ca4363b55ae2637b6858406fd85cce96bca28cc`. R66 status `CLOSED_BOUNDED_PASS_RESEARCH_ONLY`, outcome hash `24e41d60e902cad84ff4c56fb1edeb34c6975199d910a8af1596efd72c7f8c5e`, fresh independent review PASS hash `ac56e01d6ec413a96d12fc0f3b4664f8a926d0c55196886dd884aa7569c4534b`.

Live collaboration roster synchronized immediately before admission: only `/root` active; all prior R63–R66 lanes and selector returned completed. No R67 author/reviewer is yet RUNNING. Existing dirty/untracked work and all UNKNOWN/quarantined leases are preserved; no path overlap is assigned. The current snapshot retains all 32 pending records and the existing 13-slot capacity-release receipt; no additional capacity release was applied.

Exact direct dependency pins and scope are in the contract. Assigned paths are disjoint: Rust owns `candidate_receiver.rs` plus its handoff; Lean owns the new R67 module plus its handoff; the reviewer is read-only and Luna persists its report. Resource cap is 6,000 seconds: Rust 1,400; proof 2,200; review 1,200; Luna 1,200 including 500 closeout; Astra 0.

No tests, Rust build, Cargo, Lake, cache, target, scratch, environment or worktree are authorized. Static current-state check passed before admission.
