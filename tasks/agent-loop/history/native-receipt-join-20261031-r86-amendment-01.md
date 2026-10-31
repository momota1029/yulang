# R86 Amendment 01 — pin the initialization and rollback dependency

Sprint: `NATIVE-RECEIPT-JOIN/20261031-R86`  
Base contract SHA-256: `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`  
Baseline: `a44adf1f2fda99f896debf11b5f58c207728b030`.

## Evidence and added read scope

The admitted seven-file inventory located `start_candidate_graph` in `candidate_scheme.rs:2456–2478`: it creates a fresh `GraphState::default()`, calls `state.intrusion.effect_algebra.initialize()?`, then installs `self.candidate_graph = Some(state)`. Whether Origins/completions are initially empty therefore depends on the actual `candidate_intrusion` / `candidate_effect` defaults and initializer, which were outside the original manifest. The admitted `lib.rs:9746` also dispatches `state.intrusion.rollback(...)`; the context rollback body alone does not establish the full owner rollback equation.

Add exactly these read-only inputs, pinned by full-file SHA-256 in the amended R86 input manifest:

- `crates/yu-solver/src/candidate_intrusion.rs` — `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`, 31,786 bytes.
- `crates/yu-solver/src/candidate_effect.rs` — `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`, 354,102 bytes.

Inspect only defaults, initialize, rollback, state replacement/restoration and their direct receipt/completion dependencies. No recursive module expansion. Any further external owner becomes an exact open premise; do not inspect it under this amendment.

## Lane and resource boundary

This amendment changes no proof/source claims, semantics, production authority, or existing output lease. The same source worker may read these two files only after this amendment and the updated manifest are committed and pushed. Its added time is at most 300 seconds and at most its actual remaining portion of the original 1,000-second source budget, whichever is smaller; the budget does not reset. No new worker, Astra, execution, build, test, environment, cache, target, scratch or Git authority is added. The proof lane continues unchanged.

The source handoff and fresh review must distinguish what the admitted closure proves from any remaining external initializer or rollback dependency. If the remaining source budget is insufficient, stop and record the exact unresolved dependency.

All other R86 contract limits and leases remain unchanged. This amendment is primary-owned and must be pushed before the newly admitted files are read by the source lane.
