# R74 Rust implementation — frozen handoff

Sprint ID / contract revision and SHA-256: `EFFECT-PERMISSION-STORE-HIR-LOOKUP/20261031-R74`, revision 1, `e20477f1fea775ca9bd2cadc32dfff883d03833a0a68d8d08974486c1d63c1c1`.

Assignment ID / handoff revision: `/root/r74_rust`, revision 1.

Parent gate / original theorem and scope locator: effect-permission owner-exact completed-instance bridge under unchanged original R66 A/B and source domain. R73's finite Lean result remains conditional and accepted only within its stated model; this implementation does not close the parent or promote production.

Baseline / dependencies: baseline commit `21cf99c051dbca3450ef184396e43a01f8dae323`; R74 inputs manifest SHA-256 `12411b44a6fa42cd6f86030df9baf8318900ede3fc96ced3588b50afe0a0d676`; contract SHA-256 as above. Before editing, both R73 Rust input bytes matched the manifest: `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`; `candidate_receiver.rs` `eb35c73ead829ed439a347d3cb665d52d3aa4b45b242c1155cfd4377a68d6415`. The R73 receiver changes remain the pinned input; this packet adds only the approved owner lookup and its two uses.

Role / worker / session: Rust implementation author `/root/r74_rust`; session `EFFECT-PERMISSION-STORE-HIR-LOOKUP/20261031-R74`; no descendants.

Requested model and effort / observed model and effort: `gpt-6-luna` / high requested by the packet; observed model and effort UNKNOWN (runtime telemetry unavailable).

Exact leased paths / author: `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_receiver.rs`, and this handoff only; author `/root/r74_rust`.

Outcome class: implementation; source-level store-owned HIR selection.

End-to-end behavior achieved: `ConstraintStore::hir_position_for_occurrence` returns `Option<(usize, &Arc<HirModule>)>`. It first consults `occurrence_hir_positions`, accepts that position only if its HIR fully owns the branded `HirOccurrenceId`, then falls back to the first fully owning HIR in this same store's `hirs`. `require_owned` is unchanged. At the completed projection validation site, the returned index is checked directly against the stored `artifact_index`, and the returned borrowed Arc is checked against the admitted inventory entry; full occurrence ownership and `require_owned` remain checked. At provenance reification, the returned index is stored directly, eliminating a separate pointer search over `store.hirs`. Both sites retain their prior `BoundMismatch` mappings; occurrence-row overflow remains `SearchLimit`.

Exact R74 source delta: added the private lookup after `ConstraintStore::require_owned`; at `candidate_receiver.rs` projection validation, replaced `session.store.hir_for_occurrence` with the tuple lookup and added direct coordinate equality; at provenance reification, replaced `hir_for_occurrence` plus `hirs.iter().position(ptr::eq)` with the tuple lookup and stored coordinate. No other R74 source edits. The complete checkout diff also displays pre-existing R73 receiver changes because those are uncommitted frozen inputs against the pinned baseline commit.

Parent/source/native correspondence: the selected coordinate is the index in the same `ConstraintStore.hirs` inventory validated by `require_owned`. Projection validation uses that coordinate against its borrowed admitted-artifact inventory and retains full branded occurrence validation. Reification records that exact coordinate beside the original occurrence identity for downstream projection validation. This addresses the R73 missing-method receiver defect and removes the unrelated pointer rescan. It is source inspection only: Rust type checking, compilation, and runtime behavior remain unverified.

Prior evidence reused / rejected: reused R73's frozen receiver projection, admitted-artifact inventory, branded occurrence identity, and R73 review's blocking observation that `hir_for_occurrence` was not defined on `ConstraintStore`. Reused the manifest pins as byte-preservation evidence. No Simple-sub bypass was restored or touched. Rejected treating source inspection as compiler success, native evidence, Lean closure, or parent-theorem closure.

Artifact locators / SHA-256 after edits:

- `crates/yu-solver/src/lib.rs` — `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745`
- `crates/yu-solver/src/candidate_receiver.rs` — `6452e18c32bd55e49b31a2dcd474d39140ca97b73ce71a0f4fede07d32b4840e`

Checks / coverage / resources: `git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/candidate_receiver.rs` passed. No build, test, compiler, Cargo, formatter, Lean/Lake, cache, target, scratch, environment, dependency, configuration, or Git mutation was run. Source-path inspection confirms indexed-owner validation then same-store first-owner fallback; callsite source inspection confirms coordinate retention and unchanged error variants. Indexed success, invalid/missing-index fallback, foreign artifact rejection, and same local ordinal across distinct brands were not executed. Active-work elapsed telemetry is UNKNOWN; the assignment stayed within its 450-second cap.

Mutual TODO for source/proof lane: confirm that the stored returned inventory position corresponds to the exact R73 admitted-artifact identity and that downstream `Readbacks`, `requireOwned`, and `decodeOwner` obligations preserve full branded identity and fallback semantics. Keep actual Rust compilation/runtime and Lean/native correspondence OPEN.

Remaining OPEN: Rust compile/type-check and runtime; exact Rust-to-Lean identity extraction; pointer/slice/map modeling; R73 finite Lean limitations; genuine R66 `Root`; original A/B; whole-language hygiene, soundness, principality, termination and production. No inference, constraint, propagation, routing, execution or `require_owned` semantics changed. No provisional cutover is claimed.

New path: this handoff only. Disposable scratch paths: none.

Worker state / writes stopped: STOPPED / WRITES STOPPED after freezing this handoff and the two leased source outputs; no descendants or remaining processes are claimed active. Runtime telemetry remains UNKNOWN.

Review / integration: frozen for fresh independent review and Luna adjudication; not self-certified, not integrated, and not a proof or production gate closure.
