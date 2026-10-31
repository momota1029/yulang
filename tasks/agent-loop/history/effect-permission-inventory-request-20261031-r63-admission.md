# R63 admission — owner-derived inventory/request package

Status: **ADMITTED_BOUNDED_RESEARCH**. Primary: Luna (`/root`). Admission date: 2026-10-31.

Contract: `tasks/agent-loop/sprints/effect-permission-inventory-request-20261031-r63.md`, revision 1, SHA-256 `5570818da03080050d0ac5b29474e84ae31084efd319555232e2250c6ac13a74`.

## Authority, baseline, and bounded outcome

This continues the explicit original Yulang soundness/effect/principality/termination goal under its unchanged source semantics and parent quantifiers. No production or semantic authority is added. R62 closed as bounded research only; Rust-to-inventory/request projection and actual outer successful `Run` remain OPEN.

Baseline HEAD and `origin/yulang3`: `b32651e265d0184c8bff92cfe5511a56eca591cb`. R62 outcome SHA-256 `f8195a9ac73ad6eeb14e4c7f21a454cd8536201d59c66a9a7a19865667298b47`; fresh independent R62 review SHA-256 `113041f925ee3e13824d4eb2ded34903c23fa1e6ac96dcb4867a5d3a379177e5`.

Admitted outcome: privately construct, in memory and fallibly, the R55/R57 source/native inventories and Internal/Entry/Catch request coordinates from the existing Rust owner projection; construct the corresponding typed Lean package; prove only the exact equations needed to apply R62 to these constructed values. Preserve raw/canonical coordinate separation and distinct semantic/collected fact namespaces. Reject foreign or incomplete owners. No pointer casts, disk serialization, state dumps, effects on inference or subtraction, or package faithfulness assumed wholesale.

## Exact leases and budget

- Rust `/root/r63_rust`, Luna/high, 1,800 seconds: `crates/yu-solver/src/candidate_receiver.rs`; `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-rust.md`.
- Proof `/root/r63_proof`, `lean_prover` Sol/high, 1,800 seconds: `notes/theory/lean/YulangClosure/RustInventoryRequestR63.lean`; `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-proof.md`.
- Fresh reviewer `/root/r63_review`, compiler_referee Sol/low, 1,200 seconds after both authors STOP: `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-review.md`.
- Luna primary integration/state/Git: 1,200 seconds including 500 closeout. Total cap 6,000 seconds. No Astra, descendants, new worktree/environment/cache/target/scratch/build directory. Rust build/test/Cargo/formatter are outside the contract. Lean audit is pinned 4.35.0 stdin-only.

Exact direct code/model pins are in contract revision 1, including the five Rust owner files and the accepted R39/R45/R47/R48/R49/R54/R55/R57/R58/R59/R60/R61/R62 Lean modules. Each lane must rehash its direct inputs before writing and return to Luna on drift.

## Live roster and capacity

The primary synchronized the live agent roster at the R62 boundary. R62 authors/reviewer are STOPPED; the next-action selector returned its R63 recommendation and completed. The old `/root/r63_view_coverage_review` worker is not present as a live agent; its assignment row remains UNKNOWN and its exact report path remains QUARANTINED. No such path is leased or reused here.

The existing user-authorized capacity override is already RELEASED for 13 stale assignment reservations in `tasks/agent-loop/history/20261030-r24-capacity-release-supplement.md` (SHA-256 `37301a1c7aa006c59c2ec2d11ab26672ffbcfc8b8eff73610e2afad20c668414`). This admission applies no new capacity override and does not count those slots again. All worker observations remain UNKNOWN where previously UNKNOWN; all 12 quarantines and pending count 32 remain intact. The R63 authors are not yet spawned at this admission receipt; exact actual IDs/session receipts will be recorded only after supported spawn calls.

## Stop conditions and open obligations

Stop for an unrepresentable source identity, incomplete owner inventory, required edits to a read-only source owner, dependency drift, observable behavior change, review scope expansion, or budget limit. Parent A/B, complete outer Rust-to-Run, arbitrary resource/failure correspondence, whole-program soundness, effects, principality, termination, full hygiene, and production remain OPEN. No worktree, build, cache, target, scratch or compiler test was created or run for this admission.
