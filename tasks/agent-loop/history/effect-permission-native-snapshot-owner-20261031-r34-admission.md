# R34 admission — constructor-owned snapshot binding

Status: ADMITTED by Luna for the ongoing user-authorized Rust/Lean effect-hygiene goal. This continues the fixed objective after R33 closed incomplete; it changes no accepted semantics and opens no quarantined path.

## Frozen admission inputs

- Baseline branch/HEAD: `yulang3` / `afd05a2aaec63890629d97a663a7aff54574075b`.
- R33 outcome: `tasks/agent-loop/history/effect-permission-native-callback-coordinate-20261031-r33-outcome.md`, SHA-256 `e08958ea2dc101948c2632fde7ce68ba90ba87fe50008971d184034297865f7b`.
- R33 review intake: SHA-256 `6413a347f4593ed61d9154331a54e5a3186b91161598c09152ec652e9d6044a8`.
- R33 conditional module: SHA-256 `9d138f84ede8c38161195fad4a324d9f164a72632dcfa575b5a5197d2685a436`; exact R32 prefix 48,478 bytes, SHA-256 `bf2908ae347814c71ddc32ffae0f64a62103b855d96655a47aa1b9db0dc9690c`.
- Source owner `tools/inference-playground/src/runtime/program.rs`, SHA-256 `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`.
- HIR module `crates/yu-hir/src/module.rs`, SHA-256 `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- R30 archive/member hashes and Lean v4.35.0/toolchain/authority hashes are pinned in the R34 input manifest, SHA-256 `57c07d14d9074a50e55c1b116c656599240883e61879b214f53448005da8e8ca`.
- R34 contract SHA-256 `e81a6b7316623bc009f6f1488fdf5d9ba6e258efe9e6144d164f5c81d1061ff2`.

## Authorized outcome and exact leases

Rust may edit only `tools/inference-playground/src/runtime/program.rs` to bind an opaque owner token to the exact retained `Arc<HirModule>` and expose clone-preserving `Arc::ptr_eq` identity. It also owns `tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch` (proposal only for quarantined consumers) and `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-rust.md`.

Lean owns only `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean` and `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-proof.md`. It preserves R33/R32 prefixes and uses pinned v4.35.0 stdin under read-only bwrap.

Fresh independent reviewer owns only `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-review.md`, and starts only after both producers freeze. Luna owns the R34 contract/manifest/admission/stage ledger/current/outcome and exact-lease reconciliation.

Fresh envelope: 6,000 seconds (Rust 1,600; Lean 1,600; review 1,200; Luna 1,600 including 500 closeout; Astra 0). No R33 time transfer. No worktree, copy, environment, build, Cargo/Lake, test, target/cache, scratch, extraction or access to `machine.rs`/`receiving.rs`. The serialization consumers remain QUARANTINED; their integration is proposed only. No production promotion follows this owner slice.

The owner token wraps a clone of the retained HIR `Arc`, so a token retains its owner allocation and `Arc::ptr_eq` distinguishes independently allocated snapshots without counters, Debug, or structural equality. Identical HIR content in a different allocation remains a different snapshot. This design is subject to source and independent review; any mismatch or constructor bypass stops the packet.

## Dispatcher and runtime truth

`next_action_selector` independently recommended closing R33 incomplete and pursuing constructor-owned snapshot binding, with no worker start or file write. Luna verified the pinned `program.rs`/HIR module sources and admits the exact source lease above. Producer dispatch is a separate event and will be recorded only after live-roster confirmation.
