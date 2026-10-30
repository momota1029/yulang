# R35 admission — source-owned callback annotation row

Admitted by Luna under the user's continuing Rust/Lean effect-hygiene and soundness authorization.

- Sprint: `EFFECT-PERMISSION-SOURCE-ROW/20261031-R35`.
- Contract SHA-256: `b222bb668f9c8f872dfc83a19c48c8ed937a6c5894f6e8ab5b50c5ef468ce570`.
- Input manifest SHA-256: `3fc84bb7e89a303149e8e8932b731f29e3bf3d63c171f834086b29677dffdb22`.
- R34 source-owner checkpoint: commit `90fd99073fa03da2cc1ba6aed3bff8e578b34020`, pushed to `origin/yulang3`. R34 source, proof and corrected proposal hashes are pinned in the manifest.
- Relevant source owner `source_annotation.rs`: SHA-256 `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`; `local_source.rs`: `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; HIR module: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; parse node identity: `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`.

## Exact assignments

- Rust `/root/effect_permission_r31_rust`: sequential source lease `tools/inference-playground/src/runtime/program.rs` (baseline SHA-256 `9823cd8d5c972e0c6ec2766d66f9d21c6564727317bc2646d2480a9e85132f74`) and `tasks/agent-loop/inbox/effect-permission-source-row-r35-rust.md`.
- Constructive Lean `/root/r35_proof`: `notes/theory/lean/YulangClosure/SourceCallbackPermissionR35.lean` and `tasks/agent-loop/inbox/effect-permission-source-row-r35-proof.md`.
- Independent review `/root/effect_permission_r31_review`: starts only after both producers stop writing; Luna records the read-only final handoff at `tasks/agent-loop/inbox/effect-permission-source-row-r35-review.md`.
- Luna: contract, manifest, this admission, `tasks/agent-loop/history/effect-permission-source-row-20261031-r35-stage-ledger.md`, `tasks/agent-loop/history/effect-permission-source-row-20261031-r35-outcome.md`, and `tasks/agent-loop/current.json`.

Live roster was synchronized: root is the only running coordinator; R34 Rust, Lean, reviewer and selector are terminal. The existing R17 WAITING worker and its held path lease remain unchanged. Before adding R35 assignments, current-state capacity accounting showed one counted reservation; after Rust, Lean and reviewer reservations it remains four, within the 12-slot limit. No UNKNOWN writer or quarantined path is released.

Fresh R35 envelope: 6,000 seconds (Rust 1,600; Lean 1,600; reviewer 1,200; Luna 1,600 including 500 closeout; Astra 0). No R34 balance transfer. Existing checkout only; no environment, worktree, copy, build, test, cache, target, extraction or scratch. `machine.rs` and `receiving.rs` remain excluded from all reads/writes.

Admission grants only the listed R35 packets and exact paths. It does not authorize source-to-Grant/runtime claims or closure of A/B, hygiene, soundness, principality, progress, termination or production. Rust and Lean producers may start after this receipt and synchronized current state; review remains NOT_STARTED until producer freeze.
