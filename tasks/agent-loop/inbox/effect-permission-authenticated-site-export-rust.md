# Rust handoff — EFFECT-PERMISSION-AUTHENTICATED-SITE-EXPORT-20261028/r1

Handoff revision: 3  
Contract SHA-256: `4088b7dc1d357f1eb531d76ea01951630e8baf2b092856936c4e0a65f2ed77b9`  
Assignment: authenticated actual-constructor source→capture→exact-owner export observation  
Role requested: `implementer`, Luna/high  
Role/model observed: UNKNOWN (runtime metadata unavailable)  
Worker state: STOPPED after invocation 2; no further Cargo invocation or source write remains in this packet

## Lease, authorship and frozen artifact

Writable leases only:

- `crates/yu-solver/src/candidate_effect.rs` — edited by this worker; invocation-1 source SHA-256 `3e44df6b089beabf7b8c6c0e85d7985131979f167d3ac14cfa447d8b0710d848`; current revised, unexecuted source SHA-256 `6f20ac00deb2f5a84f57a0cf54cf9ceb64f2de5a90d15cc371240d9de68dfa3b`.
- `crates/yu-solver/src/candidate_scheme.rs` — unchanged by this worker; intake SHA-256 `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.
- This inbox file — handoff revision 3.

No other repository file was written. Scratch and frozen run descriptions are only under `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/`. The restored prior handoff path was not accessed. Its contract-recorded restored SHA remains `08760fd52e67d3b405638c8b378e98915ca903be7a96b4840aade071f5c2000f`.

## Implementation result and source/native correspondence

The observation now snapshots `SourceAnnotation` at the actual `candidate_formal_annotation` boundary under `cfg(test)`, retaining the borrowed annotation identity, exact owner, occurrence, parameter offset, scope and enclosing annotation position. Both observation paths consume this trace from the same HIR passed to `CandidateInference::solve` and exported by that HIR's owner. They no longer reconstruct a second `CandidateSourceSession` or index its schedule with an owner from a different lowering.

An independent Function/Tuple walk records every node, its full path and optional `SourceEffectRow`. A separate recurrence predicts the constructor's postorder Function child Effect-port visits, including optional rows and exact concrete/variable row data. Tests compare actual visits and their order to that recurrence. An explicit root row is retained by the tree observation and asserted to have no direct Function child-port visit. Each ordinary origin keeps its own owner/occurrence/parameter/enclosing position/path/nested row/concrete operands/allocation witness, then joins the actual canonical `Capture::intern` endpoint, materialized graph `Node::Row`, and exact returned owner permission port.

Delegated ordering now uses the full key `(constructor, owner, occurrence, parameter, enclosing annotation position, full path, nested row)`. The symbolic fixture has two sibling delegated sites under one annotation, distinct concrete rows `[io]` and `[state]`, and a shared `'e` memo. Each site has its own port order `0,1`; the test joins each keyed port through canonical intern and materialized graph row.

Observation event/state types and added capture state/call arguments remain `cfg(test)`. The non-test `candidate_signature_effect` signature and call path contain no `site_occurrence`, `site_parameter` or `site_path` fields. `candidate_scheme.rs`'s already-pinned capture events remain unchanged and test-only.

The original `r != q` assertion remains in its original unequal-transport test. Equality `r == q` is asserted only in the identity observation. No semantic behavior, public API, expected output, solver recovery or source domain changed. This is provisional test-only source evidence; it does not close unequal transport or any parent/proof/production gate.

## Review defects and falsifiers

The four reviewed implementation defects are addressed in the leased Rust source: (1) contradictory identity equality is gated away from the original unequal assertion; (2) constructor inputs come from the exact executing boundary/HIR; (3) delegated port order is keyed by the full source site; (4) observation-only parameters are absent from non-test signatures/call paths.

Invocation 1 reached and passed the same-HIR constructor snapshot, separate tree/Effect-port recurrence comparison, both source-origin joins, exact owner/capture/export row checks, bounded identity equality, distinct sibling q rows and sibling-port swap assertions. The subsequent existing consumer assertion failed at `state remains in the returned computation`; this consumer result is unexplained and remains **OPEN**. The failure occurred before the wrapper reached the two-site delegated observations, so those were **NOT_REACHED** in invocation 1. The original unequal assertion remains verbatim in `formal_permission_constructor_owner_domain_graph_export_observation(true)` and was not run by invocation 1.

Invocation 2 compiled the revised source and passed the combined identity plus two-site delegation wrapper. It reached the actual constructor snapshot/tree recurrence and source→allocation→canonical capture→materialized node→exact owner export joins; both distinct source origins and sibling ports remained separate. The q-substitution, same-wrong-concrete-set, wrong-owner, omitted-origin and swapped-sibling-port assertions all ran and passed. Both delegated source sites under the shared annotation were visited with distinct full keys, each two-port order was checked, and the shared-tail memo hit/miss assertions passed. The original `r != q` assertion and consumer assertion were not part of this identity-only wrapper and remain preserved in their original unequal fixture/path. No unequal-transport or consumer-pass claim follows.

The current source separates the identity fixture from the original consumer fixture: identity-only observations use distinct `[io]`/`[state]` nested rows and an explicit `[audit]` root row; the unequal path keeps its original `[io]` fixture and the consumer assertion `state remains in the returned computation`. The original `r != q` assertion remains unchanged and in place. This source revision has not been executed; invocation 1's result does not validate it.

Prior source/Lean evidence reused: admitted contract pins, prior site-export outcome/review and checked `FormalPermissionSiteTraversal` plus export decoders. The previous `FormalPermissionSourceTransport.lean` failed result remains unaccepted and was not imported. The earlier owner lookup via an independently lowered session is rejected as source evidence. No source/native parent theorem or A/B premise is closed.

## Frozen inputs and static checks

The invocation-1 pre-run inventory had 271 entries and SHA-256 `0894dc924354a2bc731b469c433b3d1beeba9e922b1baf441afdd6a264ff92c6`. The revision-2 complete input inventory for the revised source and amendment 01 has 272 entries at `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/input-inventory.json`, SHA-256 `8b6f6a5addda6d3e8e65d35e6f34e8ee4311069433a6220717811a104d9cf17b`. It covers workspace manifests/lock, local source trees compiled by `yu-solver --lib`, pinned source/proof/review artifacts, the governing sprint contract and amendment 01. All 272 entries rehashed with zero mismatches before freezing. Direct dependencies and complete input set are pinned by that inventory; source hashes above are repeated separately for review.

Completed static checks and runtime receipt:

- `git diff --check -- crates/yu-solver/src/candidate_effect.rs crates/yu-solver/src/candidate_scheme.rs` — passed.
- `bash -n` on the two frozen run scripts — passed.
- Inventory verification: revision-2 inventory has 272 entries, including amendment 01 and the current Rust sources; zero mismatches — passed.
- Static `rg` audit: all observation events are `cfg(test)`; the production `candidate_signature_effect` declaration has only semantic inputs (`context,row,family,polarity,variance,level,variables,views`).
- Invocation-2 launcher `bash -n` — passed before release. Invocation 1 compiled and failed at the consumer assertion described above. Invocation 2 compiled the revised source and passed its one focused test. No additional check or third invocation was run.

## Frozen invocation plan — requires fresh release for each

Both feature-correct invocations share a hard 180-second total. Invocation 1 used 61.11 seconds; invocation 2 used 6.53 seconds under its 30-second wall timeout plus two-second TERM grace. Combined measured wall time was 67.64 seconds. One CPU (CPU 0), one Cargo job, offline/locked resolution, one test thread, and one shared isolated `CARGO_TARGET_DIR` were fixed in both scripts. `/usr/bin/time -v` records peak RSS and wall/CPU time. Invocation-1 preflight observed 22,010,777,600 bytes available, CPU 0 affinity bind succeeded, and no process with exact executable name `cargo`, `rustc`, `lake` or `lean` was active. Invocation-1 peak RSS was 1,671,992 KiB; invocation-2 peak RSS was 1,122,284 KiB; neither exceeded 2 GiB or timed out. The mounted cgroup reports `memory.max=max` and is read-only; therefore the 2 GiB RSS ceiling was monitored by the frozen `time` receipts, not claimed as OS-enforced. No runtime budget remains assigned to Rust.

Invocation 1 was the identity plus two-site delegated wrapper, run once against the frozen pre-run source:

- Frozen argv JSON: `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/receipts/invocation-1/argv.json`, SHA-256 `278b65ca3e5e671b44847cbbfeb502835ad0b3601439a0a7d6c061fd5a913529`.
- Frozen launcher: `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/receipts/invocation-1/run.sh`, SHA-256 `1f9c3a8bd4e5a66ea1c8c08f82892093ec832b29231cc2006cf48ab937db17ff`.
- Test filter: `candidate_effect::tests::formal_permission_site_export_identity_and_delegation_observation` (`--exact`).
- Separate receipts: `stdout.txt`, `stderr.txt`, `status.txt`, `time.txt` in that invocation directory.
- Result: exit status `101`; elapsed wall time `61.11 sec`; peak RSS `1,671,992 KiB`; not timed out. The observed assertions and consumer failure are described above. Raw SHA-256: stdout `f14a53f49e04248ad17ef8627c482f48a01f3c20471c7a419a24f2c4d5c72075`, stderr `ea89a302aa41f9e01661ab89bb9286b7a4a71faf13110b7e9e06e671bdfa270b`, status `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`, time `4b8b0ea2c2e3c5b48b45e0b70ed77b5f98618e9a224f31ee0a069561ec076647`.

Invocation 2 ran the repaired combined identity-and-two-site-delegation wrapper. The identity branch returned after bounded identity/source/capture/export assertions, leaving the unrelated consumer output assertion solely on the preserved original unequal path:

- Frozen argv JSON: `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/receipts/invocation-2/argv.json`, SHA-256 `70faf60f7405ced97fe9feb0c1104d34f185bc4ed91455bdfcf82bf968f9e965`.
- Frozen launcher: `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/receipts/invocation-2/run.sh`, SHA-256 `829b32c07b3940d8433aad725f2aef1290884aa66276b72c5e3ec1d17fb079ac`.
- Test filter: `candidate_effect::tests::formal_permission_site_export_identity_and_delegation_observation` (`--exact`).
- Separate receipts: `stdout.txt`, `stderr.txt`, `status.txt`, `time.txt` in that invocation directory.
- Result: exit status `0`; elapsed wall time `6.53 sec`; peak RSS `1,122,284 KiB`; no timeout. Output reports `1 passed; 0 failed`. Raw SHA-256: stdout `c17bcb837dee9da1c529418b9598d9e1870effe2c4b9872b223ab48c1ba5120a`, stderr `595f10df6d692ddd165a8d17ea5dc6469665b7c413818ef446d27dc067e28497`, status `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa`, time `9d0cef65e812fd4ecbb287ca27e45cc61eef71ee7be15393a6f5adcd39bbd57a`.

Both exact argv vectors use `/home/momota1029/.cargo/bin/cargo test --offline --locked --manifest-path crates/yu-solver/Cargo.toml --features shadow-apply-candidate --lib <test-filter> -- --exact --test-threads=1`, under CPU-0 binding and the frozen offline/one-job/target-dir environment. A failed or timed-out invocation consumes its slot; no retry. The revision-2 complete 272-file inventory is `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/rust-target/input-inventory.json`, SHA-256 `8b6f6a5addda6d3e8e65d35e6f34e8ee4311069433a6220717811a104d9cf17b`; it includes amendment 01, the exact revised `candidate_effect.rs` run by invocation 2 and unchanged `candidate_scheme.rs`, and rehashed with zero mismatches before release. Invocation-1 pre-run inventory was 271 entries and SHA-256 `0894dc924354a2bc731b469c433b3d1beeba9e922b1baf441afdd6a264ff92c6`. Invocation 2 had the required fresh Luna release; no third invocation is authorized or performed.

## Open premises, TODOs and next step

- Unequal representative transport remains OPEN; invocation 2 is a falsifier/observation of the existing claim and may fail without changing it.
- The Lean source/native decoder instance and full theorem/axiom audits remain owned by the proof lane; no supplied observation list is promoted to a theorem.
- Fresh independent review remains required for snapshot authenticity, tree/constructor visitation correspondence, cfg(test) erasure, exact-owner joins, five falsifiers and all receipt pins.
- Original parent theorem, source/native correspondence, A/B, hygiene/principality/termination and production gates remain OPEN.

Next in-envelope action: no Rust execution remains in this packet. The run scripts and target directory are disposable scratch for primary-only hygiene; no cleanup was performed.

All Rust writes and Cargo work are stopped after freezing invocation 2. No commit-ready milestone or independent review is claimed.
