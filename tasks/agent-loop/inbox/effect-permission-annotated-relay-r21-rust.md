# R21 Rust source/native probe handoff — revision 1

Sprint `EFFECT-PERMISSION-ANNOTATED-RELAY/20261030-r21`; contract SHA-256 `ee69548873e5f9d288676a5e8f9ac45b2c1962507cd339eba12e0c149111638c`; input manifest SHA-256 `b70ac05c738f29ecd7c233f137f56dd9b333ff5a36f95ac9a99510344b00ab46`.

Assignment `/root/effect_permission_annotated_relay_r21_rust`; requested registered role/model/effort `implementer` / `gpt-6-luna` / `high`; observed model/effort `UNKNOWN` / `UNKNOWN`. No descendants. Work was restricted to the six leased Rust source paths, this handoff, the JSON receipt and `build-target`.

## Result

Outcome: **probe compile-blocked before runtime; no source/native trace produced**. The single authorized locked/offline Cargo invocation exited 101 after 40.491725894 seconds while compiling the new test in `lib.rs`. Its complete argv, raw stdout/stderr, status and sampled resources are retained in `isolated/ep-annotated-relay-r21/project/receipts/annotated-relay-receipt.json` (final SHA-256: `bc22d7eec58ae1a1c430e9892a431e8cbc713aaaf1e566b993a2e9eb1b51acea`). The test emitted no records. No Cargo retry occurred.

The two diagnostics were both local to the new instrumentation: (1) `CandidateGraphExport` has no `value` field; (2) `unresolved` is a method, not a field. After the invocation, the formatting expression was corrected to use `graph.unresolved()` and `graph.node_count()`. That correction is **uncompiled and unverified** because the packet permits one Cargo invocation total. The exact Rust source bytes at invocation time are identified by `lib.rs` SHA-256 `7a3b96ff378ee79661ce6c79d2bbf5524557ca7777805be4bfcd109dffa0134f`; final `lib.rs` SHA-256 is `3b51520c2dadb6ab929e0bf750cb6cf332c952f1b983e7aab16859808beb3270`.

The exact first observed evidence edge is **Cargo test compilation -> candidate trace execution**: it is absent because compilation failed, so source occurrence, invocation, owner, candidate permission/contribution records and runtime events were not observed by this probe. The intended semantic first missing edge remains the prior owner-path obstruction: candidate source/captured permission and contribution evidence -> authenticated same-invocation callback/computation execution event -> exact local Catch selection; for the companion, local `signal` handling -> same-invocation surviving `write` -> outer `receive` consumption. A caller-supplied invocation label is only a probe-group key and does not establish this bridge. R20 `Session::take` is outside scope and no journal transition is inferred.

## Correspondence and evidence reused

The attempted test uses the exact approved callback text from policy §1.1 (SHA-256 `163fb480ec7ecaed2c341253066a7c6cc3af1a0cf5499c384f0cad4952c64e18`) and separately `include_str!`s `original-suffix-outer-receiver.yu` (SHA-256 `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7`). The intended typed ordered records had distinct probe/source hash/source occurrence/invocation/owner/event IDs and only candidate-graph permission/contribution events; they did not claim execution selection. Because the test never ran, neither source has a trace, output value, selected Catch, or residual-consumer observation.

Reused the reviewed R24 callback bridge outcome and permission implementation audit: the relay's nested callback-result permission is retained by the candidate constructor, while the runtime lacks an authenticated callback-result receiving view/boundary and same-event Catch route. This is prior source-owner evidence, not evidence from this Cargo run. R20's failed native-prefix compilation and its `Session::take` question are not reused as current runtime evidence. No Simple-sub bypass or changed semantics was restored or introduced.

## Files, hashes and checks

Final source hashes:

- `crates/yu-solver/src/lib.rs`: `3b51520c2dadb6ab929e0bf750cb6cf332c952f1b983e7aab16859808beb3270`
- `candidate_effect.rs`: `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717` (unchanged baseline)
- `candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` (unchanged baseline)
- `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` (unchanged baseline)
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` (unchanged baseline)
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` (unchanged baseline)
- JSON receipt: `bc22d7eec58ae1a1c430e9892a431e8cbc713aaaf1e566b993a2e9eb1b51acea`

Check: exactly one `cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib r21_annotated_relay_trace::r21_annotated_relay_two_source_occurrences_keep_identity_separate -- --nocapture`; exit 101 during compile; no test body ran. CPU affinity was one CPU; sampled available RAM before launch was 28,663,705,600 bytes; sampled process-tree peak RSS was 53,575,680 bytes; limits were 180 seconds / 2 CPU GiB / minimum 4 GiB available RAM. Active time spent: 40.492 seconds of 900; no remaining Cargo invocation in this assignment. Astra: zero.

Only new generated/scratch path is leased `isolated/ep-annotated-relay-r21/project/build-target/` (Cargo compilation outputs). No other scratch paths, fixture edits, manifest/lockfile changes, Git operations, or main-tree writes. The receipt and this handoff are the only other new paths.

## TODO and boundary

TODO to Luna, request `R21-RUST-COMPILE-TRACE-01`: after this assignment is frozen, a fresh authorized check must establish that the corrected test compiles before any trace claims are considered. Inputs: this exact revision and current `lib.rs`; output: a new versioned isolated receipt/path under Luna-granted lease. Falsifier: any compile failure or trace record lacking a unique actual source occurrence and owner binding. A subsequent runtime owner must authenticate call entry/return, exact operation event, callback/computation identity, Catch owner/selection, result `1`, and for the companion the distinct surviving `write` contribution reaching outer `receive`. Current assignment cannot retry Cargo or extend its lease.

All Rust writes stopped after freezing this handoff and the JSON receipt; no running process or descendant remains. Trace and cutover are provisional/unavailable, all parent proof/source/native/production gates remain open, and independent review plus Luna adjudication are pending.
