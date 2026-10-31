# EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1 — Rust handoff

Sprint contract revision and SHA-256: `EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1`, `70a69a66a9367114a70970d73825942bfebfc08a2143b7288f057b76088aaf4b`.

Assignment / handoff revision: `EFFECT-PERMISSION-CANONICAL-EXPORT-20261028-rust`, revision 3 (final after both released attempts). Revision 1 and 2 run inputs remain retained under the leased scratch root.

Parent gate: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5; effect-hygiene semantics at `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5. Parent, source/native, A/B, effect-hygiene, principality, termination and production gates remain OPEN.

Baseline / dependencies: committed baseline `43b06a4a3` plus the admitted Rust overlay. Read-only dependencies are unchanged: `shadow_apply.rs` SHA-256 `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`; `crates/yu-solver/Cargo.toml` SHA-256 `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`; checked Lean source-origin SHA-256 `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`, constructor-realization `70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`, and export-witness `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`.

Role / worker / session: Rust implementation lane / `/root/effect_permission_identity_repair_rust` / current sprint session. Requested model and effort: Luna/high. Observed model and effort: UNKNOWN (not exposed by worker runtime).

Exact write leases and authorship: `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/candidate_scheme.rs`, and this handoff. Scratch only `/tmp/yulang-effect-permission-canonical-export-20261028-r1/rust-target/`. No Git mutation.

Outcome class: provisional test-only source-native instrumentation; final focused run failed required assertions. `FormalCaptureTypedEvent` is `pub(super)` under `#[cfg(test)]`, fixing the prior sibling-module visibility error without non-test/public expansion. After capture expands a node, a typed event reads the materialized `Node::Row` and actual `Graph.rows` `RowKey::Effect(q)`, keyed by capture, node index and polarity. The origin join ties that event to the same capture-time `CanonicalIntern` event carrying witness, raw allocation row `r`, canonical endpoint and interned node; it checks node/polarity and exact returned owner port. Each matched origin’s retained `concrete` operands are compared directly with that exact exported permission’s `permitted()` slice. Existing wrong-owner, missing-second-origin and sibling-port swap assertions remain. Memo/delegated typed row joins are implemented, but run 2 stopped before their final assertions.

No semantic, solver API, preflight, recovery, production or output behavior was changed. Prior review found missing actual captured-row linkage and dropped `Origin.concrete`; the implementation now records q from the actual captured graph row and joins each origin's concrete operands to its own exported metadata. Run 1 showed the previous ordinary-source fixture yielded `r=q` for both origins, while a symbolic memo-name filter omitted the leading quote. The bounded fixture change kept both annotated sibling paths and changed the owner body to recursive self-use (`= f pair`) along the existing source-qualified recursive extrusion path; the filter was corrected to `"'e"`. Run 2 still yielded `r=q` for both source origins, `[(21, 21), (23, 23)]`, failing the strict inequality assertion. The symbolic test passed the memo-count check but then failed its exact delegated source-site join (`delegated_sites.len() == 0`, expected `1`); the assertion does not expose which source-site field prevents the match. No nontrivial representative was synthesized. This lane stops at the observed source-to-captured-row transition.

Frozen source hashes:

- `crates/yu-solver/src/candidate_effect.rs`: `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1`.
- `crates/yu-solver/src/candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.
- Read-only `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.
- Read-only `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`.

Static checks: `git diff --check -- crates/yu-solver/src/candidate_effect.rs crates/yu-solver/src/candidate_scheme.rs` passed after the bounded fixture/filter edits. No Cargo, rustc, test or formatter process was launched after those edits.

Frozen Cargo argv for the one pending attempt (argument string; no wrapper included in argv hash):

```text
cargo test --offline -p yu-solver --lib --features shadow-apply-candidate formal_permission_constructor_ -- --test-threads=1
```

Argument-string SHA-256: `dc7290d49e009ab374ab6670fa909b770ca0d0159717617b17ea3b0cd2a9a8c5` (unchanged). Run 1 used the exact argv under CPU 0, one Cargo job and leased target dir; `/usr/bin/time -v` recorded 60.14 seconds elapsed and 1,664,404 KiB maximum RSS (zero swaps), below the caps. Run 1 exited 101 after both tests ran. Because 60.14 seconds of the combined 180-second wall cap are spent, run 2 is frozen with a 115-second timeout, CPU 0 pinning, one Cargo job and the same target dir; total scheduled cap is 175.14 seconds. The second invocation remains unlaunched pending fresh primary preflight and explicit release.

Proposed run-2 wrapper (not part of the Cargo argv hash): `taskset -c 0 /usr/bin/time -v -o /tmp/yulang-effect-permission-canonical-export-20261028-r1/rust-target/run2.resource.txt timeout --signal=KILL 115s env CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-effect-permission-canonical-export-20261028-r1/rust-target/ cargo test --offline -p yu-solver --lib --features shadow-apply-candidate formal_permission_constructor_ -- --test-threads=1`.

Run-1 scratch receipts under `/tmp/yulang-effect-permission-canonical-export-20261028-r1/rust-target/`: `argv.txt` SHA-256 `d6b02a48057fb449343626e2227782694caecc27e69eede75439360ab70780b2`; `input-manifest.txt` SHA-256 `cdb711a83ddf6f112c018bf213814feb11911db2018052bc267fd0de92672164`; `stdout.raw` SHA-256 `52d9087cee1645fae6a6059ba14031b44440f76c0b69caa93becb7848ba32ad2`; `stderr.raw` SHA-256 `769ef306a8483e9a857f8cad992c3adc53d30540a4e91c0cfc7349dd3c888c8e`; `status.txt` SHA-256 `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`; `resource.txt` SHA-256 `e4c31d12b183ed71b922b772352cdf19ee6c8ac521716cd96a9062e38622419c`.

Run-2 frozen input receipts: `run2.argv.txt` SHA-256 `d6b02a48057fb449343626e2227782694caecc27e69eede75439360ab70780b2`; `run2.input-manifest.txt` SHA-256 `5861edfe681e4e77ce58cf1b9939763fde8b40fd11bf6c7e0940ea5bac99e6eb`. Run-2 outputs: `run2.stdout.raw` SHA-256 `80ee9e2b8507487ae9bf54ac384d27855bda80f28760062fd449baa592c2a9ff`; `run2.stderr.raw` SHA-256 `723ecc0fd959ee61ec7d1e7c561e0fd3ce32d9353bd1a0ccdfd1eb675668e484`; `run2.status.txt` SHA-256 `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`; `run2.resource.txt` SHA-256 `f7611a0302d40d26fb69e50e2aecdbb871758643880b252de7dbcebb768cb55e`.

Run-1 result: exit `101`; both selected tests ran and failed. `formal_permission_constructor_owner_domain_graph_export_join` failed the `r != q` assertion with ordinary-source transports `[(19, 19), (21, 21)]`. `formal_permission_constructor_symbolic_effect_memo_hit_miss_and_delegation` failed `memo.len() == 2` because the filter used `"e"` while the trace records `"'e"`; the dump contains one miss and one hit for row `3`, witness `[2]`. It used 60.14 seconds elapsed, 1,664,404 KiB peak RSS and zero swaps. Run 2 used 6.40 seconds elapsed, 1,116,748 KiB peak RSS and zero swaps. Aggregate elapsed was 66.54 seconds; both invocations exited 101. No process remained after either run.

Run-2 result: exit `101`; both selected tests ran and failed. The owner-domain test passed its per-origin path/concrete/actual row/node/port joins before failing only the required nontrivial transport assertion with `[(21, 21), (23, 23)]`. The symbolic test passed memo count/name and paired delegation checks, then failed the delegated source-site match (`0 != 1`) before tail/port materialization assertions. No retry remains in this sprint.

Parent application and remaining evidence: the Rust tests check a finite ordinary source construction only. The new capture event is tied to a graph materialized node/row, but successful compilation, genuine `r != q` observation, actual runtime test results and independent mutation review remain pending. No claim of native snapshot authenticity or universal source/native simulation follows. Exact required falsifiers: alter q to r or another row, alter both exported concrete sets identically while origin/capture evidence stays fixed, wrong owner wrapper, omit the second origin, and swap sibling ports. If authentic nontrivial transport cannot be observed, report the exact first missing source-to-captured-row transition.

Worker state at revision 3 freeze: STOPPED; all leased source edits and handoff are frozen; both authorized Cargo invocations are spent; no Cargo/rustc process remains. No further source, scratch-receipt or invocation work is authorized by this handoff.
