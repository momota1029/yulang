# EFFECT-PERMISSION-EXPORT-WITNESS-20261028/r1 — Rust handoff

Sprint contract revision and SHA-256: `EFFECT-PERMISSION-EXPORT-WITNESS-20261028/r1`, `06581e3741ddf8a330ba8c1975a35c80e2bda06ad8d00cff3030173c6b3a370f`.

Assignment / handoff revision: `EFFECT-PERMISSION-EXPORT-WITNESS-20261028-rust`, revision 2 (final; revision 1 was the pre-run freeze).

Parent gate: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, and the preserved effect-hygiene semantics in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5. The universal parent and production/native gates remain OPEN.

Baseline / dependencies: committed baseline `43b06a4a3` with the admitted Rust overlay listed in the contract. No dependency changes. `crates/yu-solver/Cargo.toml` SHA-256: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`; read-only `shadow_apply.rs` remains `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`. Checked Lean dependencies remain `FormalPermissionSourceOrigin.lean` `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd` and `FormalPermissionConstructorRealization.lean` `70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`.

Role / worker / session: Rust implementation lane / `/root/effect_permission_identity_repair_rust` / `EFFECT-PERMISSION-EXPORT-WITNESS-20261028/r1`. Requested model and effort: Luna/high. Observed model and effort: UNKNOWN (not exposed by the worker runtime).

Exact leased paths and authorship: `crates/yu-solver/src/candidate_effect.rs` and `crates/yu-solver/src/candidate_scheme.rs` edited by this worker; this handoff file owned by this worker. `shadow_apply.rs`, Cargo manifest and Lean sources are read-only. No Git mutation.

Outcome class: provisional implementation instrumentation; compile attempt failed before test execution. The two selected constructor tests now use typed test-only records for wrapped `SourceRootId`, occurrence, full source path, source row, allocated row/witness, capture identity, explicit original-row-to-canonical-Effect-endpoint transport, polarity and interned node index. Tests join every origin to the actual exact-owner exported permission metadata and port identity, check both sibling origins and cross-swap rejection, verify `parameter_live_base + parameter`, and connect memo/delegated-tail identity separately from two ordered signature Effect-port allocations. Multiple origin witnesses may be retained for one numeric row. No semantic, API, preflight, recovery or output behavior is changed.

Frozen source hashes:

- `crates/yu-solver/src/candidate_effect.rs`: `881e2051caa2d4f8c7af617a3a135f85eba33bf3ad375c2fd33b2afd8233fb3e`.
- `crates/yu-solver/src/candidate_scheme.rs`: `ef58ad40c63e09f64a419558618a311f9adffa94931e49129c09d738dfb95ad6`.

Feature-correct Cargo argv (single invocation, released by Luna and launched once):

```text
cargo test --offline -p yu-solver --lib --features shadow-apply-candidate formal_permission_constructor_ -- --test-threads=1
```

Cargo argv SHA-256: `dc7290d49e009ab374ab6670fa909b770ca0d0159717617b17ea3b0cd2a9a8c5` (exact argument string above).

Execution wrapper: `taskset -c 0 timeout --signal=KILL 180s env CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-effect-permission-export-witness-20261028-r1/rust-target/ cargo test --offline -p yu-solver --lib --features shadow-apply-candidate formal_permission_constructor_ -- --test-threads=1`. Raw stdout and stderr were captured separately; `/usr/bin/time -v` and exit status were retained. No retry.

Preflight observation: `MemAvailable` was `22,458,384 kB`; no Cargo/rustc process was present. Luna separately reverified source hashes, >=4 GiB available memory and no competing cargo/rustc process before releasing. Focused test filter matched exactly the two selected Rust tests. `git diff --check` passed for the two leased Rust sources before launch.

Run receipt: exit status `101`; wall `34.02 s`, user `29.63 s`, system `3.13 s`, CPU `96%`, peak RSS `1,157,496 KiB`, swaps `0`. The single run stopped during compilation with three `E0603` errors: `FormalCaptureTypedEvent` is private to `candidate_effect` but used from `candidate_scheme` at lines 1735, 1752 and 3014. No selected test ran. No retry was made; a further Cargo attempt requires a fresh sprint. Raw outputs under `/tmp/yulang-effect-permission-export-witness-20261028-r1/rust-target/`: `stdout.raw` SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0 bytes); `stderr.raw` SHA-256 `31ab6b76ba9d8d36a685b62fd6eff90250a9cb9784d8e934322c51fe38e0434f` (7,973 bytes); `resource.txt` SHA-256 `99f732595338e0f5a82b370ffb19f2dbc217f58e042a777e25df581f3c2879c8`; `status.txt` SHA-256 `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`.

Source/native correspondence and open TODO: the Rust trace is finite source-native evidence only. The independent Lean lane owns a decoder/instantiation from these typed constructor events to the existing audited source-origin and constructor-realization relations, with successful native capture/export and transport stated as explicit gaps unless derived. The original source-domain universal, A/B, effect-hygiene, principality, termination, production and native gates remain OPEN.

Worker state: STOPPED; source writes frozen; Cargo process exited and no cargo/rustc child remained on the completion check. No further writes or invocations. The existing identity-repair raw logs remain retained under `/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/`.
