# EFFECT-PERMISSION-EXPORT-WITNESS-20261028/r1 — independent review

Reviewer: `/root/export_witness_review` (`compiler_referee`), fresh non-author, read-only. Verdict: **BLOCKING + two MAJOR; sprint success unestablished**. Contract SHA-256 `06581e3741ddf8a330ba8c1975a35c80e2bda06ad8d00cff3030173c6b3a370f`.

## Findings

1. **BLOCKING — Rust instrumentation does not compile.** `FormalCaptureTypedEvent` is private in `candidate_effect.rs:130`, but sibling-module uses in `candidate_scheme.rs:1735,1752,3014` produce three E0603 errors. The feature-correct Cargo run stopped before either selected test ran. Any retry requires a fresh sprint.
2. **MAJOR — canonical representative q is recorded but not checked.** `candidate_effect.rs:3121` binds `_canonical_row`; subsequent checks at `3122–3126` check polarity, component and node only. Delegated checks at `3242,3256` accept any `EffectRow(_)`. Replacing q with r or `EffectRow(999)` while preserving other fields passes. Required `r → q` falsifier is not rejected. Fix by connecting q to actual captured node/native row identity and exercise real `r != q` transport.
3. **MAJOR — exported concrete permission metadata is not joined to its origin.** `candidate_effect.rs:3100` discards `Origin.concrete`; `3104–3111` compare occurrence/source row/path, while `3072` compares the two exports to each other. Giving both exports the same wrong concrete set passes. Compare each origin's concrete operands to its matched exported permission.

| Mutation | Rust static assessment | Lean fixed-snapshot assessment |
|---|---|---|
| Wrong owner wrapper | rejected by wrapped `SourceRootId::Definition` filtering/capture count | `wrong_owner_rejected` rejects |
| Omit second origin | rejected by `origins.len() == 2` and both joins | `missing_second_rejected` rejects |
| Swap sibling ports | rejected by per-origin node join and cross inequalities | `swapped_ports_rejected` rejects |
| Lose/alter `r → q` | **accepted** if only q changes | `lost_transport_rejected` rejects on fixed fixture |

The Lean result is bounded mathematics: the four results operate on a fixed fixture and are not decoded from the failed Rust run. Its decoder does not assume `Origin`, `Construction`, or export conclusions. Native snapshot authenticity is open: `CaptureSnapshot` supplies representative/node tables and `expected` constructs the expected returned port from those tables; consistent mutation of snapshot and observations can pass. The module and handoff disclose this boundary.

## Receipt verification

Cargo receipt hashes match handoff: stdout `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; stderr `31ab6b76ba9d8d36a685b62fd6eff90250a9cb9784d8e934322c51fe38e0434f`; resource `99f732595338e0f5a82b370ffb19f2dbc217f58e042a777e25df581f3c2879c8`; status `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`. Exit 101, 34.02s, peak RSS 1,157,496 KiB, zero swaps; three E0603 errors, zero tests.

Lean final `check-2.log` SHA `62ef00a0c5c4559206bddaa952f96049edd642a80d43924af5ccd0bac455fd9c`; audit-13 SHA `7e942192e271da7228b97275e8489cd0b2c2236399485fdfdcdac4151620d036`. All 13 complete type/transitive-axiom blocks present; build/audit exit zero. Reused ConstructorRealization 11 and SourceOrigin 12 prior audit receipts match; no fresh run of those 23 is claimed. Axiom sets stay within `propext`, `Classical.choice`, `Quot.sound`; arithmetic and five fixture results have no axioms.

Frozen hashes verified: Rust `candidate_effect.rs` `881e2051caa2d4f8c7af617a3a135f85eba33bf3ad375c2fd33b2afd8233fb3e`; `candidate_scheme.rs` `ef58ad40c63e09f64a419558618a311f9adffa94931e49129c09d738dfb95ad6`; Lean source `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`; proof handoff `6813f9cd03d5b43b15fb2e9d7624da7d5dbb1cdd24bd5d49acaaf193c638232b`; Rust handoff `b88a3b6e84c885ddbc0cbde5c7511c6e6434320ac2caa3f46b7e554655dee49a`.

Parent/source/native, A/B, effect-hygiene, principality, termination and production gates remain OPEN. **STOPPED:** reviewer performed no writes, Git operations, builds/tests/Cargo/Lean invocations or descendant dispatch.
