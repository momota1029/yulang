# Sprint EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1

Status: ADMITTED by Luna after verifying the exact frozen overlay, dependencies, outcome and fresh review. Continues the user's unchanged Yulang inference/executor soundness goal. The autonomous-continuation authorization is recorded in `AGENTS.md`; no renewed prompt is needed. Branch `yulang3`.

## Original obligation and boundary

Preserve the original quantifiers and source domain in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, and effect-hygiene semantics in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5. No source restriction, solver/preflight/recovery/API/production behavior or expected-output change. Parent, native, A/B, effect-hygiene, principality, termination and production gates remain OPEN.

Prior sprint outcome: `tasks/agent-loop/history/effect-permission-export-witness-20261028-r1-outcome.md`, SHA-256 `0abb4a4eecb4a0b02e04cc1c7180793e4f66a470df25f80a548e034cc302d657`; review: `tasks/agent-loop/inbox/effect-permission-export-witness-review.md`, SHA-256 `9e4eb22d9bd8911880deb7eaf6a0119c66603991567dc45fadae7f4ba79711ac`.

## Frozen baseline and pins

Committed baseline: `43b06a4a3`, plus exact frozen dirty overlay (re-leased only to the Rust lane):

- `crates/yu-solver/src/candidate_effect.rs`: `881e2051caa2d4f8c7af617a3a135f85eba33bf3ad375c2fd33b2afd8233fb3e`
- `crates/yu-solver/src/candidate_scheme.rs`: `ef58ad40c63e09f64a419558618a311f9adffa94931e49129c09d738dfb95ad6`
- `crates/yu-solver/src/shadow_apply.rs` (read-only): `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/Cargo.toml` (read-only): `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- Checked `FormalPermissionSourceOrigin.lean`: `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`
- Checked `FormalPermissionConstructorRealization.lean`: `70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`
- Checked `FormalPermissionExportWitness.lean`: `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`
- Prior Rust handoff: `b88a3b6e84c885ddbc0cbde5c7511c6e6434320ac2caa3f46b7e554655dee49a`; proof handoff `6813f9cd03d5b43b15fb2e9d7624da7d5dbb1cdd24bd5d49acaaf193c638232b`; independent review as above.

Preserve all prior raw Cargo and Lean receipts under `/tmp/yulang-effect-permission-export-witness-20261028-r1/` and all earlier identity-repair receipts. New scratch roots only:

- Rust: `/tmp/yulang-effect-permission-canonical-export-20261028-r1/rust-target/`
- Lean: `/tmp/yulang-effect-permission-canonical-export-20261028-r1/lean-project/`

## Decisive outcome

Repair the two reviewed gaps using the same typed origin through actual captured endpoint and exact owner export:

1. Record capture-time representative `q` from the actual canonical captured node/row identity, with the same capture, original allocation row/witness `r`, endpoint polarity and node index. The verifier must fail if only `q` changes to `r` or another row. Exercise a genuine unequal transport `r != q`; merely comparing recorded values is insufficient.
2. Preserve each `Origin.concrete` and compare its resolved concrete operands against that exact origin's exported permission metadata, alongside wrapped source owner, occurrence, complete path/source row, capture id, endpoint polarity, intern/export node equality and actual returned permission port. Changing both exports to the same wrong concrete set must fail.
3. Narrowly expose `FormalCaptureTypedEvent` to its sibling only through internal test-only visibility; no public API or non-test visibility expansion.
4. Keep the checked decoder `FormalPermissionExportWitness.lean` immutable. A new Lean module may instantiate it from frozen Rust evidence with explicit identity encoding and checks for altered q and identical wrong export metadata. Supplied tables remain explicit conditional inputs; do not claim native snapshot authenticity or universal source/native simulation.

Required Rust evidence: focused feature-correct ordinary-source tests run successfully. If two attempts are needed, preserve both; the second is allowed only after a diagnosed first failure and source repair, and both together stay within 180 seconds. Required independent review: mutate q to r/another row and mutate both exports to an identical wrong concrete set while leaving origin/capture data intact; both must be rejected against unchanged captured-row/origin evidence. Also recheck wrong owner, omitted second origin, and swapped sibling ports.

If authentic native q or concrete operands cannot be derived, stop and report the exact first unsatisfied source-to-observation transition. Passing tests or fixed tables do not close the original parent theorem.

## Rust lane — Luna/high

Write leases only:

- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/effect-permission-canonical-export-rust.md`

Read-only dependencies are the frozen paths/hashes above. Keep `shadow_apply.rs`, manifests, checked Lean modules and prior receipts unchanged. No other repository source paths.

Make the event record sibling-visible only under `#[cfg(test)]` or an equally narrow private internal mechanism. Tie q to the actual captured node's canonical Effect row; retain r→q and polarity; compare intern/export node identity with the actual returned port. Preserve and join `Origin.concrete` to its matching export. Include a genuine r≠q case. Keep all origins, exact wrapped owner, occurrences and complete paths. No solver semantics, source preflight, recovery or outputs change.

Before each allowed Cargo invocation, freeze current input hashes and exact argv, verify no competing Cargo/rustc process and >=4 GiB available memory, CPU0 pin, one Cargo job, <=2 GiB RSS and 180-second combined wall cap. Feature-correct argv must include `--features shadow-apply-candidate`; filter only the two selected `formal_permission_constructor_` tests with one test thread. Store separate raw stdout/stderr, status, `/usr/bin/time -v`, input manifest and argv hash under the leased Rust root. Never retry without a diagnosed failure and changed/frozen source.

## Lean lane — registered `lean_prover`, after Rust freeze

Write leases only:

- `notes/theory/lean/YulangClosure/FormalPermissionExportWitnessNative.lean`
- `tasks/agent-loop/inbox/effect-permission-canonical-export-proof.md`

The existing three checked modules and all prior audits are read-only. Decode/instantiate only from frozen Rust observations and explicit identity mappings. Do not assume origin/construction/export conclusions. Add theorem checks that altered q and matching wrong concrete sets fail only when checked against unchanged explicit captured-row/origin data. Retain exact type and transitive axiom audits. State native snapshot authenticity and source-wide realization as open if not proved.

Maximum one serialized Lean/helper invocation, 120 seconds total, one CPU, <=1 GiB RSS. Retain all inputs, argv, stdout/stderr/time/status/axiom logs and hashes. No retry in this sprint.

## Review, resources and stop conditions

After both lanes freeze, assign a fresh non-author read-only `compiler_referee` to verify final hashes/raw receipts, Rust placement and all five falsifiers. Reviewer cannot certify own work. Max two producers, zero Astra. Heavy work serialized.

Total envelope **1,500 seconds**: Rust600, Lean450, review250, Luna100, selector50, contingency50. Stop on changed pins, overlapping/unknown writer, unsupported native correspondence, any surviving required mutation, resource/budget exhaustion or user STOP. Do not alter quarantined/unrelated paths.

At sprint end, freeze outcome, synchronize compact current state without dropping unresolved entries/quarantines, consult `next_action_selector`, and leave parent/native/production gates OPEN. Only Luna integrates, stages explicit accepted research paths, commits and pushes after exact-range review.
