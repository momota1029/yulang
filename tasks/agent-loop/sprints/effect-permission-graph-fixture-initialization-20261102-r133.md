# R133 — restore Graph field initialization in two existing fixtures

Status: ADMITTED for bounded source candidate and independent static review.
Branch / baseline: `yulang3`, `cd460e0faf2c9ba2ba21a10f3dd83ed7bb1f4609` (`origin/yulang3`).

## Original outcome and success evidence

Parent goal remains Yulang soundness and the original Simple-sub A/B obligations.
This packet is a narrow Rust fixture-construction repair; it closes no theorem,
source/native, effect-hygiene, consumer or production gate.

In the committed `crates/yu-solver/src/shadow_apply.rs`, two `candidate_scheme::Graph`
struct literals omit the required `lambda_argument_effects` field introduced in
the committed Graph type. The literals are in
`candidate_graph_row_hashing_matches_identity` near line 4951 and the canonical
row-equivalence fixture near line 5064. Add exactly
`lambda_argument_effects: Vec::new(),` to each literal. Preserve every existing
fixture value and assertion. Do not import observer hooks or other working-tree
changes.

## Exact baseline and dependencies

- `crates/yu-solver/src/shadow_apply.rs`: 275,872 bytes,
  SHA-256 `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`.
- `crates/yu-solver/src/candidate_scheme.rs`: 508,255 bytes,
  SHA-256 `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`.
- `crates/yu-solver/src/candidate_intrusion.rs`: SHA-256
  `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`.

The only candidate source output is `crates/yu-solver/src/shadow_apply.rs`,
constructed from the pinned committed blob. Expected target: 275,970 bytes,
SHA-256 `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`.
The two added fields belong to the committed `Graph` type and initialize its
required vector to the empty value appropriate for these unrelated fixtures.

## Lanes, limits and review gate

Implementer: registered Luna/high lane, 180 seconds. Exact sole output lease:
`tasks/agent-loop/inbox/effect-permission-graph-fixture-initialization-r133-source.md`.
The worker reconstructs and hashes the exact target in memory, records the
complete unified patch and confirms author STOP. No Rust source write.

Fresh independent `compiler_referee`, 120 seconds, read-only. Review the exact
handoff/hash, confirm both literals and their Graph type, require exactly the
two field additions, and verify all fixture/assertion content otherwise remains
byte-identical. Any extra required field, wrong type/cfg, source/hash mismatch or
additional source change blocks this packet.

No compiler, Cargo, tests, Lean, checker, storage/environment probe, scratch,
source materialization or build output. Total sprint cap 600 seconds; Astra 0.
No theorem or language semantics change. After a PASS, Luna may integrate and
push only the exact target above under the user's standing request to analyze
Rust and push coherent reviewed work. That source checkpoint remains uncompiled
and untested, and all parent gates remain OPEN.
