# R22 outcome: preflight rejected before execution

Sprint `CALLBACK-RESULT-OWNER-CONSUMER/20261030-R22` closes as **`CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`**. The selector directed closure after the second source preflight rejection. The exact Rust observer revision did not receive the contract-required ACCEPT, so Cargo was not run. No runtime trace or compiler counterexample exists. The Lean candidate was frozen but not checked.

The admitted [contract](tasks/agent-loop/sprints/effect-permission-owner-consumer-20261030-r22.md) has SHA-256 `cd656fba688ee8c6ffc0dd16fe9d8a0925bb52692f44521615c331fbf0767afb`; its [input manifest](tasks/agent-loop/sprints/effect-permission-owner-consumer-20261030-r22-inputs.json) has SHA-256 `dd6f0b9d11e9076e1c1089ce9af1eb692a71c9e699c1f612c91a953d2cc221be`. Baseline: `fcd38f02a33cb28b2c5c56dc6f1a48b8838e1dc4`. The source domain and original A/B claims remain unchanged. Neither source case supplies identity or premises to the other.

## Rust source and preflight

The [frozen source snapshot](tasks/agent-loop/history/effect-permission-owner-consumer-20261030-r22-rust-snapshot/README.json), README SHA-256 `bfb1e3c05f4d8c3b15b191ea90111e89da96d0c9be8f469bc34c6646c5a0980d`, contains the exact three isolated runtime files. Their SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| `machine.rs` | `2e118422c44e8849529e6bfe9bb4dd31fdd565aa6a121c6d4d18295dc5f36d1a` |
| `receiving.rs` | `8b507eef8dde72a0cd277e4bdbf8df8005b989745054c45b73ef78adbc1a076a` |
| `program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |

The first preflight rejected a stale baseline/hash set; no Cargo command followed it. A later fresh preflight authenticated the final hashes above and rejected the observer for four blocking issues:

1. The callback-use observation at `machine.rs:2552` is outside the relevant binding scope and follows the request. The test configuration cannot compile with that placement; the observation belongs at the successful `callback_use` constructor near line 1656.
2. `same_source(lambda, apply)` equates distinct lambda-definition and body-Apply occurrences. The join must use their actual enclosing lambda/formal ownership while preserving distinct occurrence identity.
3. The validator requires Request → Catch → integer → ResultConsumer, while `OperationResultConsumer` around `machine.rs:1400–1417` starts callback execution before `execute_with_substitution` emits Request around line 3000. It must check the real transition order and shallow-handler lifetime/discard path.
4. Request and selection payload IDs, selected `arm` identity, and entry formal-receipt identity are ignored; Name-receipt/schema mismatch rejection is missing.

The referee spent approximately 190 seconds across the two preflight attempts; the estimates are not instrumented, with approximately 110 seconds left in the shared 300-second budget. That remainder could not reliably cover both another substantial preflight and a final evidence review. No ACCEPT was recorded. The selector therefore directed preservation of the rejected bytes without a Cargo attempt.

The isolated source snapshot is provisional failure evidence, not accepted instrumentation. The root worktree's dirty/quarantined `machine.rs` and `receiving.rs` were not used as R22 inputs or modified by this closeout.

## Lean candidate

The frozen [Lean module](notes/theory/lean/YulangClosure/CallbackResultOwnerConsumer.lean) has SHA-256 `8b76265d486786844bb1e649ac676fe49988b903e742532d40b86104c8783f27`. It contains 15 candidate theorem declarations. The [proof handoff](tasks/agent-loop/inbox/effect-permission-owner-consumer-r22-proof.md) has SHA-256 `33e7d229fd136be5db96c498f7e4d175712f2ddcc8d80d5ff9d02cba4e456bcb` and the scratch frozen manifest has SHA-256 `75c5136a851fdefb16ab45b25ae0958a5d86b25f06e42beb70efc0c6f5e96ef0`. Lean/Lake/version checks and theorem/axiom audits are **NOT_RUN**: the contract requires the sole Cargo invocation to be terminal first, and the preflight gate rejected the sources before Cargo. The declarations have no checked kernel types or per-root axiom reports. The model does not establish Rust correspondence, a committed Catch returning `1`, or the companion `write` consumer.

## Gates and next evidence

The two approved source cases remain independent. No source occurrence, runtime owner, invocation join, permission/contribution event, Catch selection, callback return `1`, or residual `write` consumer was observed. Original parent A/B, source/native correspondence, effect hygiene, soundness, principality, termination, and production remain **OPEN**. No semantics, fixtures, expected output, or production code changed.

All three R22 lanes are STOPPED. The live roster showed each R22 identity completed; a process scan found no R22, Cargo, rustc, Lean, or Lake process. Rust and Lean writes are frozen. The R22 leases are recorded as FROZEN in the [state snapshot](tasks/agent-loop/history/effect-permission-owner-consumer-20261030-r22-state-archive.json); only those nine resolved R22 leases are removed from current capacity accounting. Historical quarantined leases remain unchanged.

The selector's next proposal is a source-derived callback observer and validator that first establishes the actual transition order and distinct lambda/Apply coordinates, then checks payload/arm/formal identities and Name-receipt/schema rejection. A successor needs a new exact contract with adequate preflight and final-review time reserved from the outset. This proposal grants no lease or production authority.

Machine-readable details: [R22 evidence](tasks/agent-loop/evidence/effect-permission-owner-consumer-20261030-r22.json). Primary Git receipt will be recorded separately at [tasks/agent-loop/history/effect-permission-owner-consumer-20261030-r22-git-checkpoint.md](tasks/agent-loop/history/effect-permission-owner-consumer-20261030-r22-git-checkpoint.md) after the coherent closeout checkpoint is pushed.
