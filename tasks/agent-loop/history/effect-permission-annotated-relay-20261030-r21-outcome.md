# R21 outcome: compile blocked before runtime

Sprint `EFFECT-PERMISSION-ANNOTATED-RELAY/20261030-r21` is **`CLOSED_INCOMPLETE — COMPILE_BLOCKED_BEFORE_RUNTIME`**. Independent review accepts preserving the failed experiment only. No source/runtime correspondence, Lean theorem, parent result, or production change is established.

The frozen [contract](../sprints/effect-permission-annotated-relay-20261030-r21.md) has SHA-256 `ee69548873e5f9d288676a5e8f9ac45b2c1962507cd339eba12e0c149111638c`; its [input manifest](../sprints/effect-permission-annotated-relay-20261030-r21-inputs.json) has SHA-256 `b70ac05c738f29ecd7c233f137f56dd9b333ff5a36f95ac9a99510344b00ab46`. Baseline: `4bb23ea31e5bb434313e073df1d68f477b54326f`.

## Rust probe

The sole authorized command was:

```text
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib r21_annotated_relay_trace::r21_annotated_relay_two_source_occurrences_keep_identity_separate -- --nocapture
```

It exited 101 after **40.492 seconds of Cargo elapsed time**, while compiling the test in `lib.rs`. The test body did not run and stdout contains no trace. The complete invocation, raw streams, status and sampled resource observations are preserved in the [Rust receipt snapshot](effect-permission-annotated-relay-20261030-r21-rust-snapshot/annotated-relay-receipt.json), SHA-256 `bc22d7eec58ae1a1c430e9892a431e8cbc713aaaf1e566b993a2e9eb1b51acea`. The six exact isolated source files and their hashes are indexed in the [source snapshot README](effect-permission-annotated-relay-20261030-r21-rust-snapshot/README.json), SHA-256 `e62208f2fca06a0179a3910bc2e32f68e7950eb2e70fecfb8f7195aa6c1720f7`. The [Rust handoff](../inbox/effect-permission-annotated-relay-r21-rust.md) is `0ed9b077c0c47f46e1b71f694f7730047501d903c7a332a89a489142c95627b7`.

The compile errors were local to the probe: `CandidateGraphExport` has no `value` field, and `unresolved` is a method. A formatting correction was made after the one invocation; the final `lib.rs` is uncompiled. No Cargo retry occurred. The receipt records one CPU, sampled process-tree peak RSS of 53,575,680 bytes and available RAM of 28,663,705,600 bytes before launch. **40.492 seconds is measured Cargo time only; total Rust lane active time is unmeasured.** Do not calculate an active-time refund from the Cargo duration.

The observed evidence edge stops at test compilation: no source occurrence, runtime invocation, owner, permission/contribution event, Catch selection, result `1`, or residual consumer was observed. The earlier candidate graph inventory cannot fill this gap.

The independent referee identified two **major successor-use blockers** in the frozen isolated `lib.rs`:

1. At lines 35879, 35888 and 35917–35920, owner selection uses a substring of debug-formatted names, and every event receives a caller-supplied invocation label that assertions compare to the same supplied constant. This cannot establish exact owner or reject a sibling invocation. The explicit “probe grouping only” disclosure keeps this from becoming a false checkpoint claim.
2. At lines 35887 and 35903–35920, export failures are skipped and `CandidateGraphSolved` makes the event list nonempty even when permission and contribution records are empty. Assertions can pass without the required evidence, and they do not validate event order, path or causal linkage.

Do not reuse this instrumentation as source/native correspondence. A future observer must select the source owner structurally, use identities minted at their owning runtime transitions, reject export/selection failures, and require the exact permission/contribution and event order.

## Lean candidate

The frozen [candidate](../../../notes/theory/lean/YulangClosure/FormalPermissionAnnotatedRelay.lean), SHA-256 `0ef1272595c766206d8d9c7232f8799937706dbf292b94483621ceabe2159c2e`, declares eight candidate theorem roots. **None reached elaboration. No theorem type or axiom report was produced.** The candidate's deliberately partial decoder returns `none`; its negative inventory theorem is not native impossibility or compiler correspondence.

Both allowed audits are spent. Audit 1 failed at `lake --version` with exit `-6` and `failed to create thread` under the added 1 GiB virtual-address cap; elapsed time was 1.598 seconds. Audit 2 verified Lean 4.35.0 / Lake 5.0.0, then failed in unchanged, unleased `FormalPermissionSourceTransport.lean` before loading the new module (`unknown tactic by_contra`, an unsolved `changed_walk_hits_copy` goal, and an unsolved successor case for `copy_reaches_parent`). It took 11.428 seconds; sampled process-tree peak was 934,830,080 bytes. The two measured audit durations total 13.025 seconds. No dependency edit or further audit occurred.

The complete audit logs and hashes are in the leased [Lean scratch artifact index](../../../isolated/ep-annotated-relay-r21/lean-scratch/artifacts.json), SHA-256 `410e440a5fa2f7369905ff8176f2f8f68c792aa4d8820be6d2cb3240799655ed`; the [proof handoff](../inbox/effect-permission-annotated-relay-r21-proof.md) is `f8c79f011e673cd2dafcaa7c94ef8198c6e2efb4b2af77764897d01ce8030d46`.

## Independent review and adjudication

Fresh `compiler_referee` review **ACCEPTS preservation as `CLOSED_INCOMPLETE` only**. It authenticated the contract, manifest, frozen artifacts, raw evidence and isolated source snapshot. It confirmed Cargo failed before the test body, the post-attempt correction is uncompiled, and the Lean audits did not reach any new root. Its major findings above block any later use of the instrumentation as identity or permission-flow evidence. It also found that the Rust handoff reports Cargo elapsed time as active time; this outcome corrects that accounting to measured Cargo time with total lane time UNKNOWN. Review grants no theorem, source/native bridge, parent closure or production authority.

## Parent gates and successor

The approved callback annotation and companion computation remain separate source occurrences. The concrete annotation → contribution → same invocation's Catch → selection/result chain, and the companion's surviving `write` → outer `receive` chain, remain OPEN. Original A/B quantifiers, effect hygiene, soundness, principality, termination, source/native correspondence and production remain OPEN. R21 changes no compiler semantics, fixtures or expected output.

At the sprint-end boundary, the selector proposes R22 to trace the existing callback-result constructor through its actual request consumer and local Catch, using runtime-owned invocation and event identities. Its rationale is baseline-specific: the R21 isolated baseline already contains `CallbackResultSchema`, `callback_entry`, `callback_use`, `callback_execution`, `callback_grant`, and installs the callback execution view at `OperationResultConsumer`. This is a proposal for observation and proof of existing code, not semantic adoption or cutover. R21's Rust compile/identity blockers and Lean dependency build failure remain recorded as unresolved prerequisites where relevant.

All three R21 writers stopped; no process or descendant remains. After cessation and review, the primary accepted a frozen handoff of the 12 exact R21 path leases; no path was released. The [state snapshot](effect-permission-annotated-relay-20261030-r21-state-archive.json) preserves the worker record before handoff. The primary's [Git checkpoint receipt](effect-permission-annotated-relay-20261030-r21-git-checkpoint.md) records the commit and remote verification after push.
