# EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1 — integrated final review

Verdict: **CLOSED_INCOMPLETE**. Independent reviewer: `/root/canonical_export_final_review` (`compiler_referee`), read-only; applied `yulang-lean-proofs`. Luna transcribed this receipt after the reviewer completed. No builds, tests, Lean execution, edits, Git operations or delegation by reviewer.

## Blocking findings

- **BLOCKING — no authentic unequal transport.** Rust run 1 failed at `candidate_effect.rs:3143` with `[(19,19),(21,21)]`; run 2 failed with `[(21,21),(23,23)]`. On both observations `r=q`, so q→r is not an effective mutation. The contract's required successful ordinary-source evidence is absent. A genuine native `r≠q` must be derived, retained against the independently materialized captured row, and shown to reject a changed q without weakening assertions or synthesizing a representative.
- **MAJOR — delegated site uses annotation position, not nested row position.** `candidate_effect.rs:2428` records `context.position()`; `SignatureContext::position` at `:309` returns the annotation position. `FormalEffectSite` at `:1657` records `effects.position`. The strict join at `:3224` therefore fails at `:3227` (0 vs 1). Delegated ports at `:2486` and ordering groups at `:235` also use the broader position, so nested rows can be conflated. Preserve nested row position plus enclosing occurrence/path, both allocations, and the strict join.
- **MINOR — frozen Rust handoff has stale pre-run statements** saying run 2 is pending/was not launched and successful compilation/results are missing. Preserve that handoff; this outcome supersedes the stale claims: both runs compiled and executed, failed, and both invocation slots are spent.

New capture-row and concrete joins are at their owning observation points. `candidate_scheme.rs:2128–2135` records q from the actual materialized graph node's `RowKey::Effect`; `CanonicalIntern` retains incoming r at `:1717–1755`. The owner test reached the capture, witness, r, polarity, node, actual returned-port, and per-origin `Origin.concrete` checks (`candidate_effect.rs:3117`) before failing the inequality assertion. The symbolic test failed before later tail/port assertions. Neither Rust test passed.

## Required falsifiers

| Mutation | Review result |
|---|---|
| Change q against fixed captured row | Rust `:3131` structurally rejects a different q; Lean `changed_q_rejected` proves this for a fixed supplied snapshot and explicit inequality. Observed q→r remains unexercised because both native cases have r=q. |
| Set both exports to one wrong concrete list while origins stay fixed | Rust `:3117` compares each export to its own origin; Lean `same_wrong_set_both_rejected` rejects a common list differing from both fixed origins. |
| Wrong owner wrapper | Exact wrapped-owner filters/counts reject it in Rust. The Lean checked fixture's ownership mutation is mathematical evidence, not a native Rust observation. |
| Omit second origin | Rust requires two origins/exports; Lean fixture rejects a shortened observation list. |
| Swap sibling ports | Per-origin path/source-row/occurrence plus `:3138` node identity rejects a swap against fixed intern evidence. Later explicit assertions `:3146–3147` were not reached. Lean fixture rejection is mathematical evidence only. |

No mutation tests ran. The Lean module uses only the diagnostic row-pair lists and leaves Context, state, code, metadata, paths, capture/root, and node IDs explicit. `run1_decode` and `run2_decode` require successful `decodeValue` and matching retained entries; those premises remain open. No native extraction, snapshot authenticity, source-wide realization, or nontrivial transport is established. Consistent changes to supplied inputs are outside its fixed-input mutation results.

All ten theorem type/transitive-axiom blocks were inspected and match the raw log, `audit-10.txt`, and final proof handoff:

| Declaration suffix | Complete axioms |
|---|---|
| `recorded_rows_are_identity`, `run1_expected`, `run2_expected`, `run1_snapshot_rows`, `run2_snapshot_rows` | none |
| `run1_decode`, `run2_decode` | `propext`, `Quot.sound` |
| `changed_q_rejected`, `wrong_concrete_rejected`, `same_wrong_set_both_rejected` | `propext` |

No proof holes, project axioms or checker bypasses were found in the six-module dependency cone.

## Frozen hashes and receipts

```text
contract                       70a69a66a9367114a70970d73825942bfebfc08a2143b7288f057b76088aaf4b
candidate_effect.rs            75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1
candidate_scheme.rs            31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707
Rust handoff                   ea9d9e74f383adefb120abcc619c8395404e20f41d0f1acc71764df0fba20d8e
Native Lean module             a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1
Proof handoff                  1bbbdbc3b45936ca842259203c577623c80b05619e88fb5e1cd37079ff222140
Rust-only review               61f6a21373c352533bfd772bb81711dc2968aa7012548d11f40f4dc3a97d7523
```

All 12 Rust raw receipt hashes match the frozen handoff; both feature-correct argv files match. Run-2 manifest matches final sources. Run-1 manifest authenticates its historical source hash, but the historical source bytes are not retained, so they were not reconstructed. All 32 Lean frozen-manifest entries were rehashed with zero mismatches. Lean receipt hashes: `check-1.log` `a88c3af182d567487250cfd6c085a693cabfce4fe7102637ec332d693d100869`; `check-1.time` `1e6cd4010b95f0a066f8c13ea920d822a98564e3b00bb0c43b8acc286d5a7c4e`; status `a204102458f5f13526075ed05042e2cadcaaea9a275ef1e6f2abbe29fa688749`; `audit-10.txt` `9801e52180adbf6336abb6338eb21665dc84948af4db3a9260b666139b07be64`; manifest `af131282b6ae99531b6b1396655ae0eb36b18df0f9ccb7b9e6f82dceba441644`.

| Invocation | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Rust 1 | 101 | 60.14 s | 1,664,404 KiB | 0 |
| Rust 2 | 101 | 6.40 s | 1,116,748 KiB | 0 |
| Lean sole check | 0 | 6.38 s | 968,532 KiB | 0 |

Combined Cargo wall is 66.54 s (<180 s). Lean is within 120 s/1 GiB. Outer Lean argv pins CPU0; wrapper fixes one Lean thread; project/audit use `-j1 -M1024`; pinned Lake/Lean is 4.35.0, and no default build ran. Rust raw time receipts show one Cargo job/timeouts; CPU affinity and preflight headroom are not independently captured there. Parent/native/production gates remain OPEN.

**STOPPED.** No reviewer processes remain.
