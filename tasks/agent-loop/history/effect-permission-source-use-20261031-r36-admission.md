# R36 admission — source-owned callback use and permission-row selection

Status: **ADMITTED**. Sprint `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`, contract revision 1.

- Baseline: `yulang3` at `1388bdc476e5dc0c0bb96532715c7280aa95b10e`.
- Contract: `tasks/agent-loop/sprints/effect-permission-source-use-20261031-r36.md` SHA-256 `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0`.
- Input manifest: `tasks/agent-loop/sprints/effect-permission-source-use-20261031-r36-inputs-r1.json` SHA-256 `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4`.
- The manifest pins 15 direct authority, source, syntax and R35 dependency files by byte hash.
- Resource envelope: 6,000 seconds (Rust 1,600; Lean 1,600; independent review 1,200; Luna 1,600 including 500 closeout; Astra 0). No carryover.
- Existing checkout only. No worktree, clone, environment, copy, Cargo/Lake build, tests, target, cache, extraction or scratch.
- `machine.rs` and `receiving.rs` remain excluded from reads and writes. No `Instruction::Apply` shape change.
- Preserve all 32 pending records and every UNKNOWN/quarantined writer path. Existing capacity release is idempotently retained; no additional capacity slots are released.

## Live roster reconciliation

At admission, `/root` was the only running coordinator in the live roster. The R35 Rust, proof, review and selector agents were terminal. The current-state R17 worker row claimed WAITING, but its identity was absent from the synchronized live roster. It is therefore recorded UNKNOWN and its exact inbox path is QUARANTINED; no writer cessation or path release is inferred. Existing UNKNOWN workers and all quarantined paths remain exact. The three STOPPED R35 lane rows and old FROZEN scheduling leases were archived; R35/R34 source and proof bytes remain hash-pinned in the R36 manifest and outcomes. No active RUNNING/WAITING child was available for notification.

## Granted packets

Rust implementer and Lean prover may begin only on their disjoint exact output leases in the contract. Independent review is reserved but cannot start until both outputs and direct dependencies are frozen. Luna owns current state, handoffs' review slot, integration and Git. This admission authenticates no semantic, runtime, whole-language, A/B or production claim.
