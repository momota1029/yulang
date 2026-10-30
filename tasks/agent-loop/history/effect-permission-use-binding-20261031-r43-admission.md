# R43 admission receipt

Sprint `EFFECT-PERMISSION-USE-BINDING/20261031-R43` admitted by Luna under the standing ongoing Yulang Rust/Lean goal and the 2026-10-16 sprint decision. This receipt binds exact scope, dependencies, budget, same-checkout constraint, and dispatched lanes.

- Contract: `tasks/agent-loop/sprints/effect-permission-use-binding-20261031-r43.md`, SHA-256 `0e4e11482fe905f10229f08e015e3088f1da9bba3db04bd462241b9ecf920aed`.
- Prior state: `tasks/agent-loop/current.json`, SHA-256 `1e4a823ef91d09cc993400f3e3911831a3344db3eb10d0ee19ae579e3505f543`; 32 pending items preserved, 16,384-byte state limit validated after the R42 compaction.
- Branch/head: `yulang3` / `b41e2433644ef7359af6ab68754804dbf1eb768d`, equal to `origin/yulang3` at admission.
- R42 source checkpoint: `2182b07fbc7aa92c725634a78e0b2db3252e49e5`; R42 reviewed outcome: `tasks/agent-loop/history/effect-permission-native-incidence-20261031-r42-outcome.md` SHA-256 `784b45b73da9dbf0aff4e23d9b190b4f263070d9efeb56e037846eb453bf9a9f`.
- Source pins: `candidate_effect.rs` `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db`; `candidate_scheme.rs` `c14f6cecb38fbf54b15e808f7385d9782dec1a784a12eac1315e1c32becd8429`; R42 Lean `61bb9ced2a80a75c2e952c3f5198a36ad7b9ae10f06df1a7996d38851107d4d6`; R42 review `2bd380bc54c00674ca693d2058d11bddb471862d625215771aa444246aeec146`.
- Remaining model pins: R39 `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; R41 `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e`.
- Read-only source pins: `term.rs` `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`; `lib.rs` `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce`; `candidate_context.rs` `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38`.
- Exact writers: Rust `/root/r43_rust` owns `candidate_effect.rs`, `candidate_scheme.rs`, and the Rust handoff; Lean `/root/r43_proof` owns the R43 module and proof handoff. Fresh reviewer `/root/r41_independent_review` will own the review packet after both authors STOP. Luna owns Git/state integration.
- Reservation: 4,200 seconds total (Rust 1,200; Lean 1,200; review 900; primary 900 including up to 500 closeout; Astra 0). No extra capacity override.
- Resource fence: existing checkout only; one `git worktree` listed at admission; no environment, build, Cargo, tests, Lake, cache, target, or scratch. R43 begins with the explicit no-Lake rule; R42's disclosed version invocations are retained in history.

At admission live-roster synchronization showed no active R42 producers or reviewer; selector and prior workers were completed. Two R43 producer launches and exact leases are recorded in current state after live launch confirmation. Unknown/quarantined paths and all 32 pending items remain unchanged.

## Exact source-owner loci at admission

- `crates/yu-solver/src/candidate_effect.rs:303` owns the retained permission vector; `:434–445` defines `FormalEntryPermission`; `:1845–1900` authenticates registration/owner/scope/formal/source Lambda and stores the concrete permission payload.
- `crates/yu-solver/src/candidate_scheme.rs:423–449` owns `FreshRoute` and R42 incidence certificate identity; `:453–494` reconstructs its exact route-local Function/child and actual TermView argument-effect field.
- `crates/yu-solver/src/term.rs:831,856` checks arena-branded term lookup and exposes the actual term view; pinned source hash recorded in the contract.

No semantic rule, public API, consumer, propagation, provider-arrival, Catch/residual subtraction, or production authority is admitted.
