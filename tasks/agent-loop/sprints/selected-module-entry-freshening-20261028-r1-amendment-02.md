# Amendment 02 — canonical isolated-worktree path

Parent: `SELECTED-MODULE-ENTRY-AND-FRESHENING/r1`.
Amends amendment 01 (`tasks/agent-loop/sprints/selected-module-entry-freshening-20261028-r1-amendment-01.md`, SHA-256 `0e4c6e266723fc7795f9481fbea4f8466f1237e0a7eefefe8b466adec71310be`).

Before the Rust writer was launched, Luna moved the detached worktree at base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` from `/tmp/yulang-selected-module-freshening-repair-r1` to the repository-relative path `isolated/selected-module-entry-freshening-repair-r1`. This was done so every path lease could be represented as a canonical repository-relative exact path in `current.json`. The move completed before the worker's first read or edit. The applied rejected overlay and subsequent repaired bytes were preserved exactly; only the worktree location changed. The shared root source copies remain unmodified by this worker and quarantined runtime owners remain untouched.

For amendment 01, replace the stale `/tmp` worktree locator with:

`/home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1`

The writer's exact leased paths are the three Rust files and `tasks/agent-loop/inbox/selected-module-entry-freshening-repair.md` under that worktree. The frozen repair handoff's `/tmp` reference is superseded by this location correction; its contents and source hashes remain as submitted. The final source hashes are `candidate_effect.rs` `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`, `candidate_scheme.rs` `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`, and `shadow_apply.rs` `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a9a78cf72ff`. No source semantics, output, lease membership, budget, role, theorem, or verification authority changes.

The proof target and handoff remain on amendment 01; they did not use the Rust worktree. All previous findings, proof boundary, budget accounting and gates remain unchanged. This amendment grants no Rust baseline admission and no Cargo/build/test permission. Fresh independent review of the frozen Rust delta remains next. Parent, source/native, H_u, A/B, effect-hygiene and production gates remain OPEN or AUTHORITY_BLOCKED exactly as before.
