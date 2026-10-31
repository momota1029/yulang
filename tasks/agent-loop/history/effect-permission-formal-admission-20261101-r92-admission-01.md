# R92 admission — source-owned logical admission and effect hygiene

Admitted by Luna at `2026-10-31T16:03:45Z` on branch `yulang3`, baseline `0bdac5f73ebb54d4049e8a8b8896330beda1c6f5`, with `origin/yulang3` at the same commit.

## Authority and outcome

This is a bounded continuation of the user's active Rust/Lean soundness goal. The sprint-start selector `/root/r85_boundary_dispatch` recommended R92 after R91 and was observed completed. Its fixed target is the actual `EventProof`/App `ViewLogic` admission and `decodeFrame` readout across formal registration → Shared delivery → both-mode Name use, using occurrence-indexed dependency/write analysis. The original source domain, theorem quantifiers, dependent telescope, Value/Computation modes, and shared witnesses remain unchanged.

R91 remains `CLOSED_BOUNDED_EXECUTION_BLOCKED`; its two failed calls remain consumed, its candidate remains unchecked, and its reviewed source finding identifies the missing source-owned logical-admission/readout law. R92 is not an R91 retry. R92 permits at most two new primary-owned in-memory Lean checks, each ≤120 seconds, only after an independent reviewer verifies the exact ordered input and Luna pushes its authorization. No Lean call is authorized merely by this admission.

## Exact contract and dependency record

- Contract: `tasks/agent-loop/sprints/effect-permission-formal-admission-20261101-r92.md`.
- Input manifest: `tasks/agent-loop/sprints/effect-permission-formal-admission-20261101-r92-inputs-r1.json`, SHA-256 `080e254e9eb19dd4df54bc28aca6bdf45478eb413e9f8d8b9df76dad04c04cc2`, 105 exact entries.
- The manifest carries all 93 R91 source pins (all 93 matched current bytes at admission), the frozen R91 candidate and outcome/review/call receipts, the R90 proof/source/review seam, and the already closed migration review/reconciliation record.
- Pinned toolchain: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; executable `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

## Runtime and leases

The live collaboration roster was synchronized at admission. The R92 dispatcher returned a terminal selection; the migration-gate reviewer returned a terminal audit; the prior R91 proof/source/review agents are terminal. Other historical identities absent from the live roster remain UNKNOWN in `current.json`; their paths remain quarantined. The previously authenticated 13-slot capacity release remains in force; no fresh override was needed or applied.

Exact R92 write paths:

- Luna: `tasks/agent-loop/current.json`, this admission, the R92 state-compaction record, exact Lean call authorization/receipt records, and the final outcome.
- Proof lane: `tasks/agent-loop/inbox/effect-permission-formal-admission-r92-proof.md` only.
- Source lane: `tasks/agent-loop/inbox/effect-permission-formal-admission-r92-source.md` only.
- Fresh independent review: `tasks/agent-loop/inbox/effect-permission-formal-admission-r92-review.md` only.

No new Lean source path is leased. All Rust/compiler paths are read-only. In particular, `candidate_effect.rs`, `candidate_scheme.rs`, `shadow_apply.rs`, the quarantined runtime files, and the quarantined module-environment handoff cannot be written or reclaimed. No environment, worktree, copy, build, cache, scratch output, Lake invocation or test is authorized. No unresolved pending item is removed from compact state.

## Gates and closeout

The proof lane audits the unchanged R91 candidate and proposes a deterministic module-context-preserving assembly; Luna owns any exact direct call. The source lane traces the original admission/readout owners and returns the first source law or exact missing premise. The independent reviewer checks both frozen handoffs and all actual call results. A module-context error or mathematical failure stops execution and is preserved as evidence; a conditional lemma, source trace or static result does not close the original parent.

Original A/B, complete Call construction, source/native correspondence, effect hygiene, principality, termination and production remain OPEN. R92 success is a checked, source-backed reduction of the exact admission/readout obstruction or an exact falsifier/missing-law result with owner and next in-scope step.
