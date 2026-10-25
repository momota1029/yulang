# LEAN-CALL-STEP-TYPING-20261025/r2 outcome

Status: **ACCEPTED / CLEAN**, Luna integration. Exact proposition preserved from r1; baseline for this repair sprint: `862c8777684587f6ca2b20d22859f954804a2c50`. Frozen r2 contract SHA-256: `7c7d53498cf0ad43e61d5afa20b525e47adbf41caa205b14f77afa4323d024d0`.

## Result

`YulangClosure.Control.call_state_typed_step_preservation` now has a checked proof for every one of the 28 constructors in the current pinned `CallControlStep`. It preserves exactly `CallStateTyped sig t result`, `t.resultType = s.resultType`, and `t.literalSuffix = s.literalSuffix` from the frozen contract.

The r1 attempt remains immutable and `FAILED_VERIFICATION / UNACCEPTED`; its unknown dependent pattern identifiers were fixed in a new r2 module. No semantics, premise, dependency, constructor, or quantifier changed. The author used 113 seconds of the 600-second grant and STOPPED before verification.

## Verification and review

Luna revalidated the exact source and accepted output pins before compilation. The two serialized Lean invocations both succeeded, in order, with no timeout or stderr:

1. `CallStepTypingRepair.lean` compiled in 0.649264530s. Candidate SHA-256 `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586`; `.olean` SHA-256 `d3ce599691c41652fb5663b843862cb250664a06279ce777721069d980456d98`; `.ilean` SHA-256 `8d56de64b33870fac7ed6b9a9ff7fc248d612ff12b638e498663625eb8920ed4`.
2. Exact signature and axiom query succeeded in 0.304187163s. Printed signature matches the frozen theorem and axiom output is `[propext]`, within the contract cap.

Complete argv, UTC start/end, timings, exit statuses, source and dependency hashes, outputs and stdout/stderr are in `tasks/agent-loop/inbox/20261025-call-step-typing-r2-verification.jsonl`, SHA-256 `975f0c540e2e87219afd7fc0dd7477085bc81539f5f7da0de174764eeec5e52a`. Query source SHA-256 is `cc18788d3a266c60379842b24b45a305e60fc10d6ee6bfbde0c9906aa5f0f1e2`.

Fresh independent `compiler_referee` review is **CLEAN**, with no blocking, major, or minor findings. The full review is `tasks/agent-loop/inbox/20261025-call-step-typing-r2-review.md`, SHA-256 `f0e461a622e5309242ee151dac8f93a18183ed01262b77b836e066902f53981f`. It checked all 28 cases, exact statement, consumer/view fields, return substitution, response-binder lifting, complete receipts, artifact hashes, and the axiom result. Reviewer model/effort and wall time were not available; no Lean, tests, Git, or writes were performed by the reviewer.

The static sprint checker passed after current state was brought below its serialized 16 KiB cap. This is tooling evidence only. No tests or Rust checks were requested or run.

## Claim boundary

This closes only conditional one-step preservation for the existing formal transition and typing relations. It establishes no progress or successor coverage; `.force (.view (.delay body) occurrence)` still has no matching transition. World, effect, metadata, receipt, source/native, original Call A/B, inference A/B, and production claims remain OPEN. r9 remains `SOURCE_INPUT_BLOCKED / UNACCEPTED`. The earlier accepted syntax theorem remains independently CLEAN.

## Checkpoint commits

The r1 failure and r2 repair were pushed as a sequence of ordinary commits, including `862c87776` (r1 outcome), `3933b3420` (r2 frozen contract), `71cb5bd69` (r2 frozen candidate), `c9a397725` (r2 compile), `1038ffbf9` (r2 signature/axiom query), and `59703b9d2` (review start). Luna's final state/outcome integration commit follows this receipt.

## Next action

Consult the dispatcher for the next exact proposition and bounded sprint. Keep the open adequacy, A/B, source/native, effect/world, inference, and production gates unchanged.
