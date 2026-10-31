# R84 Lean slot 3 authorization — full Root candidate

Primary authorization for invocation **3 of the four-slot ceiling**. Invocation
1 ran the exact normalized prefix and exited 0; it consumed one invocation.
Slot 2 is unused. This separately authorizes the frozen full candidate input.
It does not accept any theorem before its own output is audited.

## Gate and reviewed artifacts

- R84 contract: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84.md`, SHA-256 `28890c4ee0953c4a4e01a1f5a95b04b22eaa45616d87a4f3b5a9ad2a8d6604f0`.
- Input manifest: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84-inputs.json`, SHA-256 `ecefcea9636419ec2407950301061c969501e6248fca4e7bb5737edc07912871`.
- Independent review receipt: `tasks/agent-loop/inbox/effect-permission-root-elaboration-r84-review.md`, SHA-256 `ac3373ee1cc4cf7b4f619ee16425d90fa938914a675a340fceebcefd1ae39825`; verdict PASS for the source, all thirteen unchanged theorem statements, normalization, and exact slot-3 recipe.
- Slot-1 result: `tasks/agent-loop/history/effect-permission-root-elaboration-20261031-r84-slot1-result.md`, SHA-256 `4cb8d67812a751b0254b42f613573d6df8b4f605ca5923128437c23f7161722c`; exact input matched and Lean exited 0 in 9.034 seconds. Its stdout archive was incomplete due to response truncation; no theorem was accepted from slot 1. Slot 3 runs the reviewed complete candidate input and must retain its full output in the primary result record.
- Frozen candidate: `notes/theory/lean/YulangClosure/ConstructedPhysicalRootR84.lean`, 22,748 bytes, SHA-256 `1681d78a8ec4b103dac7fb808bc4cdd02e0a46cba196ad5a64db6c10601f1839`.

## Exact invocation

- Recipe: accepted slot-1 normalized prefix body + import-stripped frozen R84 candidate + one newline + frozen `full_queries` string from the proof handoff JSON.
- Exact stdin: 103,791 bytes, SHA-256 `5c35dd49b71508fea4755abf680327932099249de1d1f4f5f250ca2d949651f2`.
- Pinned executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`.
- Working directory: `notes/theory/lean`.
- Environment: `LEAN_NUM_THREADS=1`.
- Hard timeout: 120 seconds; `-j1` and `-M1024` unchanged.
- Reconstruct and hash-check the exact stdin in memory, supply it directly to Lean, and capture complete stdout/stderr in memory. Persist the complete raw streams as the primary result after process exit; do not print or encode the full streams into the tool response.
- No Lake, build, tests, formatter, cache, `.olean`, target, scratch file, environment, or worktree creation.

The exact full input was reconstructed from the pinned prefix body, candidate,
and query string; its bytes and hash match both the manifest and independent
review. The reviewer checked the candidate and all thirteen unchanged Root
statements. A successful full audit still requires complete printed theorem
types and transitive axiom reports, exit 0, and no forbidden axioms or
error-recovered declarations. Any failure consumes slot 3; only one
diagnostic-directed, independently reviewed and separately authorized slot 4
may follow.
