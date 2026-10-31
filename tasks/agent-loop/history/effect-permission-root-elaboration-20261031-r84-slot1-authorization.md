# R84 Lean slot 1 authorization — normalized dependency prefix

Primary authorization for invocation **1 of at most 4**, after independent
review PASS and exact-input reconstruction. This authorizes only the frozen
normalized dependency prefix; it accepts no theorem and does not authorize
slot 2, slot 3, or slot 4.

## Reviewed artifacts

- R84 contract: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84.md`, SHA-256 `28890c4ee0953c4a4e01a1f5a95b04b22eaa45616d87a4f3b5a9ad2a8d6604f0`.
- Input manifest: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84-inputs.json`, SHA-256 `05f1743b43737117a092fbf13ae8717793d559a24d103b96a857d6e15176a8d2`.
- Candidate: `notes/theory/lean/YulangClosure/ConstructedPhysicalRootR84.lean`, 22,748 bytes, SHA-256 `1681d78a8ec4b103dac7fb808bc4cdd02e0a46cba196ad5a64db6c10601f1839`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-root-elaboration-r84-proof.md`, 331,759 bytes, SHA-256 `c9ba9b410094cea83309b2df18e64f42fe4308ef7b158c708fb737d41ead618a`.
- Independent review receipt: `tasks/agent-loop/inbox/effect-permission-root-elaboration-r84-review.md`, SHA-256 `ac3373ee1cc4cf7b4f619ee16425d90fa938914a675a340fceebcefd1ae39825`; reviewer `/root/r83_review`, verdict PASS for source, normalization, statements, and assembly recipes. The reviewer did not execute Lean.

## Exact invocation

- Slot 1 recipe: reconstructed normalized prefix body + the frozen `prefix_queries` string from the proof handoff JSON. No candidate body is included.
- Exact stdin: 93,368 bytes, SHA-256 `e031132b1a5a42f22c5faba355a1af3d8639d0d577de9051e81f403bf465ebb3`.
- Pinned executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`.
- Working directory: `notes/theory/lean`.
- Environment: `LEAN_NUM_THREADS=1`.
- Hard timeout: 120 seconds. Existing `-j1` and `-M1024` limits remain in force.
- Supply stdin from memory; capture complete stdout and stderr in memory. After execution, retain exact streams, byte counts, hashes, exit, elapsed time, timeout status, and measured peak RSS if available in the assigned proof handoff and primary result record.
- No file input/output for the Lean process; no Lake, build, test, formatter, cache, `.olean`, target, scratch, environment, or worktree creation.

The exact stdin was independently reconstructed from pinned source slices and
normalization records and matched the reviewed byte count and hash. The
reviewer independently reconstructed the same slot-1 recipe and hash. All
source claims, definitions, constructors, and candidate theorem statements
remain fixed. A failure consumes slot 1 and closes this stage; only an actual
diagnostic-directed, separately reviewed and separately authorized slot 2 may
follow. A pass is only prefix/type/axiom evidence; slot 3 still needs its own
candidate review and authorization.
