# R78 Lean audit 1 authorization

Authorization: Luna primary, under the standing Rust/Lean goal authority in root AGENTS.md.
Sprint: EFFECT-PERMISSION-INTEGRATED-ALIGNMENT/20261031-R78, contract revision 1.
Frozen candidate commit: `59e826d06` (Lean module and proof handoff); Rust source candidate commit `86148330b` is separately labeled unresolved and not production-approved.

- Module: `notes/theory/lean/YulangClosure/IntegratedSourceAlignmentR78.lean`, 10,345 bytes, SHA-256 `5ac87fdc86601cf4e8507ec168cc37c5e7091d50bbeb4bab5ee1cdbce35d2faf`.
- Independently reconstructed audit stdin: 57,409 bytes, SHA-256 `fe4816df474cf33882c161966d54c24303e34f75e5fb7a4e30212b0d9dffcfb3`; all 14 source-slice hashes matched.
- Declarations: 9 exact `#check` plus transitive `#print axioms` queries.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Invocation: `lean -j1 -M1024 --stdin`; cwd `/home/momota1029/rust/yulang/notes/theory/lean`; `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- This is audit 1 of at most 2. No retry and no third audit. No Lake, project build, tests, cache, target, scratch, new environment, or worktree.

The exact input was assembled in memory and its full source/slice hashes and byte count matched before this authorization. This authorization commit must be pushed before invocation. Full stdout and stderr will be retained byte-exactly in the leased proof handoff with hashes, exit status and elapsed time.
