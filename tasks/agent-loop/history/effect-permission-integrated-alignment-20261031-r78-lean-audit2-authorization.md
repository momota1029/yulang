# R78 Lean audit 2 authorization

Authorization: Luna primary, under the standing Rust/Lean goal authority in root AGENTS.md.
Sprint: EFFECT-PERMISSION-INTEGRATED-ALIGNMENT/20261031-R78, contract revision 1.
Audit 1 failed (receipt preserved in proof handoff); this is audit 2 and the final permitted invocation. No retry or third run.

- Frozen candidate commit: `37e871595`.
- Module SHA-256: `bfe304c33e6018910739d58d37c2122a4a475fac57e00091e1a700a965510029`.
- Independently reconstructed exact stdin: 57,790 bytes, SHA-256 `0c61742191ea55c18c68ef6ef4e30e1c34cf48bb24275ca310481629602ed0c7`; all 14 source/slice hashes matched.
- Nine exact theorem type and transitive-axiom queries.
- Pinned Lean executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; args `-j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; timeout 120 seconds.
- No Lake, project build, tests, formatter, cache, target, scratch, environment, or worktree.

Audit1 diagnostics repaired: reduce the indexed Apply/do expression explicitly and fully qualify the R77 finite fixture use. A static scan found no proof holes, project axioms, or bypasses. The authorization commit must be pushed before invocation. Capture stdout/stderr byte-exactly in the proof handoff with hashes, exit, timeout, elapsed time, then stop.
