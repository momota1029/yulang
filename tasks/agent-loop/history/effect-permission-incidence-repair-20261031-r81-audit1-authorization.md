# R81 Lean audit 1 authorization

Sprint: `EFFECT-PERMISSION-INCIDENCE-REPAIR/20261031-R81`; sequence: `R81-CONSTRUCT-1`.

Primary Luna separately authorizes one exact-input Lean audit under the R81 contract. Reconstructed in memory from all 15 source segments and 12 theorem queries in `tasks/agent-loop/inbox/effect-permission-incidence-repair-r81-proof.md`; exact stdin is 107,431 bytes, SHA-256 `35a379150757ec307d17da62048d64de23ab6e9c014183e1ac5a79bd99daedd6`. Every pinned source hash, segment byte count/hash, and total input digest were reauthenticated before this authorization.

Invocation: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`; working directory `notes/theory/lean`; `LEAN_NUM_THREADS=1`; hard timeout 120 seconds. Executable SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. Input is piped directly from memory; stdout/stderr are captured in memory and appended with hashes to the proof handoff. No scratch files, build output, cache, target or environment.

This authorization permits only this exact stdin once. Audit count: 1 of at most 2; combined execution limit: 240 seconds. Any nonzero exit is a failed proof audit; no theorem is accepted from error recovery. The second audit requires a separate pushed authorization. This record authorizes no compiler, Lake, Cargo, tests, builds, or semantic change.
