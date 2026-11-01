# R143 — kernel-check the frozen ordered-permission snapshot model

Status: admitted by Luna under the ongoing Yulang Rust/Lean soundness goal.
Parent: `YulangClosure.SourceProblem.InferenceSoundness` and effect-hygiene H remain OPEN.
Semantic candidate: R140's explicit ordered formal-permission projection only.

## Fixed outcome and exact inputs

Verify the exact frozen R140 Lean module with native Lean 4.35.0 and record all
25 theorem types and complete transitive axiom audits printed by that file.
The source file is immutable for this packet:

- `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean`,
  23,626 bytes, SHA-256
  `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985`.
- R140 proof handoff:
  `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-proof.md`,
  SHA-256
  `a0a8e21563435014b8da3c48bcae871ae87794e4f0ec68d842e243825364de05`.
- R140 independent review:
  `tasks/agent-loop/history/effect-permission-ordered-snapshot-20261102-r140-review.md`,
  SHA-256
  `d3a66d051dacb2cca835325adaf081865e08987fe253aed56d89f30f2c531624`.
- Import surface is `Std` only. There is no Lake build and no project import
  dependency for this direct kernel check.
- Toolchain pin: `leanprover/lean4:v4.35.0`.
- Resolved native Lean executable:
  `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`,
  SHA-256
  `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Prior successful R136 native method and limits are recorded in
  `tasks/agent-loop/inbox/formal-permission-constructor-r136-proof.md` and
  `tasks/agent-loop/history/formal-permission-constructor-r136-review.md`.

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` with
its original all-supported-source quantifiers and correlated evidence. The
ordered projection does not supply the authenticated Rust-to-Lean identity
map or equality with a successful native inventory. Do not claim parent
soundness, effect hygiene H, A/B, source/native equality or production.

## Verification protocol and resource boundary

Use the exact native executable above; before each attempt, recheck its SHA-256
and require `LEAN_NUM_THREADS=1`. Feed the frozen input bytes through stdin to
the native executable with `--stdin -j1 -M1024` from `notes/theory/lean`.
Capture exact argv, cwd, input bytes/hash, complete stdout and stderr, exit,
versions, wall/CPU timing, and sampled process-group RSS.

Run a process-group monitor at 0.1-second intervals. At an observed RSS of
1,073,741,824 bytes or at timeout, terminate the whole process group (TERM,
bounded grace, then KILL) and retain the monitor record. This is a **sampling
guard, not a hard aggregate memory cap**; `-M1024` bounds the individual Lean
process only. Pin the Lean child to one currently allowed CPU. Do not create a
Lake cache, environment, worktree, scratch source, or log file; retain raw
streams and resource samples in memory until they are written into the exact
leased handoff.

At most three Lean proof invocations total, each at most 120 seconds and at
most 240 seconds aggregate native wall time. A later invocation is allowed
only after a genuine Lean elaboration diagnostic and a new R143 candidate file
with an exact input hash. Keep R140 untouched; any repair goes only to
`notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR143.lean`.
If thread creation fails before elaboration, the same resource/thread failure
recurs, the pinned executable hash changes, the process cannot be stopped,
or any limit is reached, freeze evidence and stop without retry.

Before invoking Lean, check the complete input hash and preflight the native
binary identity/version against this contract. No Lake, Cargo, Rust build,
Rust tests, Astra, package, dependency, environment, or general resource probe
is authorized.

## Exact outputs and assignments

- Registered `lean_prover`, 600 seconds maximum. Exact handoff:
  `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-check-r143-proof.md`.
  The optional R143 Lean file above is writable only if an actual Lean
  elaboration diagnostic requires a source repair. Preserve all 25 theorem
  declarations, their types/quantifiers/meaning, and the original R140 file.
- Fresh independent Lean reviewer, 240 seconds maximum, distinct from the
  author. Exact receipt:
  `tasks/agent-loop/history/effect-permission-ordered-snapshot-check-20261102-r143-review.md`.
- Luna outcome/state/Git: 300 seconds maximum.
- Dispatcher and bounded contingency: 360 seconds; no transfer to proof calls.
- Total envelope: 1,500 seconds.

Accept as **KERNEL_CHECKED_RESEARCH_ONLY** only if exit is zero, all 25 target
declarations print their exact theorem types and complete `#print axioms`
results, no target is missing, no `sorryAx` or unapproved axiom occurs, and
fresh review accepts the retained logs, input hash and declaration coverage.
Report actual standard axioms rather than calling the proof axiom-free. On
failure, record the concrete first error and mark the module unchecked or
rejected; do not turn a constructed declaration into a checked theorem.

All unrelated Rust dirty/untracked paths remain untouched. The reviewed R142
Rust candidate remains patch-only and does not authorize source integration.
