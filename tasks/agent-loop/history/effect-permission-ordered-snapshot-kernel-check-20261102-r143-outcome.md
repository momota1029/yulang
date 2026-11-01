# R143 outcome — ordered permission snapshot kernel check

Status: **KERNEL_CHECKED_RESEARCH_ONLY**. Parent `YulangClosure.SourceProblem.InferenceSoundness`, effect hygiene H, A/B, source/native correspondence and production remain OPEN.

R143 checked the repair copy `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR143.lean` against frozen R140 source. R140's original candidate failed elaboration and remains unchanged and unchecked. The repair preserved all 25 theorem statements and corrected only recursive-call arguments, one reducible proof, and a reserved binder name.

The pinned Lean 4.35.0 native run exited 0. All 25 theorem types and complete transitive axiom lists were retained and independently reviewed. Dependencies are only `propext`, `Classical.choice`, and `Quot.sound`; no target depends on `sorryAx` or an unapproved axiom. The reviewer reproduced all six retained stdout/stderr hashes and accepted the input identities, complete failure/success streams and resource receipt. Two invocations used 12.636466617 seconds aggregate native wall time; peak sampled RSS was 784,080,896 bytes. The RSS monitor is a sampling guard, not a hard aggregate cap.

Independent review: `tasks/agent-loop/history/effect-permission-ordered-snapshot-check-20261102-r143-review.md`, SHA-256 `0bfc75c6e083bea3e37e1af1a25c5933827c6fcf632ff2103ce1c3556688fb3b` — PASS, no blocking or major findings.

The checked results establish only local ordered-projection facts for the formal table. The first remaining premise is an authenticated Rust-to-Lean identity/table map, registered-key coverage, and equality to the same successful native invocation's actual suffix and root vectors. No source/native bridge, shared source witness, hygiene theorem, A/B result, semantic adoption or production authority follows. The next discriminating step is the source/native table bridge; owner: Luna.

Exact artifacts: R143 contract and admission, repair module, frozen proof handoff, review receipt, and this outcome. R140 source SHA-256 remains `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985`; R143 repair SHA-256 is `88efc42949e7d912189313b670bc3537879d4b2eb6998b195ba606e44de536e9`; proof handoff SHA-256 is `b9d576691256b2ec124cbcceaf01ffad41978e68b78eda69e761ac66132dc6fd`.

No Rust source, Cargo build/test, Lake build, cache, environment, worktree or scratch output was changed or created by R143. Existing dirty/quarantined Rust paths remain untouched. On the separate user request to analyze Rust, a read-only audit of clean `candidate_scope.rs` found no justified production bug; its concrete remaining gap is direct Rust regression coverage of the already-proved composition/remapping law. That audit is separate and does not alter this outcome.
