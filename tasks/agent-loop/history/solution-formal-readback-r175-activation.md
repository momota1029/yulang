# R175 activation receipt

Sprint `SOLUTION-FORMAL-READBACK/20261102-R175`; branch `yulang3`, baseline
`59fce5ec0`. The unchanged goal is Yulang type/inferred-effect soundness
against original source typing rules; runtime/machine correctness is excluded.
R174 closed incomplete after independent PASS for the bounded
`BLOCKED_SOLUTION_CARRIER` result. Parent inference soundness remains OPEN.

## Admission and frozen boundary

R175 is a read-only admission preflight: determine whether the existing
original semantics and actual inference carrier determine a pre-invocation
`FormalAssignment` from the same successful solution. Value must read the
original `Descriptor` from prepared `native_root`; Computation must read the
complete `Interface` from `native_root` plus `entry_effect`, preserving the
prior telescope and source coordinate. No `solves`, carrier identity or
readback function may be assumed. Return the exact READY input set or
`BLOCKED_SEMANTIC_AUTHORITY`; do not claim parent closure.

Contract SHA-256: `a5f02d6cbe5383262943f17637315420d2f8747219bdd750f9448d50f45ebc40`. Every listed R173/R174, Rust API and Lean source hash
matched before admission. No additional path is authorized. `candidate_context.rs`
remains excluded unless a later exact packet pins it.

## Roster and leases

Live roster synchronized before admission: Luna active; all prior agents
completed/STOPPED. No active worker displaced. Existing UNKNOWN assignments,
quarantines, 16-slot capacity receipt and runtime-path quarantines remain
unchanged. R174 source writer had stopped and its reviewed handoff was committed/pushed; its exact completed output lease was relinquished. No quarantined/UNKNOWN path lease was released.

Read-only lanes: `/root/solution_formal_readback_r175_source` (`researcher`,
600s) audits API route/callers/result semantics and prepared formals;
`/root/solution_formal_readback_r175_proof` (`lean_prover`, 900s) audits
concrete original meanings and possible same-solution registration. Both send
findings to Luna and hold no write lease. A fresh independent reviewer gets
300s after the integrated handoff freezes.

Luna's sole output lease is
`tasks/agent-loop/inbox/solution-formal-readback-r175.md`. No builds, tests,
Cargo, runtime inspection, environment/cache/target/scratch, source edits,
worker descendants or additional output paths are admitted. Worker exact-
contract acknowledgements are pending.

## Contract revision 2

The source lane identified `crates/yu-solver/src/candidate_call.rs` as the
first additional owner needed for the public candidate formal observer. Luna
pinned SHA-256 `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
before content reads. The dependency is read-only; no semantic result or write
authority changed. Updated contract SHA-256: `514b13bf3934ac9723afe3f66776a0a036f0844604e373d326dc2faab436f7ba`.

## Contract revision 3

Luna pinned the original semantic authority set named by the proof lane before
further worker reads. The exact paths and hashes are in contract revision 3;
their purpose is to distinguish source-side authority from the still-missing
Rust-solution interpretation. Luna had hash-verified these files before its
initial bounded orientation read. No worker had read them under revisions 1
or 2. Updated contract SHA-256: `7660e19661ecf4d6d3fbf2ee51c7ab699952ce5966c3f07aa3d9dde32f0e5f9f`.

## Source lane finding (revision 2)

The source researcher stopped after the pinned `candidate_call.rs` trace. The
ordinary public `SolvedModule::solve` path and default-off candidate route are
distinct; successful `Ok` results can retain conflicts. The candidate
computation-source observer exposes prepared `native_root`/`entry_effect`
handles for Computation, while its Value branch returns `None`; a different
Call observer can expose an authenticated Value root only for a formal-use
Call. These are structural observations, not source Descriptor/Interface
readback or parent solution semantics. External caller coverage is unverified.
No source output file was written.

The proof researcher acknowledged contract revision 3, verified all 28 frozen
input hashes before reading the newly admitted authority sources, and resumed.
