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
