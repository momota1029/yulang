# R143 admission

Luna admits `EFFECT-PERMISSION-ORDERED-SNAPSHOT-KERNEL-CHECK/20261102-R143`
under the unchanged Yulang Rust/Lean soundness goal. The dispatcher selected a
single native kernel check of the frozen R140 module, with bounded repairs only
for actual elaboration diagnostics. The R140 file remains immutable.

The exact Lean input is SHA-256
`da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985` and the
native Lean binary is pinned by path and SHA-256 in the admitted contract.
Execution is authorized only under its process-group sampling, CPU, wall-time,
aggregate-call, stop, and review limits. Thread-creation failure before
elaboration means immediate stop without retry.

R143 can establish kernel acceptance of the ordered projection model only.
Rust source/native equality, the original theorem, effect hygiene H, A/B and
production remain OPEN. Dirty and quarantined paths remain outside all leases.

Contract:
`tasks/agent-loop/sprints/effect-permission-ordered-snapshot-kernel-check-20261102-r143.md`.
