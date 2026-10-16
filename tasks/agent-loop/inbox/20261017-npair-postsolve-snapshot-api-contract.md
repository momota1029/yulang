# Post-solve snapshot API readiness handoff

Sprint `npair-postsolve-snapshot-capability-20261017`, revision 1; contract
SHA-256 `3709fc3ee119b95583b2b92ce8c3aa7820e8ac8723b2f0441cc402b266433637`.
Assignment `NPAIR-POSTSOLVE-SNAPSHOT-API-CONTRACT-20261017`, handoff revision 1.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

Author Luna/high primary; exact outputs are this handoff and
`notes/design/2026-10-17-npair-postsolve-snapshot-api-contract.md`.
Readiness cap 300s. No compiler source lease.

## Frozen inputs and result

Proof artifact `notes/theory/2026-10-17-npair-postsolve-snapshot-capability.md`
SHA-256 `9e1ae6e71f095b89b09796e5da375d1f152427b658b6fe3bc045553632a4a3d6`;
proof handoff `tasks/agent-loop/inbox/20261017-npair-postsolve-snapshot-capability.md`
SHA-256 `cb14c88835e0a8e17b95d394a0e8889c64502500df24cba41c3785f201e6849b`.
All contract and ten source/prior-artifact pins matched in the producer receipt.

The actionable API proposal transfers original `bounds`/`effect_bounds` into
candidate-only retained storage before the consuming session is dropped,
constructs only private owner-bound borrowed views, and resolves every physical
slot through original row/lane/index/operand storage. This avoids cloning and
keeps ordinary `SolvedModule` retention separate. It requires resource-ledger
changes for the longer retained lifetime.

The exact proof blocker remains decisive: returned `FrozenInferenceData` omits
both physical vectors, so no current post-solve accessor can inspect the
original physical slot. The proposal does not establish the quiescence
predicate, complete evidence coverage, or authentication of unavailable
OwnerEmission/ExtrusionLink/FreshUse antecedents. Those cases remain explicit
incomplete/reject results. Implementation readiness and parent closure remain
OPEN. Same-owner construction is proposed but not implemented.

Frozen design SHA-256:
`ee0cf9823b0cb7e44e512f535ec0dc4980df73fa69cf83aed0e0b4d4739f7488`.
No tests, builds, probes, Cargo, source/compiler execution, code, or semantic
changes.

## Next review and resource envelope

After Luna STOP, run the contract's sequential reviews: compiler_referee 120s,
architect 60s, spec_auditor 60s. Sprint accounting: 60s coordination; proof
measured 142s and charged 180s; readiness conservatively charged at its full 300s cap; reviews cap
240s; reserve 60s. No cross-sprint carry-over. Fresh review must check storage
transfer, resource retention, owner identity, unproved quiescence, incomplete
evidence, and exact separation from source semantics. No code follows without a
new implementation gate.
