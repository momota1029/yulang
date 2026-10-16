# Sprint npair-concrete-producer-realization-20261017

Status: ACTIVE for proof; compiler implementation WAITING for explicit user
approval of the frozen reviewed proposal. Parent:
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary: Luna/high; Luna remains the sole Git integrator and current-state owner.

## Fixed outcome

Implement the reviewed concrete-only negative formal-port producer after
approval, prove its bounded source/native correspondence, and locate the first
missing authentic ingress step. Do not claim source acceptance, universal
formation readiness, parent closure or production authority.

Previous reviewed baseline commit:
`d1b706e83` (`Record reviewed NPAIR native port contract`).
Effective reviewed design:
`notes/design/2026-10-17-npair-native-port-code-contract.md`, SHA-256
`a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce`.
Review handoff revision 3:
`tasks/agent-loop/inbox/20261017-npair-native-port-code-contract.md`, SHA-256
`6ec84d409f261345ab682c1d37b6d41126fb7d69fff2577ab580bc92a295c3d1`.
Formation proof:
`notes/theory/2026-10-17-npair-native-port-formation.md`, SHA-256
`a7be614af3b432e785fb64d2580ee30de30c448ba5d332e5c40162cb4578ce4f`.

All direct source/adoption dependencies must be re-hashed from the predecessor
contract and proof before reliance. Freeze the new source-owner pins before any
implementation write.

Pinned governing/source inputs at baseline `d1b706e83`:

- Adopted NPAIR definition: `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md`, SHA-256 `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`.
- Adoption receipt: `notes/design/2026-10-17-source-formation-proposals-adoption.md`, SHA-256 `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Existing readiness contract: `notes/design/2026-10-17-negative-pair-native-implementation-contract.md`, SHA-256 `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064`.
- Receive obstruction: `notes/theory/2026-10-17-receive-negative-pair-construction.md`, SHA-256 `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f`.
- Native formation proof: `a7be614af3b432e785fb64d2580ee30de30c448ba5d332e5c40162cb4578ce4f` (path above).
- Reviewed producer design: `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce` (path above).
- `candidate_effect.rs`: `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9`.
- `candidate_source.rs`: `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.
- `candidate_context.rs`: `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
- `lib.rs`: `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.

## Proof lane — Astra/medium, maximum 720 seconds, at most five stages

Sole outputs:

- `notes/theory/2026-10-17-npair-concrete-producer-refinement.md`
- `tasks/agent-loop/inbox/20261017-npair-concrete-producer-refinement.md`

Derive the concrete-only producer refinement: one fresh shared row, distinct
source Permission data, all Function children and slots 43/44, pair publication
and route rollback obligations. Apply this result to the original receive route.
Inspect actual Function lower propagation and `BoundAdmissionCause` to locate
the first missing antecedent for authentic `At`; return an exact obstruction if
the inputs cannot be reconstructed. Keep mixed/multiple-symbolic `C_sym`, full
operands and all parent quantifiers open. No code/test writes.

## Implementation lane — Luna/high, maximum 1080 seconds, WAITING for approval

After the user approves the exact reviewed patch, Luna may edit only:

- `crates/yu-solver/src/candidate_effect.rs`
- `tasks/agent-loop/inbox/20261017-npair-concrete-producer-implementation.md`

Implement the effective reviewed contract: internal pair predicate and port
branch; existing order of all four value/effect operations with exact child
paths and error restoration; self-contained Permission records; ownership,
checked accounting and route rollback. Preserve source preflight refusal and
root computation-effect handling. Stop before writing if accountable identity
storage or rollback requires another file/design. No preflight/source acceptance
change, no tests/fixtures/expected-output changes, no `At`, transport, consumer,
or subtraction code.

Until explicit approval arrives, the implementation worker and source path lease
remain WAITING/quarantined; no compiler edits are authorized. The approval does
not extend to mixed, multiple-symbolic, or explicit-empty forms.

## Review, resources and boundaries

Fresh sequential compiler, architecture and specification reviewers receive
the frozen proof and code snapshots, at most 120 seconds each. Total envelope:
2400 seconds (proof 720, implementation 1080 conditional, reviews 360,
coordination 120, reserve 120). No test or build execution is authorized by
this contract. One Astra assignment maximum; retain the three historical
UNKNOWN reservations and quarantined board lease.

Stop on approval absence for the implementation lane, a changed source-owner
pin, a missing identity/accounting representation requiring broader authority,
any reviewer finding, or exhausted cap. Keep NPAIR mixed-source coverage,
authentic ingress `At`, N-Transport, whole `rho_u`, J1/J2 future completeness,
actual receive consumer, subtraction, F1/FK1, source/native adequacy and
production OPEN.
