# Local-use retention proposal repair handoff

Sprint-ID / contract revision and SHA-256:
`local-use-retention-proposal-repair-20261017`, revision 1;
`8d1bd53dab64ae049a04ca506bc75f469479de3b7b4a525d6f1c0900c9578cb4`.

Assignment-ID / handoff revision:
`LOCAL-MAP-RETENTION-PROPOSAL-20261017`, revision 2. Revision 1 remains
immutable in `tasks/agent-loop/snapshots/20261017-local-use-retention-proposal-handoff-pre-repair.md`.

Parent gate / original theorem:
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN; original source
scope and quantifiers unchanged. See corrected proof and the closed prior-sprint
receipt for exact parent route and exclusions.

Baseline and direct source hashes:

- `candidate_scheme.rs`: `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
- `shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- `candidate_intrusion_tests.rs`: `30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3`.
- Corrected M2 proof: `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
- M2 correction handoff: `2d3ca0ff0115f4098dd763b8c9ec3d8468d00c47007f51cca66d93bbad0218e2`.
- Old proposal and handoff snapshots: `a346ef6812109eb181cf160127959ac8320389b1a8a2d52e566464039601fb55` and `572e06a32b268dc3d089c5b4d27b4361fa194ca133857dc6bb2da8c7edec14ad`.

Role / author / session:
Luna primary author and sole integrator, current session; no descendants.

Outcome class:
Unapplied code proposal revision 2. No compiler or test source changed.

Correction:
Preserve `LocalFreshRoute.rows` as its current sole row-vector owner. The exact
single-file patch introduces `RetainedFreshUseMaps`, moves every other
`FreshUse` field exactly once into it, and records its separately allocated
capacities in `refresh_bytes`. The existing route and test consumers continue to
read `route.rows`; no duplicate row vector or sibling-module accessor is added.
The record header is accounted through `size_of::<LocalFreshRoute>()`; backing
allocations exclude rows and are counted through `RetainedFreshUseMaps::bytes()`.
No allocation is added at commit and no retained map charge is subtracted.

Resource disclosure:
Retaining construction maps increases session memory and may cause earlier
resource-limit rejection. The practical envelope and overhead are unmeasured;
no unchanged resource-acceptance claim is made.

M2 boundary / parent application:
For queries validly evaluated at pinned precommit version `v0`, M2 preserves the
answer. Invalid or changed projections have no equality claim. The patch adds no
version checker, immutable historical snapshot, NPAIR descriptor/Permission,
At, provider lineage, consumer selection, subtraction, source/native adequacy or
whole-`rho_u` result. Referent lifetime, ID non-reuse, relocation and later
invalidation remain unproved implementation obligations. Parent and production
remain OPEN.

Exact frozen outputs:

- `notes/design/2026-10-17-local-use-retention-code-contract.md`
- `tasks/agent-loop/inbox/20261017-local-use-retention-code-proposal-repair.md`

Checks:
Static inspection and source SHA-256 verification only. No tests, probes,
builds, Cargo or compiler execution. Prior current-contract state check is not
runtime or mathematical evidence.

Resource cap:
Luna proposal repair 120s maximum; conservatively charge the full allocation,
exact elapsed UNKNOWN. No carryover from closed sprint.

Next step:
Freeze output hashes, then assign an independent architect delta review (90s).
After architect STOP, assign independent spec audit (90s). If either finds a
blocking/major issue or the packet exceeds its cap, reconcile rather than
expanding scope. CLEAN reviews prepare a user decision only; explicit approval
of this exact option is required before a separate code sprint.

Mutual TODO `LOCAL-MAP-RETENTION-PROPOSAL-20261017`:
Review the rows-preserving single-file split, exact map-field completeness,
source applicability, exact-once resource accounting and memory limitation.
Falsifiers: any current `rows` consumer broken; any `FreshUse` field dropped or
duplicated; any backing allocation counted twice/not at all; any invalid-v0
equality claim; or any inference of NPAIR authentication from map presence.

Writer state:
Luna STOPPED after freezing both exact outputs. No descendants or background
work. Independent reviews remain to be assigned by Luna.
