# Implementation handoff: local-use retention

Sprint / contract: `local-use-retention-implementation-20261017`, revision 1.
Contract SHA-256: `c6ed05c5ed10e16d97cfe4e367af5f2bc2a8e650f2169ec8e8d81b7df81e9935`.
Assignment: `local-use-retention-implementation-20261017-Luna`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Baseline: `9a2c7d80826ae33493f2bcc4786bc06e450ae36a`.

## Authority, author and frozen dependencies

User approved exact option 1 and the disclosed memory/resource tradeoff:
“採択で構いません”. Approval receipt:
`notes/progress/2026-10-17-local-use-retention-implementation-approval.md`,
SHA-256 `356231ad001a02c5085119412af26534e56e38082aca747262e8873ffa67f13c`.
Proposal: `notes/design/2026-10-17-local-use-retention-code-contract.md`,
SHA-256 `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a`.
Corrected M2 proof SHA-256
`f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.

Sole implementation source lease: `crates/yu-solver/src/candidate_scheme.rs`.
Applied source SHA-256: `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`.

Author: `/root`, Luna/high primary, current session. Observed model/effort:
UNKNOWN / UNKNOWN. Maximum 300 seconds allocated; author STOPPED after one
bounded source edit and static integration review. No descendants.

## Outcome and source correspondence

`LocalFreshRoute.rows` stays the sole row-vector owner. `FreshUse::into_retained_parts`
moves that vector unchanged and moves the other eight existing fields exactly
once into private `RetainedFreshUseMaps`. The retained record owns
`scope_remap`, `scoped_relations`, `context_use`, `terms`, `effect_operands`,
`bundle_remap`, `context_remap` and `evidence_remap`. The existing graph and
occurrence stay associated with the same route.

`RetainedFreshUseMaps::bytes` accounts every non-row backing capacity. The
inline record and unchanged rows field are included in
`size_of::<LocalFreshRoute>()`; row backing capacity is still counted once by
the existing route accounting. At commit the maps move without allocation,
and the old `retained_bytes` subtraction is removed because those capacities
remain live. Existing route reservation, fallible work ordering, rollback and
row consumers are untouched.

The corrected M2 premise remains only valid evaluations at pinned precommit
`v0`; invalidation is separate. This implementation does not add a version
checker or authorize later semantic dereferences. It proves no descriptor,
Permission, authentic At, provider lineage, receive consumer, subtraction,
NPAIR closure or production authority. Increased session memory may cause
earlier resource-limit rejection; the practical envelope remains unmeasured.

## Checks, omissions and writer status

- Inspected approved proposal bytes, `FreshUse`, route, commit and
  `refresh_bytes`, route reservation, `shadow_apply` `route.rows` consumer,
  affected test-source `route.rows` consumers, and prior architecture/spec
  reviews.
- `git diff --check`: passed.
- After source freeze, primary ran
  `cargo check -p yu-solver --features shadow-apply-candidate --tests`:
  passed in 9.12s; test targets compiled and no tests executed.
- No test execution, benchmark, probe or separate compiler run.
- No other compiler/test/source path changed by the implementation author.
- No benchmark or physical allocator/resource-acceptance claim.
- Exact next proof step: derive source-grounded postcommit ownership and
  capacity correspondence, apply corrected pinned-`v0` M2 within its stated
  lifetime premises, and identify the first unproved native NPAIR producer /
  consumer obligation without inferring semantic lineage from retained maps.

Code writer stopped; this source diff is frozen for the disjoint proof lease.
