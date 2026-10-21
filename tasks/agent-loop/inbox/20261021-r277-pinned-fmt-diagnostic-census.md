# R277 primary handoff — pinned fmt diagnostic census

Contract: `tasks/agent-loop/sprints/r277-pinned-fmt-diagnostic-census-20261021.md`.
Baseline: `7d9a68922`.
Status: checkpointed; primary-only, unreviewed.
Parent: unchanged R149 Types/Console and broader Yulang2 sample goal.

R276 pins `lib/std/core/fmt.yu` to blob
`fd7b6607094c9ad70bde1fd41890363fa8bd6b31` and records that the current parser
reports syntax diagnostics, so no `ShadowArtifact` is published. R277 retains
all 50 diagnostic ranges and classifies them as 36 root `ErrorGroup`s, 7
`OperatorChain` `ErrorGroup`s, and 7 missing `CaseArm`s. The test checks exact
blob identity, range-to-source validity, diagnostic order, and category
totals; each occurrence also carries a bounded exact-source excerpt. Root groups cover role fields, implementation fields, and `where`
constraints; the other groups arise in expression syntax. This spans multiple
`yu-syntax` owners and source carriers, beyond R277's leases. No parser edit
was made.

Proof: R149 and its source/native correspondence remain OPEN. No worker is
assigned under the user-directed solo constraint. No role solving, imports,
inference, execution, proof closure or production promotion is in scope.

Verification: focused census test, `cargo check -p yu-playground`, sprint
static check and `git diff --check` passed; no broad suite. The exact
next owner is a versioned grammar/source-carrier design spanning role and
implementation members, `where` clauses, operator expressions, and case-arm
recovery. R149 sample execution, proof, and production remain OPEN.
