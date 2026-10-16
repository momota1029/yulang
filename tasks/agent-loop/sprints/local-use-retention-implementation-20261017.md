# Sprint local-use-retention-implementation-20261017

Status: ACTIVE, user-approved bounded implementation plus independent proof.
Branch / baseline: `research/simple-sub-intrusion` / `9a2c7d80826ae33493f2bcc4786bc06e450ae36a`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Approval: `notes/progress/2026-10-17-local-use-retention-implementation-approval.md`.
Approval receipt SHA-256:
`356231ad001a02c5085119412af26534e56e38082aca747262e8873ffa67f13c`.

## Original outcome and success evidence

Implement and prove the reviewed postcommit structural-retention invariant:
after a successful local-use commit, the route keeps the existing `Graph` and
sole `rows` owner, and retains each of the other eight `FreshUse` maps exactly
once. The corrected M2 claim remains limited to valid finite structural-query
evaluations at pinned precommit `v0`; invalidation is a separate outcome.

Success evidence: exact single-file patch matches the approved representation;
all route and frame byte formulas account each backing allocation and inline
header once; publication remains a move after preflight and has no new fallible
step; rollback/drop behavior remains route-owned; fresh independent reviews find
no blocking/major issue; compile-only check succeeds if authorized by this
contract; proof applies the bounded invariant to its parent and names the next
exact native obligation. This is not NPAIR closure.

## Authority, inputs and pins

User approval: exact option 1 and memory/resource tradeoff, recorded in the
approval receipt above. Independent proposal reviews were CLEAN. No semantic or
expected-output change is authorized.

- Proposal SHA-256:
  `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a`.
- Proposal review handoff SHA-256:
  `e2a0f6afafbb74785d2d5c7bc16753cbbfb0a9ef6d2b01b6b37897e808331c4d`.
- Corrected M2 SHA-256:
  `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
- `candidate_scheme.rs` baseline SHA-256:
  `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
- `shadow_apply.rs` baseline SHA-256:
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- `lib.rs` baseline SHA-256:
  `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
- `candidate_source.rs` baseline SHA-256:
  `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.
- Affected local-route source test SHA-256:
  `30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3`.
- Prior NPAIR formation obstruction SHA-256:
  `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f`.
- Adopted source-formation boundary receipt SHA-256:
  `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.

Any pin mismatch or newly discovered required semantic decision stops the
affected lane and returns to Luna. The proof author may use frozen candidate
source only after the implementation author has stopped and the applied diff is
frozen.

## Implementation lane — Luna, maximum 300s

Only write:

- `crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/20261017-local-use-retention-implementation.md`

Transfer the existing `rows` vector into `LocalFreshRoute.rows`; destructure
`FreshUse` and move its other eight fields once into one private route-owned
retained record. Account all non-row map capacities there; preserve existing
row, graph, route growth and rollback owners. Remove the commit-time release
subtraction because those bytes remain retained. Do not modify call sites,
tests, fixtures, expected outputs, APIs, semantics or adjacent abstractions.
Record a frozen handoff with source diff, exact hashes, checks, omissions and
writer STOP receipt. No proof author starts before this freeze.

## Independent proof lane — Sol, maximum 360s

After implementation STOP and frozen diff, write only:

- `notes/theory/2026-10-17-local-use-retention-applied-correspondence.md`
- `tasks/agent-loop/inbox/20261017-local-use-retention-applied-correspondence.md`

Prove the postcommit ownership/capacity correspondence from the frozen source.
Apply corrected M2 only under its valid same-`v0` and lifetime premises. Connect
the retained structural maps to the original local-use route and clearly
separate that correspondence from descriptor/Permission, authentic At,
provider-lineage, consumer-selection and subtraction claims. Do not repeat the
completed obstruction census. End with the exact next native NPAIR producer /
consumer obligation and owner. No compiler edits or semantic authority.

## Review, checks and budget

One author at a time; three historical UNKNOWN reservations and the quarantined
board lease remain. Fresh sequential read-only reviews after both lanes:

1. `compiler_referee`, max 120s: source diff, exact-once fields, accounting,
   commit/rollback, correspondence proof and scope boundary.
2. `architect`, max 100s: ownership/lifecycle, route sizing, reservation,
   rollback and retained allocation accounting.
3. `spec_auditor`, max 80s: exact approval scope, corrected M2 boundary and
   no promotion of structural maps into semantics.

Total envelope 1200s: implementation 300, proof 360, reviews 300, one
compile-only check 120, coordination 60, reserve 60. Run at most one compile-only
check after source freeze using `shadow-apply-candidate`; compile test targets
only and execute no tests. Failure stops for reconciliation; no automatic
retry. Do not run benchmarks or claim physical allocator equivalence. Preserve
the stated increased-memory / possible-earlier-resource-rejection limitation.

Exact proof/code output leases above are disjoint. Reviewers are not authors or
coauthors. Luna alone adjudicates, updates compact state, stages explicit paths,
commits and pushes non-forced. Preserve the unrelated modified
`tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`.

## Parent limits and stop conditions

This sprint can close only the bounded implementation and correspondence
invariant. It cannot close authentic negative pair formation, NPAIR `rho_u`,
source/native adequacy, actual receive consumer, subtraction, N-Transport,
mixed/multiple-symbolic coverage, F1/FK1 or production. Existing language
meaning and expected-output protection remain unchanged.

Stop a lane on pin mismatch, authority/dependency/lease expansion, unresolved
resource accounting, runtime failure, exhausted budget, unavailable reviewer,
writer cessation uncertainty or session STOP. Preserve unknown leases and
reservations; do not leave a worker falsely RUNNING. Freeze an outcome receipt
and consult the dispatcher at the sprint-end boundary.
