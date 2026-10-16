# Sprint local-use-retention-proposal-repair-20261017

Status: proposed by `next_action_selector` and accepted by Luna as a bounded
correction sprint. It repairs one MAJOR proposal source-applicability finding;
it grants no compiler-code authority.
Branch: `research/simple-sub-intrusion`.
Administrative baseline: `c9993c2b3` plus the closeout commit containing this
contract.
Original proof sprint: `local-use-existing-map-retention-20261017`, closed
PARTIAL — M2 CLEAN, proposal MAJOR.

## Outcome

Produce a revised, unapplied retention contract and exact proposal patch that
preserves `LocalFreshRoute.rows` and its existing `shadow_apply` and test
consumers, while moving each other existing `FreshUse` map exactly once into a
separate retained owner. Count every map allocation and inline header exactly
once. Explicitly state the memory/resource acceptance cost. No compiler source,
tests, fixtures, expected outputs, or semantics may be changed in this sprint.

The original parent and quantifiers remain unchanged:
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN. The only proof input
is corrected M2: equality for valid evaluations at pinned precommit `v0`;
invalidation is separate and has no equality conclusion. The proposed storage
does not implement a version checker, historic projection, NPAIR descriptor,
Permission, At, provider lineage, consumer selection or subtraction.

## Frozen inputs and source pins

- Corrected proof `notes/theory/2026-10-17-local-use-existing-map-retention.md`:
  `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
- M2 correction handoff:
  `tasks/agent-loop/inbox/20261017-local-use-map-version-repair.md`,
  `2d3ca0ff0115f4098dd763b8c9ec3d8468d00c47007f51cca66d93bbad0218e2`.
- Immutable proposal/handoff snapshots listed in the old sprint closeout.
- Current `candidate_scheme.rs`:
  `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
- Current `shadow_apply.rs`:
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- Current `candidate_intrusion_tests.rs`:
  `30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3`.
- Corrected sprint contract and review handoffs are additional exact pins at
  proposal launch; a pin mismatch stops the packet.

Architect's MAJOR finding was that `shadow_apply.rs::fresh_use` constructs
`CandidateGraphFreshUse` using `route.rows`, and tests use `route.rows` for
local-route row images. Keep that field and its owner. Do not duplicate its
vector and do not redirect the sibling consumer across a private-field
boundary. A candidate is to destructure `FreshUse` at commit, move `rows`
into its existing `LocalFreshRoute.rows`, and move every other map into one
new private retained-maps record owned by that route. The patch must show the
complete field list and account each backing capacity and inline header once.
If this cannot be shown to preserve the current single-source-file write
boundary, stop and return a concrete reason rather than expanding code scope.

Resource disclosure must use this wording or a materially equivalent clear
statement:

> Retaining construction maps increases session memory and may cause earlier
> resource-limit rejection. The practical envelope and overhead are unmeasured;
> no unchanged resource-acceptance claim is made.

## Exact leases and reviewers

Luna author, maximum 120s, may write only:

- `notes/design/2026-10-17-local-use-retention-code-contract.md`
- `tasks/agent-loop/inbox/20261017-local-use-retention-code-proposal-repair.md`

Before editing, snapshot and hash current proposal bytes are already preserved.
The new handoff is sequential revision 2 under the same proposal assignment.

After author STOP and exact byte/hash freeze:

1. Fresh independent architect delta review, 90s, read-only, exact two-output
   lease only. Check the field split, `rows` call sites, source applicability,
   atomic commit, rollback, capacity/header accounting and memory statement.
2. Only after architect STOP, fresh independent spec audit, 90s, read-only.
   Check M2's pinned-version boundary, no semantic authentication from maps,
   no language/expected-output change, and approval gate.

Luna coordination is capped at 30s. Reserve is 30s. Total new sprint cap is
360s. No carryover from the closed sprint. If any lane exceeds its cap, STOP
and reconcile; do not silently expand resources or source scope.

## Checks and stop conditions

Allowed evidence for the author/reviewers: hash verification and static source
inspection of the pinned constructor, commit, accounting, rollback, export
adapter and affected test source. No tests, probes, builds, Cargo, compiler
execution, or changes to compiler/test files. These checks cannot prove runtime
resource behavior. The proof's identity/lifetime/version premises remain
unverified implementation obligations.

Success is a frozen proposal that composes with all existing `rows` consumers,
accounts moved allocations exactly once, states resource uncertainty, and
receives CLEAN architect/spec reviews. This still only prepares a user decision.
After both reviews, Luna presents the exact proposal, alternatives and memory
tradeoff. Only explicit user approval can authorize a separate code sprint.

Preserve unrelated dirty work, three historical UNKNOWN reservations and the
quarantined board lease. Luna remains sole integrator; exact-path staging and
non-forced push only.
