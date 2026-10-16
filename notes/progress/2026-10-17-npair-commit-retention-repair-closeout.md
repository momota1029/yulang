# NPAIR commit-retention repair closeout

Sprint `npair-commit-retention-repair-20261017`, contract revision 2,
SHA-256 `5816b68d1cfdf2e51e519ba2864154055fe6efbffb2f02037e38b59f7d8b6fc3`.

## Outcome

**REVIEWED-PARTIAL.** The conditional finite-query retention lemma R1 was
independently CLEAN-reviewed by compiler_referee. The repaired Draft candidate
was independently CLEAN-reviewed by architect and spec_auditor within its
finite registered-query scope. These results identify the information that a
future committed Use record must preserve and address the earlier MAJOR about
FreshUse maps being discarded at commit. They do not establish that current
native code retains this information.

R1 requires a complete pre-commit projection for registered finite queries,
stable dependency lifetime/versioning, atomic publication and invalidation
before consumers. Under those premises, the projection returns the same typed
operands and Pending status after FreshUse destruction without reconstructing
discarded maps. The proof explicitly leaves source authentication, future
generation, scheduling progress, whole native `rho_u` and the actual receive
consumer open. Its CLEAN verdict is bounded to this conditional lemma.

The candidate now specifies the query projection, promotion into a session-owned
Use record before final commit, lifetime/reference rules, rollback behavior,
pending producer and wake-up conditions, completion criteria, progress
obligation, and shared-DAG/index/subscription/undo accounting. It remains Draft
and is not approved for code. The actual implementation still drops all
FreshUse maps except `rows` at `GraphState::commit_local_use`.

## Parent, limits and resources

Original `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN, as do
whole native `rho_u`, authentic NPAIR formation and replay, extrusion/intrusion,
arrival/future completeness, mixed symbolic coverage, actual subtraction
consumer, source/native adequacy, F1/FK1, soundness, principality, F5 and
production. No source or expected-output changes, tests, Cargo, probes, builds
or compiler execution occurred. No code lease was issued.

Charged 1080/1200 seconds: proof 240, architecture author 600, three reviews
240. Remaining 120 seconds (coordination and reserve) are retired. No previous
budget transfers. All assignments STOPPED; three historical UNKNOWN
reservations, quarantined board lease, and unrelated dirty sprint JSON remain
preserved.

The next sprint is
`tasks/agent-loop/sprints/local-use-existing-map-retention-20261017.md`. It
examines only already-created FreshUse maps and prepares a concrete, reviewable
code contract/patch proposal. It has no compiler source write or execution
authority. Any internal representation choice must pass `rules/design-authority.md`'s
review and explicit user-approval gate before implementation.
