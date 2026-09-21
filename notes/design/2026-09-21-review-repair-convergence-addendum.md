# Review and repair convergence addendum

Status: Authoritative
Scope: repository-wide review/repair continuation and return-to-design policy
Approved-by: user
Approved-at: 2026-09-21
Drafted-by: primary agent
Reviewed-by: spec_auditor
Supersedes: numeric review/repair round caps and normal-round-limit return clauses

## Decision

Review and repair have no numeric round limit. Continue with one batched repair
pass and focused delta review while the latest required review contains an
accepted `BLOCKING` or `major` finding and each pass closes or materially
narrows concrete findings.

A newly noticed risk starts another repair pass only after the primary
adjudicates it as an accepted `BLOCKING` or `major` finding. Minor-only
textual or test-comment repairs retain the primary-inspection exception in the
active orchestration rules.

Return to design or to the user only when a finding exposes missing authority
or a missing decision, a semantic contradiction, a false premise, a required
scope expansion, or a repair round makes no material progress. An elapsed
round count is never by itself a reason to stop.

## Preserved controls

This addendum does not remove:

- M0-M3 reviewer-count limits;
- one write-capable agent at a time and producer/reviewer separation;
- finding adjudication and batching;
- focused delta-review scope;
- verification, broad-test, and performance-measurement budgets;
- historical records of how many rounds earlier work actually used.

Adding reviewers or measurements merely for reassurance remains forbidden.

## Narrow supersession

This addendum supersedes every active numeric review/repair round cap and every
instruction to return to design merely because a "normal", M2, or M3 round
limit was reached. In particular it supersedes the normal-round-limit clauses
in:

- `2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md`;
- `2026-09-18-hir-operator-association-first-slice-draft.md`.

Those documents otherwise retain their authority, and their historical round
counts remain unchanged.
