# Callback endpoint policy and task-ledger compactification

Date: 2026-10-04. Scope: durable record of the user's B/A clarification and
navigation cleanup; no compiler implementation.

## Authority adjudication

The bounded Authoritative callback contract already required expected
callback context before body constraints, selected Handler role from that
context, independently formed parameter/body interfaces, rejected copying or
equating expected endpoints into the literal, and compared the completed
interface using ordinary subtyping (§2, `notes/design/2026-10-03-callback-context-delivery.md`).
This already ruled out early substitutions that impose stronger constraints
than that eventual comparison.

The user's 2026-10-04 instruction made the following additional choices
explicit: call that ordering **B** and make it the normative/reference
constraint-generation semantics; name the completed-interface check as one
ordinary `F_lit <: F_cb`; allow **A** only as scheduling/partial evaluation of
logical consequences of B; and require observational/solution equivalence
covering acceptance, principal solutions, method/adapter choices, and
residual/evidence semantics. No algorithm, API, phase, or implementation was
selected.

These additions are recorded in callback-context-delivery §2.1. A bounded
compiler-referee delta review found no BLOCKING, major, or minor issue and
confirmed that the text preserves the explicit implementation boundary. The
user's direct instruction supplies authority; the review checked faithful
recording and invariants, and did not ask for the same approval again.

## Current navigation

`tasks/current.md` now leads with the full objective, closed decisions, the
active Pure-value callback theorem, remaining milestone blockers, and direct
links to governing designs. The prior 2,554-line chronological ledger was
moved, with its substantive content preserved, to
`notes/progress/2026-10-04-task-ledger-before-compaction.md`. Its archive notice
points readers back to the compact current task; historical/intermediate
statements remain traceable and do not override later authority.

`notes/design/INDEX.md` now distinguishes the closed B/A policy from the
still-open callback proof clauses and links to the active progress record.
The source design remains authoritative; the index remains navigation only.

## Verification and residuals

`git diff --check` and bounded link/path review are the appropriate checks for
this record-only/documentation update. No tests, builds, or measurements were
run. The callback theorem remains open for whole-carrier admission/domain
inclusion, endpoint/profile adequacy, and observation-bound inclusion; the
larger source-State and Milestone-3 blockers are summarized in `tasks/current.md`.

## Follow-up compactification

The user requested a further reduction of `tasks/current.md` to current
decisions, proof gates, blockers, and governing links. The detailed callback
witness clauses remain in
`notes/progress/2026-10-04-value-entry-bind-projection.md`; structural witness
limits remain in
`notes/progress/2026-10-04-root-only-regular-witness.md`; State observations
and the missing source bridge remain in
`notes/progress/2026-10-04-local-state-capture-observation.md`; chronological
investigations remain in the archived task ledger. No decision or design status
changed in this navigation edit. `notes/design/INDEX.md` labels the callback
contract as closed and the Pure-value theorem as open, and distinguishes the
B/A requirements already in the Authoritative source contract from the explicit
optimization-equivalence clarification recorded on 2026-10-04.

The follow-up compactification is complete: `tasks/current.md` now keeps only
the full objective, closed decisions, active proof gates/blockers, and governing
design/history links. The index now has a short active-inference navigation
section and the callback row restates the exact closed/open split. Authority
adjudication remains unchanged: B's ordering and ordinary final inequality
followed from the existing Authoritative contract; the user's explicit B
reference designation, allowance of A as an optimization, and named
observational/solution-equivalence conditions are the newly clarified durable
content. No unresolved semantic choice was found, so no user decision is
pending.
