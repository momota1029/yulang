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
