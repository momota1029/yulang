# Cycle124: recording source dictionary equations

Status: Draft implementation boundary, 2026-11-11. I-18 item5, narrowing the
Evidence bridge. Items1 and2 remain owned by Astra and are not changed.

## Goal and boundary

The previous cycle's PlannedEvidence still takes a term interpretation and a
Recorded premise. Actual declaration terms cannot yet be derived generally:
nominal constructors lack a Common interpretation and interval captures must
not silently acquire a centre. Independently, remove manual Recorded proofs by
implementing the exact finite ordinary-constraint update for Located packages.
This is a dictionary equation transaction, not general Step or candidate selection.

Data: an existing checked State and source-indexed Located head/output packages.
The executable update appends two inequalities for each argument and two for each
output occurrence. Slots, separate type/row source maps, observations and interval
identities are retained. Existing invariants follow from old ordinary constraints.

Independent meaning: for every assignment M, updated Models M iff old Models M
and every package's interval/output equations hold at M. Satisfiability is
preserved exactly when all new obligations have a common old model. No model
existence is assumed silently. Multiplicity and source identities remain intact.

Planned theorems: exact model law, automatic Recorded, source-preserving Refines,
model conservation when already entailed, non-vacuous/rejection regressions.
Compose these with whole-dictionary evidence without claiming declaration-term
adequacy or that any general B4Bridges field is closed.

Authority: spec06 §§6.2–6.3 and §6.5; existing dictionary modules; Yulang2
ROLE-MORE-001 through 005. Old advertised-where behavior is not imported.

## Declaration-body provenance and representation boundary

Actual checked declarations supply explicit associated Equation bodies; absent
explicit names fall back to the role's declared default. The tagged Body keeps
these distinct: explicit Pattern variables are captured declaration names,
default Roles.Term variables are positional role arguments. Independent Supplies
uses membership/absence, not the executable lookup. Its exactness and coverage
are established under the actual signature and name-uniqueness certificates.
Mapping over demand.outputs retains all names, targets, order and duplicates.

A combined OutputPlan must select one actual visible declaration by its checked
ID for both canonical children and root outputs. Two separately chosen arbitrary
term and child relations are not substituted for that connection.

The remaining general interpretation is not a new semantic choice to hide:
TyTerm has no nominal node; the constructor catalogue has layout but no Common
meaning or variance; Capture has interval endpoints and no centre; compound
requests have not been materialized. Spec06 §6.5 already requires center-free
intervals, and the B5 interval design excludes encoding nominal names as variant
tags. The implementation preserves these gaps and does not invent a centre,
nominal carrier map, or a conversion between default and explicit binder scopes.
