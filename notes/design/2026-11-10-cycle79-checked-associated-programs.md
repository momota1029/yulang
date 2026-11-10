# Cycle79: checked source associated programs

Status: Draft. B4 bridge 1, 2026-11-10. Design saved before implementation.

## Objective

Close the executable whole-program elaboration boundary for a finite list of
scope-resolved associated obligations with raw goal syntax. Compute placeholder
scope, declared role arity, and associated-name membership instead of asking a
caller to supply a valid Template. Preserve every occurrence, order, source
receiver/output name, associated name, and goal exactly on successful checking.

The registry remains the existing total Roles.RoleDecls function. This does not
claim source declaration visibility, parsing, registry well-formedness, general
interval receiver materialization, or dynamic where completeness. The checker
recognizes a fragment; rejection is not a new language rule. Existing spec6.1–6.3
and Roles.RoleDecl/AssocWellFormed already determine arity and associated names.
The sole-placeholder limitation and int/str materialization are cycle78's
implementation boundary, not new semantics. No unresolved identity decision.

## Data and theorem contract

RawOccurrence stores receiver/output/name and a Roles.Goal without proof fields.
An independent Valid predicate requires scope bound ≤1, role arity equality,
and a declared associated name. RawProgram validity is pointwise membership.
Erase removes proof fields from cycle78's Program. Elaboration returns Option
Program. For all roles/raw/program, elaboration returns program iff erase
program equals raw and raw is valid. Acceptance iff every input occurrence is
valid; failure iff some occurrence is invalid. Thus no row disappears or changes.

Lift accepted programs into the existing exact execution contracts. For all
well-formed core/associated registries, successful checking, arbitrary old
states and all ordinary assignments, the actual solver keeps cycle78's exact
source-model contract. Success of resolution or model existence is not a
checking premise. Prove generated materializations have declared arity/name.

Test empty program, valid multi-row shared names, nested placeholders, out-of-
scope variables, wrong arity and undeclared names. Five B4 bridges stay open.
