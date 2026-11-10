# Cycle81: preserve source role obligations alongside equations

Status: Draft. Date: 2026-11-10. Scope: bridge 1, finite scope-resolved clauses.

## Partial goal

Close the finite source boundary that cycle80 deliberately left open: retain one
role obligation per source clause, including clauses with no associated equations,
while preserving the entire existing associated-equation projection. Compute
scope, signature arity and associated-name validation for every clause. Prove an
executable all-role discharge test equivalent to an independent conjunction of
source role obligations under an explicitly supplied scalar source-head map.

This does not infer that map from an expression or from saturation. Unsupported
scalar encodings return false in this test; this is a fragment boundary, not a
new language rejection rule or a final diagnostic classification. Bare obligations
are no longer erased, but dynamic child generation, registry visibility, general
interval knownness and source parser adequacy remain outside.

## Data and independent judgment

Reuse cycle80 Source/Clause/Equation. A checked Obligation contains a receiver
source name and a one-placeholder structural Template. A checked Package contains
an ordered list of those obligations and the existing equation Program. The
checker computes both from the same source, retaining duplicates and order.

For every role registry and source, successful checking is equivalent to source
scope/arity/name validity plus exact erasure of both projections. Empty equation
lists still require scope and arity validation for their role clause. Total role
registries do not establish source visibility or actual dictionary existence.

For every well-formed impl environment, accepted package and arbitrary map
heads : Nat -> Base, all-role execution succeeds iff every original source clause
has a structurally filled goal that independently Resolves. The independent
judgment uses Fills and Resolves, never executable resolver output. Duplicate and
permuted clauses obey conjunction semantics. No obligation can be discharged by
the absence of an associated equation.

## Authority and verification

Spec6.1–6.3 fixes role signatures, associated equations and conjunctive where
requirements. Live work/dots-audit C3-PARENT accepts both sibling orders and its
missing-child case fails. That is semantic background, not a direct oracle for
this Lean carrier. Existing scope/identity questions are not decided here.

Run a focused module build, trust=0 theorem audit, empty/bare/mixed/duplicate/
invalid-source checks, and real resolver positive and missing-dictionary cases.
No full local build or full Audit. Report remaining B4 bridges explicitly.


## Implemented boundary clarification

`runSource` computes the package and role test, so `run_source_exact` has no
successful-check premise. Its iff is validity plus independent discharge for all
source clauses. `run_source_permutation` covers arbitrary sibling permutations.
The head map is not connected to the equation saturation state. The existing
int/str materializer also limits constant templates with unused receivers.
Neither limitation is a new language rule; false is not final classification.
