# Cycle80: grouped associated-clause extraction

Status: Draft. Date: 2026-11-10. Scope: bridge 1, finite scope-resolved associated obligations.

## Partial goal and boundary

Close exact extraction of every associated equation from an arbitrary finite list
of scope-resolved where clauses. Each clause supplies a receiver source name, a
structural goal, and an ordered list of associated name/output source-name pairs.
Extraction expands every pair once, keeps clause and equation order, and feeds the
cycle79 checker. This is the associated-equation projection only. A clause with no
associated equations contributes no propagation edge; its bare role obligation
still exists and is NOT solved or discharged by this projection.

The syntax here is a new small Lean carrier, not the Rust parser AST. Source name
resolution, visibility and registry validation remain outside. The one-placeholder
fragment and existing int/str materialization remain unchanged. No dynamic child
selection, persistent invocation identity, T13 desugaring or new refusal semantics
is chosen. Spec6.3 fixes associated equalities and shared ordinary variables;
spec6.1–6.2 fix declarations. Existing Q1/Q2 and cycle23/24 questions remain open.

## Data, execution, independent statements

`Equation` contains `name : Nat` and `output : Nat`. `Clause` contains
`receiver : Nat`, `goal : Roles.Goal` and `equations : List Equation`.
`Source := List Clause`. `row clause equation` makes one RawOccurrence;
`lower` concatenates the per-clause row maps. No caller-supplied occurrence list,
slot map, validity certificate, fuel, valuation or completed frontier is needed.

The independent `Occurs source row` judgment has an explicit clause-membership
and equation-membership derivation. Its equivalence to generated-list membership
is proved rather than assumed. Exact list equations and length conservation also
preserve multiplicity and order, which membership alone would not establish.

For all finite sources and total role registries:
- `r ∈ lower source ↔ Occurs source r` (both directions, arbitrary row).
- `(lower source).length = sum of equation counts` (including duplicate equations).
- checker success iff exact erasure equals lower source and each source equation
  satisfies the existing scope/arity/associated-name checker.
- failure iff an explicit source clause/equation violates that checker.

Independent source-name `Derives` reads a clause and an equation, uses structural
`Fills`, independent `Resolves`/`AssocDerives`, and scalar decoding. It never calls
the executable resolver. For every successful check and all old states, it is
proved equivalent to cycle78's structural derivations, then connected to actual
saturation evidence and source models. The initial-state seed interface still uses
the accepted program's computed table; source expression inference is not proved.

## Verification and comparison

Focused module build and trust=0 theorem audit; regressions cover empty sources,
empty association lists, multiple equations, duplicates, shared source names,
invalid middle clauses/equations and concrete propagation. No full local build.
Live audit 55574b605 C3-PARENT accepts both sibling orders and generic form, while
missing-child fails. These are semantic background, not an oracle for this new
Lean syntax carrier. No new Yulang2 run or Rust parser adequacy claim.
