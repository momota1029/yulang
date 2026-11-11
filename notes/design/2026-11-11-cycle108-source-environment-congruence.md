# Cycle 108: visible environment changes at the computed source boundary

Status: Draft proof plan, 2026-11-11. Scope: B4 order-independence, finite checked
source fragment. No language-semantics choice is introduced.

## Existing result and missing bridge

`RoleVisibility.resolve_congr` and `RoleDictionaries.elaborate_congr` already
prove rigid-goal invariance under equal membership of visible core declarations.
The gap-analysis estimate predates these connections; repeating those theorems
would not close a new subgoal. The next bridge is the computed source forest:
associated equations can change evidence, which changes materialized goals and
recursive dictionary payloads. Its invariance is not an immediate rewrite of the
rigid resolver.

For arbitrary associated environments E and F with exactly the same AssocImpl
members, arbitrary fixed role declarations R and finite source S, prove:

- independent associated equation Step, inductive source Derives, Models and
  AllDischarged are invariant;
- under the existing WellFormed and AssocWellFormed premises for both envs,
  the complete two-bit public observation is equal, including invalid input;
- for every returned row in each report representing the same source Clause c,
  every scalar b and full Plan p occurs on one side iff it occurs on the other.
  The payload includes declaration identity and ordered, repeated where children.

The equality-of-members input is sufficient for permutations and duplicate
occurrences of the same declaration. It does not equate different declarations
with the same head, and does not add global nonoverlap. Matching row membership
and equality to raw c remain explicit. No successful tree, dictionary, scalar
head map, state, fuel, work table or execution schedule is supplied to the run.

## Second subgoal

After publishing the first bridge, retain all failed rigid diagnostic structure
under equal visible membership, allowing only the overlap-head list's order to
change. Connect the relation to arbitrary child addresses and exact projected
Plan equality. This is diagnostic equivalence, not language-level method
observational equivalence and not a new four-way final classification.

## Specification and Yulang2

Spec 6.2 fixes caller-visible impls and ambiguity rather than first-candidate
selection. Spec 6.3 gives associated equality flow and conjunctive where children.
Read audit `y2-claims-role-boundaries-cycle-2.md`, ROLE-MORE-001/002: both orders
of two matching role implementations are ambiguous; a specific head does not
outrank a general head. ROLE-MORE-003/005 records a difference in old declared
where handling. We retain the authoritative new spec and do not import that old
behavior. These are existing audit observations, not a fresh Yulang2 execution.

## Limits

This is scope-resolved scalar evidence with int/str encoding and rigid recursive
roles. General Form/state materialization, fresh dynamic child allocation, K2,
EOF final four-way classification, parser lowering, source canonical dictionary
order and method interpretation remain open. B4's five global bridge packages
remain open, while this closes a real part of order-independence across the
source mixed-closure and dictionary boundary. No standalone concrete iff is the
primary result. Existing production modules remain unchanged except append-only
imports, audit registrations, and documentation.

## Third subgoal: expression input to the actual dictionary forest

The first two subgoals compiled and were published at 03:36 UTC. Next connect
existing checked annotated scalar Expr (literal, variable and let) directly to
the mixed-closure dictionary forest. Internally lower each validated binding to
two ordinary bounds. Prove mixed Derives iff the pre-existing independent
expression Derives, and all-model meaning of those generated bounds. Preserve
bare clauses and binding-only names, including contradictory duplicate names.
No caller passes equality atoms or successful head evidence. Unsupported Expr
and mismatching annotation fail this fragment checker, not the language itself.

For all env/roles/wf/awf, finite clause lists and finite bindings, the public
runner returns some report iff bindings evaluate to their annotations and the
clauses are well-scoped. Each dictionary payload is exactly independently
expression-derived evidence, structural materialization and the existing typed
Dictionary. All model statements quantify arbitrary name valuations, not just
an existential successful solver witness. Ordinary consistency and role success
remain separate observations.
