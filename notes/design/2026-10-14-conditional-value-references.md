# Conditional result Value references

Status: Draft; the new result-incidence choice is not implementation authority.
Scope: source Value-reference edges for the newly supported private If carrier.
Baseline: `13c100980a75e294fb78200de51cf702d7499483`.
Existing authority: top-level inference principles §1.1; parent-copy SCC
intrusion, definition-root ownership and selected Apply fragment membership.

## Already determined

Both branches contribute type constraints even for a constant condition.
Every condition and branch is traversed for its enclosing definition's source
references. Nested local initializers retain their own definition owner.
The existing If grammar is unchanged: `if p: f else: g` is an inline example.
The new carrier requires an explicit else; it does not decide the value of an
omitted else. Boolean literal resolution follows frozen Oracle `a58eefc31`,
`crates/infer/src/lowering/name_ref.rs:72`: lexical bindings, Boolean literals,
then module lookup. These facts do not determine a new If-result adjacency.

The earlier Apply decision explicitly limits recursive fragment membership to
Name and nested Apply. It cannot silently authorize traversal through a new
If result. Type bounds and containment alone do not add Value-reference edges.

## Choice A: condition and every branch (proposed)

For `if p: f else: g`, the conditional result's source references include
`p`, `f`, and `g`. Every elsif contributes its condition and branch as well.
No condition is executed to select references. These are edges to the actual
resolved Name Values, not to arbitrary type rows or branch-result Values.

Construct one shared auxiliary fragment for each new If, following its
condition/body/else children whose forms are Name, Apply or If. Its result
Value points to that fragment. Name/Apply fragments keep their current rules
except that Apply fragments may now use a direct If child's fragment. An auxiliary
path contracts to the corresponding resolved Name reference; no result-to-
nested-result containment edge is introduced.

Group, Ascription, Lambda and Block remain the existing fragment boundaries.
This proposal does not silently make those constructors transparent. Their
definition-owner traversal is unchanged, including local-initializer ownership.
This is an additive construction for the explicitly named forms, not a claim
of complete source-global incidence or preservation for all expressions.

## Choice B: branches only

The conditional result includes references from every branch but excludes
condition-only references. Both choices also authorize Apply fragments to
traverse direct If children; this extension is part of either approval.
The same constructor and wrapper boundaries apply.
Thus `if p: f else: g` contributes `f` and `g` but not `p` for the result's
own adjacency. Definition-root references still include `p` in either choice.

These choices can change SCC membership when the condition refers back to a
definition involved in the result's extrusion. They therefore cannot be
selected by an implementation convenience or by the branch-join proof.

## Verification and scope

After the choice is reviewed and selected by the user, check source-generated
conditional callees and arguments, both constant conditions, nested If/elsif,
condition-only reference cycles, lexical/module identity, and existing wrapper
boundaries. Extend the helper-path projection proof to the selected constructor
edges; reuse the established activation theorem after that source premise.
Require linear retained fragments/edges in source incidences. Do not infer
global typing preservation, principality or hygiene from those checks.

Until the choice is selected, literal support and branch constraint generation
may proceed. Their reports must leave conditional-result SCC completeness
explicitly open; they must not label missing incidence as a proved absence.
