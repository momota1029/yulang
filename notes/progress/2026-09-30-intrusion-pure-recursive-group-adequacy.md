# Pure recursive-group generation adequacy

Date: 2026-09-30
Status: conditional proof for a narrow declarative fragment; not independently reviewed
Scope: pure `Var`/`Int`/`Lambda`/`Apply` expressions and one recursive SCC
Governing records: `2026-09-30-intrusion-pure-source-typing-rules.md`, `2026-09-30-intrusion-scc-constraint-scheme-rules.md`, and the SCC-intrusion redesign charter

## Declarative group rule

Fix a preorder carrier `D` with the Function subtyping law from the pure
source-typing rules. An outer environment `Γ` maps external names to fixed
values in `D`. For a statically resolved SCC `G={d₁=e₁,…,dₙ=eₙ}`, choose
monomorphic recursive assumptions `S_d∈D` and exposed member types `R_d∈D`.
The recursive names in every body resolve to the same `S_d` assignment. The
declarative rule is:

```text
for every d ∈ G:
  Γ[d ↦ S] ⊢ e_d : T_d     T_d ≤ S_d     T_d ≤ R_d
──────────────────────────────────────────────────────── RecGroup
Γ ⊢ rec G : { d ↦ R_d | d ∈ G }
```

The separate `S_d` and `R_d` values are deliberate. A recursive body must
produce a value usable at its monomorphic recursive assumption and at its
external member type. Both inequalities are obligations; the rule does not
identify the two endpoints or add an implicit recursive type equation. This
defines declarative typing for the research fragment; it is not yet a
preservation/progress theorem for an operational semantics.

## Generation relation

For each RHS `e_d`, generate `(t_d,C_d)` under one endpoint environment
`Ξ_G` that maps each recursive name `d` to a fresh endpoint `s_d` and maps
outer names to fixed anchors. Allocate distinct fresh endpoints for all
lambda parameters and application results. Add fresh `r_d` and form:

```text
C_G = ⋃ C_d ∪ { t_d ≤ s_d, t_d ≤ r_d | d ∈ G }
```

Let `A_G` be the outer anchor identities referenced by this graph. Let `L_G`
contain every identity freshly allocated for the SCC, including all `s_d`,
`r_d`, lambda parameters, and application results. Freshness gives
`A_G ∩ L_G = ∅`. For a fixed outer assignment `η : A_G → D`, write
`Sat_G(η,ν)` for satisfaction of all obligations in `C_G` by
`ν : L_G → D`.

### Adequacy theorem

For every fixed `η`, the following are equivalent:

1. there is a declarative recursive-group derivation under the outer
   environment interpreted by `η`, with recursive assumptions `S_d` and
   exposed member types `R_d`;
2. there is an assignment `ν : L_G → D` such that `Sat_G(η,ν)` and
   `S_d=eval(s_d,η,ν)`, `R_d=eval(r_d,η,ν)` for every `d`.

For `1⇒2`, apply the completeness direction of the monomorphic expression
generation theorem to each body under the fixed `S` assignment. It supplies
one extension for the body's generated endpoints with
`eval(t_d)≤T_d`. The declarative `T_d≤S_d` and `T_d≤R_d` obligations imply
the generated lower edges by transitivity. The bodies' generated endpoints
are pairwise fresh, so the extensions combine with the common `S` and `R`
assignments into one `ν`.

For `2⇒1`, apply the soundness direction of the expression generation theorem
to each satisfying `C_d`, obtaining
`Γ[d↦eval(s,η,ν)] ⊢ e_d : eval(t_d,η,ν)`. The two added inequalities are
exactly the premises needed to instantiate `RecGroup` with
`T_d=eval(t_d,η,ν)`, `S_d=eval(s_d,η,ν)`, and
`R_d=eval(r_d,η,ν)`.

Thus the candidate graph's member root relation is exactly the declarative
set of possible external member types:

```text
Root_G,d(η) = { eval(r_d,η,ν) | ν : L_G→D and Sat_G(η,ν) }
```

Upward closure adds precisely declarative subsumption at an external use.
The graph-scheme denotation is therefore sound and complete for this
declarative relation, not just a renaming-invariant approximation. This is a
root-principality theorem for the stated fragment and rule.

## Ownership partition for this fragment

This fragment has no post-boundary mutation, effect identities, or
member-specific fetch boundaries. Its exact ownership partition is therefore
simple:

```text
Local_d = Gen_d = L_G
Free_d = A_G
Cycle_d = ∅
Erase_d = ∅
```

Cycles in the graph are back-references to existing endpoint identities; they
do not allocate extra recursive binder identities. Every incoming use gets a
fresh bijection on all of `L_G`, fixes `A_G`, and receives the same `C_G` under
that renaming. The parent-transport fiber lemma then proves equality of the
root relation at each use. Different uses have disjoint fresh ranges and share
only the fixed outer assignment. There is no mixed local/free identity in
this subcase, so the cross-member anchor-coherence issue is discharged here
without assuming a rule for fetch-dependent boundaries.

The extra variables for other members are intentionally included in each
member view: their constraints certify that the whole recursive group is
well-typed, and existentially projecting them computes the selected member's
root relation. A member use does not reuse another member's internal
assumption; all group-local identities are freshly assigned in that use.

## Limits and next extension

This proof assumes the monomorphic expression-generation correspondence and
the Function subtype law. It does not establish that this declarative
recursive-group rule is the intended Yulang rule, prove operational soundness,
cover ordinary let-polymorphism or member-specific levels/fetches, model
effects/roles/diagnostics, or compare the final accepted program set with the
frozen Oracle. In particular, the previously proposed mixed
`Gen_d`/`Free_d` ownership case is not solved by this result; it is absent
from the fragment because every SCC-created endpoint is generalized and every
outer endpoint is fixed.

The next extension is nested let-polymorphism over an outer anchor environment.
It must derive the free-variable/generalization partition from a declarative
typing rule and establish how constraints crossing that boundary are retained.
Only after that should the model admit different member fetch boundaries and
test whether a component-wide `C_G` lens remains complete.
