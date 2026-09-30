# Candidate SCC constraint-scheme rules for the pure source fragment

Date: 2026-09-30
Status: candidate declarative rules; unreviewed; not implementation authority
Scope: recursive binding groups, graph generalization, and external use in the pure expression fragment
Governing sources: pure source typing rules; source-constraint semantics gate; intrusion sketch

## Recursive group generation

Assume an enclosing endpoint environment `Ξ₀` whose variables are fixed at the
current generalization boundary; external names are monomorphic endpoints in
this initial rule. Let `G = {d₁=e₁,…,dₙ=eₙ}` be one statically resolved
recursive definition SCC. Allocate one fresh member root `r_d` for each
definition, and place all member roots in the recursive generation
environment:

```text
Ξ_G = Ξ₀ ∪ { d ↦ r_d | d ∈ G }
```

Generate each member body in this same environment with one shared fresh-name
supply, so variables allocated for different bodies remain distinct:

```text
Ξ_G ⊢ e_d ⇓ (t_d, C_d)       for every d ∈ G
C_G = ⋃_{d∈G} C_d ∪ { t_d ≤ r_d | d ∈ G }
```

`C_G` is the complete finite regular obligation graph for the SCC. Internal
references to `d` resolve to `r_d` directly; they are not scheme uses and are
not freshened. `L_G` consists of every graph variable allocated while
generating the group above the boundary, including member roots and all
lambda/application variables. `A_G` consists of the fixed enclosing
identities referenced by `C_G`. Require `L_G ∩ A_G = ∅`. Recursive type
behavior remains a cycle of inequalities through the `r_d` variables; no
equation `r_d = e_d` is added.

The group is declaratively well-typed in fixed environment `η : A_G → D` iff
there is one joint assignment `ν_G : L_G → D` satisfying every obligation in
`C_G`. A type variable shared by two member bodies is assigned once by this
joint assignment. This relation describes the SCC before per-member views are
selected.

## Graph scheme and use

The generalized component is the graph object

```text
Component_G = (C_G, A_G, L_G, roots_G = {d ↦ r_d})
```

It is immutable after construction. For each external incoming use `u` of
member `d`, choose a fresh identity set `F_u` and a bijection
`ρ_u : L_G ↔ F_u`, extended by identity on `A_G`; distinct uses have disjoint
fresh ranges. The use receives root `ρ_u(r_d)` and the entire obligation
graph `ρ_u(C_G)`.
Thus a use of one member retains the same SCC constraints and recursive
sharing as every other member view, while independent incoming uses do not
share their component-local assignments. Enclosing identities remain shared
through one fixed `η`.

For fixed `η`, define the member relation:

```text
Root_G,d(η) = {
  eval(r_d,η,ν) | ν : L_G→D and Sat(C_G,η,ν)
}
Pred_G,d(η) = { T | ∃t∈Root_G,d(η). t ≤ T }
```

The denotation of `Component_G` at a use of `d` is, by definition, the set of
all `T` in `Pred_G,d(η)`. It is a principal graph scheme for this relation:
every satisfying local assignment yields an instance root, every instance
root comes from such an assignment, and ordinary subsumption contributes
exactly the upward closure. No least assignment to all of `L_G` is required.
An empty solution fiber yields an empty relation; it is not repaired by
discarding an obligation.

For a finite family of incoming uses, each use receives its own `ν_u` over its
disjoint `F_u`, while all uses share the same anchor environment `η`. Their
joint acceptance condition is one conjunction of every renamed member graph
and every caller-use constraint. It factors into independent local fibers only
when the caller constraints communicate solely through anchors. Otherwise
retain the full joint relation; do not multiply separately projected root
marginals.

## Correctness argument, conditional on source generation

The group-generation relation uses one shared environment `Ξ_G`, so every
internal reference and every source-generated cross-member inequality appears
once in `C_G` with its intended shared endpoint identities. External use
instantiation replaces exactly `L_G` by a disjoint fresh set and fixes `A_G`.
The parent-transport fiber lemma then gives a bijection between satisfying
assignments to the source group graph and assignments to each renamed use
graph, preserving the exposed root value. For multiple uses it applies to the
joint renamed conjunction. Therefore the graph scheme preserves the source
constraint assignment relation and its member root projections.

This is a candidate principality result relative to the declarative graph
semantics, not a proof that the generated graph captures Yulang typing. It
assumes that each body's constraint-generation rule is sound/complete, the SCC
membership partition is correct, all cross-member constraints are retained,
and the `A_G`/`L_G` ownership split matches lexical generalization boundaries.
Those premises remain unproved. The construction also has no latent effects,
handlers, rows, roles, diagnostics, failure scheduling, or runtime entrypoint
semantics, and it does not prove final acceptance equivalence with the Oracle.

## Why this is not ordinary Simple-sub extrusion

This candidate stores an immutable component constraint graph and defines
instantiation by a bijective renaming of its owned identities. It is a
constraint-scheme semantics. It does not claim to simulate the paper's
polarity-sensitive source-side bound insertion or its two representatives
`(variable, polarity)`. Any optimization that replaces this graph with fewer
ports or projected member views requires a separate preservation proof under
`Root_G,d` / `Pred_G,d`; a one-polarity variable with a meaningful bound stays
in the graph under the user's current decision.

## Next proof step

Extend expression generation with binder ownership and the group rule above,
then verify the exact `x f` application bound and its recursive self edges in
the generated component. After that, add ordinary non-recursive polymorphic
bindings and test whether the shared-outer-identity rule composes with this SCC
semantics. Only then add Yulang latent effects and compare final accepted
programs against the frozen Oracle.
