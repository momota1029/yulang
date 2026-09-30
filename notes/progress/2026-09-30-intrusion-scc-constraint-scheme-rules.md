# Candidate recursive Function SCC constraint-scheme rules

Date: 2026-09-30
Status: candidate declarative rules; unreviewed; not implementation authority
Scope: recursive binding groups, graph generalization, and external use in the pure expression fragment
Governing sources: pure source typing rules; source-constraint semantics gate; intrusion sketch

## Recursive group generation

Assume an enclosing endpoint environment `Ξ₀` whose variables are fixed at
the current generalization boundary; external names are monomorphic endpoints
in this initial rule. Let `G = {d₁=λx̄.e₁,…,dₙ=λx̄.eₙ}` be one statically
resolved SCC of recursive Function definitions. The source model needs two
identities per member: a monomorphic self placeholder `s_d` used inside the
SCC, and an exposed member root `r_d` used by external callers. They are
distinct graph variables; do not silently alias them. Install only self
placeholders in the recursive generation environment:

```text
Ξ_G = Ξ₀ ∪ { d ↦ s_d | d ∈ G }
```

Generate each member body in this same environment with one shared fresh-name
supply, so variables allocated for different bodies remain distinct:

```text
Ξ_G ⊢ λx̄.e_d ⇓ (t_d, C_d)       for every d ∈ G
C_G = ⋃_{d∈G} C_d
      ∪ { t_d ≤ s_d | d ∈ G }
      ∪ { t_d ≤ r_d | d ∈ G }
```

`C_G` is the complete finite regular obligation graph for the SCC. Internal
references to `d` resolve to `s_d` directly; they are not scheme uses and are
not freshened. Both `s_d` and `r_d` belong to the SCC-owned set `L_G`, along
with every graph variable allocated while generating the group and its
lambda/application variables. `A_G` consists of fixed enclosing identities
referenced by `C_G`. Require `L_G ∩ A_G = ∅`. Recursive type behavior remains
a cycle of inequalities through the self placeholders; no equation
`s_d = e_d` or `r_d = e_d` is added.

The group is declaratively well-typed in fixed environment `η : A_G → D` iff
there is one joint assignment `ν_G : L_G → D` satisfying every obligation in
`C_G`. A type variable shared by two member bodies is assigned once by this
joint assignment. This relation describes the SCC before per-member views are
selected.

## Graph scheme and use

The generalized component is the graph object

```text
Component_G = (C_G, A_G, L_G, self_G = {d ↦ s_d}, roots_G = {d ↦ r_d})
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

## Worked source graph: `pub f x = x f`

The pure expression rules and the split self/export identities derive a
specific graph. Let `s` be f's internal self placeholder, `r` its exposed
root, `q` the parameter type, and `v` the application result. The body `x f`
generates `q ≤ Fun(s,v)`; wrapping the body as a Function and adding the two
definition-boundary obligations gives:

```text
q ≤ Fun(s,v)
Fun(q,v) ≤ s
Fun(q,v) ≤ r
```

This corresponds to the exact pure value shapes in the Oracle source trace:
the application upper from `x f`, the replay-derived recursive lower on
`TypeVar(1)`, and the selected lower at the exported `TypeVar(0)` root. The
Oracle trace includes effect and subtraction coordinates and additional
intermediate variables; these are the declarative pure-value constraints, not
a claim that the full Oracle graph consists only of these three edges. The
source identity and provenance evidence is recorded in
`notes/progress/2026-09-30-intrusion-source-identity-map.md` and
`notes/progress/2026-09-30-intrusion-q-finite-bound-cycle-trace.md`.

The candidate graph is satisfiable in the tagged powerset carrier: choose
`q=Bottom`, `v=Bottom`, and `s=r=Top`. The first edge holds because Bottom is
least; both Function lower bounds hold because Top is greatest. Thus retaining
the recursive constraint does not make the SCC empty.

Now consider an external use `f 1`. Application generation adds a fresh `w`
and the constraint `r ≤ Fun(Int,w)`. The exported lower edge implies
`Fun(q,v) ≤ Fun(Int,w)`, hence `Int ≤ q` by Function contravariance. But the
body edge gives `q ≤ Fun(s,v)`, so transitivity requires `Int ≤ Fun(s,v)`.
That is impossible in the candidate carrier because integer and Function
heads have disjoint tags. Therefore every result choice for `f 1` has an empty
constraint fiber. This matches the already observed final Oracle
specialization rejection of the concrete `int -> unit` instance; any earlier
intrusion rejection changes only the phase for this invalid use.

The derivation is conditional on the three-edge source rule and tagged
powerset separation of Int and Function. It does not establish the correct
scheme relation for all roots or the full source-to-Oracle bridge, but it
replaces the earlier candidate's conflation of the recursive self identity
with the exported root.

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

Review the two-identity source rule against all admitted definition forms and
prove its correspondence to the declarative typing judgment, including
multi-member SCCs. Then add ordinary non-recursive polymorphic bindings and
prove that shared outer identities compose with this SCC semantics. Only then
add Yulang latent effects and compare final accepted programs against the
frozen Oracle.
