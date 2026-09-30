# Candidate recursive Function SCC constraint-scheme rules

Date: 2026-09-30
Status: candidate declarative rules; unreviewed; not implementation authority
Scope: recursive binding groups, graph generalization, and external use in the pure expression fragment
Governing sources: pure source typing rules; source-constraint semantics gate; intrusion sketch; `notes/progress/2026-09-29-intrusion-oracle-ledger.md`

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

The SCC is the monomorphic recursive region, not one polymorphic binder
scope. Each member has its own generalization boundary `b_d`, determined by
that member's binding fetch. The candidate member view is a root lens over the
whole source graph, not an edge-pruned copy:

```text
H_d = (C_G, root = r_d, b_d, Gen_d, Free_d, Cycle_d, Erase_d)
```

`Gen_d` contains graph identities above `b_d`; `Cycle_d` contains recursive
identities that must freshen with this view; `Local_d = Gen_d ∪ Cycle_d`.
`Free_d` contains all other surviving graph identities and resolves through a
stable environment map. For this constraint-retaining candidate,
`Erase_d = ∅`: no source edge or recursive row is removed during view
construction. A source identity may be local in one member view and free in
another because the member boundaries differ. The same raw `C_G` constraints,
including edges through other SCC members, remain available to each root lens;
each lens selects a different root and binder partition. The map and root
selection are member-specific, while constraint identity and sharing stay
component-wide.

A single component-wide quantification set is not justified: the Oracle
generalizes each member separately and fetch kinds can use different
boundaries. The frozen-source evidence is summarized in
`notes/progress/2026-09-29-intrusion-oracle-ledger.md`:
`generalize_boundary` is selected per definition, and `quantify_component`
invokes root generalization separately for each member. This candidate keeps
that member specificity without requiring Oracle's inference-stage edge
selection or polarity erasure.

## Graph scheme and use

The generalized component retains the source graph and member-specific root
lenses:

```text
Component_G = (C_G, A_G, L_G, self_G, roots_G, {H_d | d ∈ G})
```

`C_G` is immutable after the SCC closes. For an external incoming use `u` of
member `d`, freshen exactly `Local_d = Gen_d ∪ Cycle_d` with an injective map
`ρ_(d,u) : Local_d → Fresh_(d,u)`, and fix every surviving `Free_d` identity
through the shared environment map `E_d`, which is injective on distinct
surviving source identities. All distinct incoming uses, including uses of
different members, have pairwise disjoint fresh ranges; each member uses its
own `b_d` and partition. The use receives `ρ_(d,u)(r_d)` when `r_d` is local,
or `E_d(r_d)` when it is a preserved free identity, together with `C_G` under
that renaming. This keeps open-SCC recursion monomorphic, gives each external
use an independent member-local instance, and retains intended outer sharing.
The constraint graph is shared as the component authority; use overlays apply
the member-specific identity map rather than one component-wide quantification
plan.

For fixed member environment `η_d : E_d(Free_d) → D`, define the member
relation by assigning all local variables in the shared source graph:

```text
Root_G,d(η_d) = {
  eval(r_d,η_d,ν) | ν : Local_d→D and Sat(C_G,η_d,ν)
}
Pred_G,d(η_d) = { T | ∃t∈Root_G,d(η_d). t ≤ T }
```

The denotation of the root lens `H_d` at a use of `d` is, by definition, the set of all `T`
in `Pred_G,d(η_d)`. It is a principal graph scheme for this relation: every
satisfying member-local assignment yields an instance root, every instance
root comes from such an assignment, and ordinary subsumption contributes
exactly the upward closure. No least assignment to all of `Local_d` is
required. An empty solution fiber yields an empty relation; it is not repaired
by discarding an obligation.

For a finite family of incoming uses, each use receives its own `ν_u` over its
member-specific disjoint fresh range, while all uses share the same resolved
free anchors. Their joint acceptance condition is the conjunction of each
renamed `H_d` view and each caller-use constraint. It factors into independent
local fibers only when the views and caller constraints communicate solely
through anchors. Otherwise retain the full joint relation; do not multiply
separately projected root marginals.

## Correctness argument, conditional on source generation

The group-generation relation uses one shared environment `Ξ_G`, so every
internal reference and every source-generated cross-member inequality appears
once in `C_G` with its intended shared endpoint identities. Each `H_d` is a
root lens over this complete graph: `Local_d` assignments are existentially
projected while the member's `Free_d` anchors are fixed. There is no
edge-deletion operation in this candidate. The proof obligations are source
generation adequacy, correct `b_d`/partition ownership, and that this
existential root projection matches the declarative member/use relation. Given
those premises, the parent-transport fiber lemma gives a bijection between
assignments to `C_G` and each renamed use overlay, preserving the exposed root
value. For multiple uses it applies to the joint renamed views with one shared
anchor environment. Transport does not establish source generation or the
typing meaning of the root projection.

This is a candidate principality result relative to the declarative graph
semantics, not a proof that the generated graph captures Yulang typing. It
assumes that each body's constraint-generation rule is sound/complete, the SCC
membership partition is correct, the root projection of the complete source
graph is the language's member typing relation, and every
`b_d`/`Gen_d`/`Free_d`/`Cycle_d` partition matches that member's lexical
generalization boundary.
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

If `H_f` retains the meaningful value constraints above, consider an external
use `f 1`. Application generation adds a fresh `w` and the constraint
`r ≤ Fun(Int,w)`. The exported lower edge implies
`Fun(q,v) ≤ Fun(Int,w)`, hence `Int ≤ q` by Function contravariance. But the
body edge gives `q ≤ Fun(s,v)`, so transitivity requires `Int ≤ Fun(s,v)`.
That is impossible in the candidate carrier because integer and Function
heads have disjoint tags. Therefore every result choice for `f 1` has an empty
constraint fiber. This matches the already observed final Oracle
specialization rejection of the concrete `int -> unit` instance; any earlier
intrusion rejection changes only the phase for this invalid use.

The derivation is conditional on the three-edge source rule, the `H_f` root
lens retaining the complete source graph, and tagged
powerset separation of Int and Function. It does not establish the correct
member root relation for all roots or the full source-to-Oracle bridge, but it
replaces the earlier candidate's conflation of the recursive self identity
with the exported root.

## Two-member sharing witness

For `f x = g x; g y = f y`, let `s_f` and `s_g` be the open-SCC self
placeholders; let `r_f` and `r_g` be the exported roots. Let `a,b` be the
argument types and `u,v` the application results. The candidate source rules
generate:

```text
a ≤ Fun(s_g,u)       Fun(a,u) ≤ s_f       Fun(a,u) ≤ r_f
b ≤ Fun(s_f,v)       Fun(b,v) ≤ s_g       Fun(b,v) ≤ r_g
```

The first member's use of `g` points to the same live `s_g` that the second
member's body constrains; it is not a separately instantiated scheme. The
group graph is nonempty in the tagged powerset carrier by assigning
`a=b=u=v=Bottom` and `s_f=s_g=r_f=r_g=Top`.

After the SCC closes, `H_f` and `H_g` are separate root views with their own
member-specific boundaries. A use of `f` freshens `Local_f` through its map;
a use of `g` freshens `Local_g` through its map. Shared outer anchors remain
common. If a source identity is generalized in both views, the two member
maps still produce distinct use identities; if it is free in a view, that
view preserves its environment mapping. The views may include constraints
induced through the other member, so their exact projection is still a proof
obligation. The Oracle ledger observes an unproductive pure Function mutual
cycle, but this simple two-line source is a declarative witness, not a claim
that its finalized scheme strings match that Oracle fixture.

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
