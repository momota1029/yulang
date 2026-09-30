# Parent transport for a pure recursive component

Date: 2026-09-30
Status: reviewed conditional theorem; not implementation authority
Scope: parent renaming of a source-adequate pure recursive component and its per-use views
Governing records: `2026-09-30-intrusion-parent-transport-fiber-lemma.md`, `2026-09-30-intrusion-recgroup-let-composition.md`, `2026-09-30-intrusion-final-acceptance-contract.md`

## Setup

Let the recursive-group-plus-nested-let generator produce a component
`G=(C_G,A_G,L_G,{s_d},{r_d})`, with all SCC-created identities in `L_G`,
fixed outer anchors `A_G`, and roots `r_d`. Assume the conditional adequacy
theorem in the composition note: for every fixed anchor assignment `η`, the
member root relation of `C_G` equals the source-defined
`MemberTypes_G,d(Γ,η)`. This premise is available only for related outer
environments `Ξ≈_ηΓ`, and under the composition theorem's global freshness
conditions: group-local ranges are pairwise disjoint and disjoint from outer
anchors, and each nested-let lookup receives a fresh local range. `C_G` is a
finite regular conjunction of source subtype constraints; cycles are identity
back-references, not equations.

Allocate a fresh boundary parent `p_v` for every `v∈L_G`, with all parents
pairwise distinct and outside `A_G`. Define the injective map
`π:A_G∪L_G→A_G∪P_G` by fixing anchors and mapping `v↦p_v`. The intruded view
is the pointwise image:

```text
I(G) = (π(C_G), A_G, P_G, {π(s_d)}, {π(r_d)})
```

No constraint is dropped, approximated, or merged. In particular, the
application upper involving `q` in `f x = x f` transports to
`p_q ≤ Fun(p_s,p_v)`. This is a candidate parent-preserving operation, not
the Oracle's polarity erasure or a claim that ordinary Simple-sub extrusion
uses this operation.

## Parent-fiber theorem

For a fixed `η:A_G→D` and an assignment `ν:L_G→D`, define the unique parent
assignment `ν^π:P_G→D` by `ν^π(p_v)=ν(v)`. For every endpoint `e` over
`A_G∪L_G`, structural induction gives:

```text
eval(e,η,ν) = eval(π(e),η,ν^π)
```

Thus each source obligation has the same truth value before and after
transport, and:

```text
Sat(C_G,η,ν) iff Sat(π(C_G),η,ν^π)
```

The assignment map is bijective because `π` is bijective from `L_G` onto
`P_G`. Existential projection therefore gives, for every member root `d`,

```text
Root_G,d(η) = Root_I(G),d(η)
Pred_G,d(η) = Pred_I(G),d(η)
```

where `Pred` includes the same declared upward subsumption. By the assumed
group adequacy theorem, `Pred_I(G),d(η)` is exactly the source member relation
`MemberTypes_G,d(Γ,η)` with subsumption. The equality holds independently for
every fixed `η`, including empty solution fibers; it does not select a
favorable outer assignment.

For one incoming use `u`, choose a fresh bijection `σ_u:P_G→F_u` and compose
`ρ_u=σ_u∘π` on local identities, fixing anchors. The parent-transport fiber
lemma gives the same equalities for this member-view fiber. To state the
whole continuation relation, let `A_J` contain every fixed outer identity
referenced by the group or continuation, and let `K` be the continuation's
generated identities other than identities owned by member-use copies,
including caller result/argument endpoints. `A_G⊆A_J`; write `C_e` for all
continuation constraints after each lookup has selected its distinct graph
copy. Thus `C_e` contains every obligation that connects a use root to its
caller and every obligation coupling two or more uses. The complete generated
relation is:

```text
J = C_G^base ∪ (⋃_{u∈Uses(e)} C_G^u) ∪ C_e
```

Here `C_G^base` is the one group-validity copy; each `C_G^u` is a distinct
per-use copy of `C_G`, and `C_e` refers to each use's root in that copy. Any
additional source-required cross-use obligation belongs in `C_e` and is
retained there. Base locals and all use locals have pairwise disjoint ranges;
only the fixed outer identities `A_J` and continuation identities `K` are
shared. For the base copy choose `π₀:L₀→P₀`; for each use copy choose
`πᵤ:Lᵤ→Pᵤ`. All parent sets are pairwise disjoint and outside `A_J∪K`.
Extend them to one map `Λ` that fixes `A_J∪K` and is the disjoint union of
`π₀` and all `πᵤ`. Every obligation in `J`, including caller and cross-use
constraints, is transported by this same `Λ`. For each fixed assignment
`ζ` to `A_J∪K` whose restriction to `A_G` is the member's `η`, pointwise
evaluation commutes with `Λ`, so:

```text
Sat(J,ζ,ν) iff Sat(Λ(J),ζ,ν^Λ)
eval(t_e,ζ,ν) = eval(Λ(t_e),ζ,ν^Λ)
```

The map on the complete local domain `L₀ ⊔ (⊔ᵤ Lᵤ)` is bijective. Thus
existential projection preserves the full joint root/use relation for each
fixed shared context, including empty fibers. It factors into independent use
fibers only when `C_e` couples uses solely through the fixed shared context.

Because each component map is injective, references to each live recursive
self placeholder remain references to one shared parent vertex within the
base SCC copy. The SCC's identity-reference topology is isomorphic. This
preserves the generator's boundary rule: names in recursive bodies resolve to
`Mono(s_d)` and retain their live intra-SCC references, while only
continuation lookups use `Poly(S_d^G)` and receive distinct fresh parent
copies. No SCC edge is unfolded or converted into an independent use. All
external uses receive disjoint copies of the parent set, while `A_J` and the
continuation context `K` remain shared.

## Why injectivity is required

If two distinct locals are mapped to one parent, the assignment correspondence
fails whenever the endpoint language has an injectively interpreted binary
constructor `Pair`. In a carrier containing distinct values `a≠b`, take two
unconstrained locals `x,y` and expose the endpoint `Pair(x,y)`. Before a
non-injective map, its root relation contains `Pair(a,b)`; after identifying
both locals with one parent, only diagonal values `Pair(c,c)` are
representable. Thus a many-to-one parent map can lose source instances and is
not justified as sharing preservation. This example is a generic map
counterexample; it is not a claim that the current pure source syntax contains
`Pair`.

## Limits

This theorem composes source-graph adequacy with an exact parent renaming for
the stated pure custom declarative system. It does not prove that the frozen
Oracle's edge selection, ordered root preparation, effects, roles, handler
hygiene, diagnostics, or runtime checks are represented by `C_G`; those
extensions are required for the full Oracle-capability objective. It also
does not establish an implementation complexity bound or authorize compiler
changes. The source-graph theorem and parent-fiber lemma remain conditional
premises and the final-acceptance contract is still a candidate.

## Review record

On 2026-09-30, compiler-referee and spec-auditor M3 review identified the
missing related outer-environment/freshness premises and an incomplete joint
use relation. The primary added those premises, included the base validity
copy, every fresh member-use graph, all caller and cross-use constraints, and
a single injective renaming over their combined identity domain. Follow-up
review confirmed the fixed outer domain `A_J`, shared continuation context
`K`, and empty-fiber/root equality. The review did not assess the conditional
source-group adequacy premise, effects, roles, diagnostics, full Oracle
acceptance, implementation, or complexity.
