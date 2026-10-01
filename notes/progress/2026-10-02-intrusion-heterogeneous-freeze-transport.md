# Heterogeneous pure-saturation freeze transport

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: reviewed conditional theorem; not implementation authority
Implementation authority: none

## Claim

This note closes a composition gap between three existing conditional results:

1. pure finite bound-graph saturation preserves the complete assignment fiber;
2. injective parent transport preserves a fixed component's constraint fiber;
3. the recursive-group/let source relation retains one coupled continuation
   with all use copies and cross-use obligations.

The additional case is that member roots may be saved at different finite
saturation stages. This happens without changing any semantic rule or adding
a new selector. A saved stage is valid only after source collection for the
component is complete.

## Definitions and assumptions

Use the pure finite saturation state from
[`2026-09-29-intrusion-abstract-semantics-draft.md`](../design/2026-09-29-intrusion-abstract-semantics-draft.md),
`S=(Q,L,U,X)`. Define its complete constraint encoding as

```text
Enc(S) = Q
       ∪ { p ≤ v | p ∈ L(v) }
       ∪ { v ≤ n | n ∈ U(v) }.
```

`X ≠ ∅` denotes an empty satisfying fiber; it is not an ignored successful
residual. The endpoint carrier and interpretation satisfy the conditional
preservation axioms stated in the abstract-semantics draft: every saturation
insertion is equivalent to the conjunction it extends, including structural
decomposition and mismatch classification.

Let the **complete** collected source component be

```text
C_G = (A_G, L_G, Roots_G, Constraints_G)
```

with fixed anchor identities `A_G`, component-local identities `L_G`, and
member roots `r_d`. Let `S₀` encode `Constraints_G`, and only then run the
monotone pure saturation operator `F`. A saved view may use any reachable
finite stage `S_k = F^k(S₀)`. Distinct member roots and incoming-use views may
choose distinct stages. No later independent source constraint may be omitted
from one of these views.

Saturation changes only the constraint encoding: member root endpoints and
their selected source identities remain fixed at every stage. This premise is
needed for the root-observation equality after assignment reindexing.

For a fixed anchor assignment `η` and local assignment `ν`, write
`Sat(C_G,η,ν)` for satisfaction of the complete collected source conjunction.
The saturation carrier lemma gives:

```text
Sat(C_G,η,ν) iff Sat(Enc(S_k),η,ν)
```

for every finite `k`, including stages with already-derived mismatch evidence.
This is pointwise equality of the whole local solution fiber, not merely
equality of projected root bounds.

## Heterogeneous snapshot composition

Let `C_G^base` be the component-validity copy, `C_G^u` a distinct copy for
each incoming use `u`, and `C_e` every continuation constraint, including
caller obligations and any constraint coupling multiple use roots. The full
joint relation is

```text
J = C_G^base ∪ (⋃u C_G^u) ∪ C_e.
```

Choose an arbitrary reachable snapshot `S_{k_0}` for the base copy and
`S_{k_u}` for each use copy. Replace each copy by the image of its complete
encoding under that copy's already-fixed component-copy map. The map carries
each member root to the same copy-local root identity referenced by `C_e`;
the snapshot replacement itself leaves `C_e` unchanged. Call the result
`J_snap`. Let `A_J` be the fixed outer identities and `K` the continuation's
generated identities excluding every base/use-copy local identity. The fixed
context is exactly `F=A_J∪K`; the base locals and each use-local set `L_u` are
pairwise disjoint and disjoint from `F`. `C_e` may reference any of those
locals, including use roots. For every assignment `ζ` to `F` and assignment
`ν` to all base/use locals:

```text
Sat(J,ζ,ν) iff Sat(J_snap,ζ,ν).
```

Proof: each base/use component is pointwise equivalent to its own complete
constraint conjunction at the same assignment, even when its snapshot stage
differs from the stages chosen for other copies. Replacing finitely many
conjuncts by equivalent conjunctions preserves their conjunction with the
arbitrary fixed `C_e`. No independence between uses is assumed; all
cross-use constraints stay in `C_e`.

Now let `Λ` be the disjoint union of the component-local parent/use maps,
fixing exactly `F` and mapping every base/use local—including roots referenced
from `C_e`—to a disjoint fresh local/parent identity outside `F`. Assume each
local map is a bijection and finite endpoint interpretation is compositional.
Apply `Λ` to the complete conjunction, including the local references inside
`C_e`; do not fix those references merely because the constraints mention
them. Structural induction gives

```text
Sat(J_snap,ζ,ν) iff Sat(Λ(J_snap),ζ,ν^Λ)
eval(t_e,ζ,ν) = eval(Λ(t_e),ζ,ν^Λ)
```

where every root and every caller/cross-use constraint uses this same `Λ`.
Because the combined local map is bijective from the full base/use-local
domain to its target domain, existential projection preserves
the complete joint root/use observation relation, including empty fibers.
Applying the same declared subsumption afterward preserves the same `Pred`
relation. Different snapshot times therefore do not affect this conditional
pure transport result.

## Source-collection boundary

Saturation timing and source-constraint collection are distinct. The theorem
does not license freezing a component before its source constraints are
complete. For example, let the early graph contain `Int ≤ x`, and let later
source collection add `x ≤ Bottom`, with `Int ≰ Bottom`. The early view admits
`x=Int`; the complete graph has an empty fiber. Parent renaming and fresh use
copies preserve the early graph's incorrect acceptance. The later obligation
is not a saturation consequence of `Int ≤ x`.

Therefore the precondition is either (a) complete source collection before
the first snapshot, or (b) an explicit proof that every later-added source
constraint is entailed by every already-published view. The present theorem
uses (a).

## Limits

This closes only heterogeneous **pure saturation snapshots** inside the
existing conditional graph model. It does not prove that source collection
constructs the right `C_G`, that the endpoint carrier matches the Yulang
Oracle, that the solver finds every feasible polarized assignment, or that a
principal finite scheme exists. It does not cover effects, methods, roles,
diagnostics, publication atomicity, or runtime behavior. No compiler code or
tests changed; user approval and successor-design review remain prerequisites
for implementation.

Proof producer: `compiler_referee`, read-only analysis of the existing graph,
source-composition and parent-transport definitions. Independent specification
audit closed the domain-definition repair with no remaining findings. Review
scope was the saturation mismatch, complete-source boundary, heterogeneous
snapshots, fixed/shared identity domains, coupled continuation transport, and
assignment-fiber projections. It does not certify source adequacy, the
carrier, solver completeness, principality, or Oracle final acceptance. The
producer's analysis is not treated as self-certification.
