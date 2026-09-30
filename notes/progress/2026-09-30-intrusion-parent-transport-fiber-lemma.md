# Intrusion parent transport preserves finite constraint fibers

Date: 2026-09-30
Status: conditional lemma; primary derivation; not independently reviewed
Scope: renaming/parent transport after a selected finite constraint graph is fixed
Governing sources: intrusion abstract-semantics draft §§3–5; Simple-sub audit; q-bound successor draft

## Statement

Let a finite regular endpoint graph use a carrier `D` with a preorder `≤`.
Endpoint evaluation looks up a variable's assigned `D` value directly; it
does not unfold graph back-edges. Let the graph's identity set be split into
preserved anchors `A` and member-local identities `L`, with `A ∩ L = ∅`.
Let `C` be the complete selected conjunction of subtype obligations for this
view, and let `root` be its exposed endpoint. Extra use constraints are
allowed, provided they are included in `C` or in a context relation that is
renamed by the same map.

Choose a port set `P` disjoint from `A` and a bijection `φ : L ↔ P`.
Rename every endpoint and every obligation in `C` by the identity on `A` and
`φ` on `L`, obtaining `φ(C)`. For an incoming use `u`, choose a fresh set
`F_u` disjoint from `A` and from every other use's fresh set, and a bijection
`σ_u : P ↔ F_u`. Define `ρ_u` to fix `A` and map each `v ∈ L` to
`σ_u(φ(v))`; thus `ρ_u : L ↔ F_u` is a bijection.

For every fixed anchor environment `η : A → D`, every local assignment
`ν : L → D` has a unique renamed assignment `ν_u : F_u → D` satisfying
`ν_u(ρ_u(v)) = ν(v)` for all `v ∈ L`. Then:

```text
Sat(C, η, ν)  iff  Sat(ρ_u(C), η, ν_u)
eval(root, η, ν) = eval(ρ_u(root), η, ν_u)
```

The correspondence is bijective. Consequently the set of realized root
values is unchanged by parent transport and per-use freshening. If scheme
instantiation exposes exactly `ρ_u(C)` and applies ordinary upward subsumption,
its denotation is exactly the graph's `Pred` relation
`{T | ∃t. Sat(C,η,_) ∧ eval(root,η,_) = t ∧ t ≤ T}`. This conclusion needs
no least solution for the entire variable tuple and does not turn recursive
inequality cycles into equations.

For a finite family of uses, the same result holds for the joint relation
when all local identities across all uses are renamed by one injective map
into a disjoint union of fresh sets, all shared anchors use one common `η`,
and every cross-use obligation is retained and renamed. If the source relation
has no cross-use constraints except through anchors, the joint local solution
fiber is the product of the per-use fibers. Otherwise the joint conjunction,
not a product of separately projected marginals, is preserved.

## Proof

Structural induction on endpoint syntax proves evaluation commutes with
`ρ_u`: constants are unchanged; each variable is assigned the corresponding
value by construction; each constructor applies the same interpretation to
equal child values. The argument also applies to finite regular graphs because
back-edges are variable lookups and no coinductive unfolding occurs.

For every source obligation `s <: t`, evaluation commutation gives the same
two values on both sides, so its preorder judgment has the same truth value.
Conjunction over the exact same obligation set proves the `Sat` equivalence.
The inverse assignment is defined by `ν(v) = ν_u(ρ_u(v))`; the bijection
between `L` and `F_u` makes it a two-sided inverse. Applying the same
evaluation lemma to `root` proves equality of root values. Existentially
projecting this bijection gives equality of root sets, and then equality of
their upward closures by the unchanged preorder.

For several uses, apply the same proof to the disjoint union of their local
identity sets and the single joint obligation conjunction. Shared anchors
remain fixed, and every joint obligation is transported by the same map.
Product factorization follows only when that conjunction factors by use after
fixing the shared anchors.

## What this closes and what it does not

This proves the transport step of intrusion once the selected graph, its full
identity partition, and all root/use obligations are already correct. It
applies to any carrier whose endpoint evaluation is syntax-directed and whose
constraints are subtype obligations; the powerset candidate is one possible
instance. The proof is independent of polarity and therefore does not identify
positive and negative Simple-sub extrusion representatives.

The lemma does **not** prove that Oracle root preparation selects `C`, that
the parent map preserves every source constraint while producing `C`, that
the `A`/`L` partition is correct for SCC members, or that any finite scheme
representation exposes exactly this graph. It also does not prove the
candidate carrier models Yulang types/effects, source lowering is adequate,
the Oracle final pipeline accepts exactly the declaratively well-typed
programs, or handler hygiene is preserved. Those remain separate gates.
