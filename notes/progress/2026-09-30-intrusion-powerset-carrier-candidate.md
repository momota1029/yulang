# Powerset carrier candidate for pure intrusion semantics

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: unselected semantic candidate; no implementation authority

## Candidate

An architecture analysis proposed interpreting graph variables in
`D = P(N)`, ordered by subset. Set union/intersection interpret type union and
intersection; `Bottom = ∅` and `Top = N`. `N` is a countable tagged encoding
universe with a distinct constructor tag and disjoint coordinate channels for
each constructor argument and variance direction.

- A nullary atom denotes its unique tag.
- A covariant argument channel contains the encoded argument set.
- A contravariant channel contains its complement in `N`.
- An invariant argument uses both the covariant and complement channels.
- A Function uses a complement channel for its argument and a covariant
  channel for its result.

With disjoint channels, inclusion between same-head Function encodings is
equivalent to contravariant argument inclusion and covariant result inclusion.
For an invariant nominal argument it is equivalent to equality of the encoded
argument sets. Distinct head tags make irreducible constructor mismatches
non-inclusions. This gives a concrete candidate for the pure saturation
axioms; the encoding and each axiom still need a written proof and independent
review.

The carrier distinguishes an interval from an equation. The one-sided
`Bottom ≤ q ≤ Fun(Int, q)` has the assignment `q = ∅`; it does not force a
recursive equation. The two-sided matching interval
`Fun(Int, q) ≤ q ≤ Fun(Int, q)` asks for a fixed point of the result-positive
map `q ↦ Fun(Int, q)`. That map is monotone on the complete lattice `P(N)`, so
Tarski gives a fixed point for this specific interval. This does not prove
existence for every recursive or polarity-reversing graph.

## Selector fixture

The `ints` endpoint graph admits `p = a = u = r = {tag_int}`; its inequalities
force `tag_int ≤ r`, so this is the least root value for the captured endpoint
subgraph. The `mixed` graph has the corresponding Bool assignment. The Rust
endpoint trace connects the constants in the producer payload lower bounds to
the selector result roots through the invariant first argument of the
same-head `step` comparison.

This does not show that the complete recursive-use graph has a satisfying
assignment. Its separate `step <: int` events have an
`UnknownInternal(OriginId(1))` path in the exact OCast classifier explanation.
The carrier's subtype fiber and the Oracle's incomplete-provenance/diagnostic
judgment must remain separate until their relation is specified.

## Required next work

1. Define the tagged universe and constructor encodings without relying on
   informal “disjoint channel” shorthand; prove every pure saturation axiom.
2. Search for a polarity-reversing guarded interval whose assignment fiber has
   no least element, or prove a principality theorem for the claimed graph
   class.
3. Define environment-indexed scheme instantiation over the assignment
   relation, including fresh local identities and fixed outer anchors.
4. Relate the selected root/epoch snapshots and the separate incomplete OCast
   outcome to public Oracle observations.
5. Obtain independent compiler-semantic and specification review before Gate
   D. This candidate is not a selected carrier or implementation instruction.

No compiler code or permanent test changed. The supporting evidence came from
focused Rust probes in the detached Oracle worktree; no Python or performance
measurement was used.
