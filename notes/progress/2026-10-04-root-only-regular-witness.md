# Root-only regular-witness theorem (2026-10-04)

Status: independently reviewed bounded theorem; progress evidence only. This
does not change a language rule, the status of a governing design, or the
compiler implementation gate.

## Result and scope

After a fixed equality quotient, unguarded structural satisfiability has a
regular witness whenever every endpoint is either a descriptor-free class
appearing only as an original inequality root or a closed contractive regular
descriptor graph, over identity atoms, mandatory finite Records, and ordinary
structural Functions. Free-class aliases share one track. Any finite joint set
of original inequalities among these tracks is allowed. Effects, optional
Records, casts/adapters, permissions, guards, `Phi/K,D`, identity-sensitive
graph constraints, and source acceptance are outside the result.

The result strengthens the existing closed-endpoint interval results to
several mutually constrained free roots. It decides existence in this bounded
fragment and constructs one regular witness; it does not describe the full
solution fiber or supply a principal residual representation.

## Finite synchronous construction

Let `Λ` contain all labels in the closed input graphs. Before completeness,
erase every field outside `Λ` throughout an arbitrary satisfying assignment.
Keep every input atom distinct; if the atom domain has values outside the
finite input set, map all such values to one fixed atom outside that set. If
it has none, no extra representative is needed. These transformations
preserve every original direct structural comparison and its retained child
obligations.

Use tagged child coordinates

```text
I = {Arg, Result} ⊎ {Field(ℓ) | ℓ ∈ Λ}.
```

A state at a common address records: presence for each free track; the exact
closed descriptor node or absence for each closed track; and the active
`(original-bound-id, orientation)` obligations. Orientations select the
current order of the same two original tracks. The initial state includes all
free roots, all designated closed roots, and every original bound in its
positive orientation. A shared equality class has one track.

At each state, choose one simultaneous head vector for all present free
tracks: an input atom, Function, or Record with a mask from `Λ`. Closed tracks
follow their exact heads. Reject mismatched heads, atoms, or obligations whose
endpoint is absent. For each coordinate present in any track, construct a
successor state, even when no obligation currently uses that child; it records
all resulting track presences, closed anchors, and obligations. Thus selected
heads always have complete well-formed child graphs. Coordinates absent in
every track may terminate or use one all-absent state.

For each active obligation, apply the direct structural rule. A Record
comparison requires the upper labels to be a subset of the lower labels and
transfers that same obligation only to upper-present fields. A Function
comparison reverses the argument obligation and preserves the result
obligation. No original bound is replaced by a composed comparison. The
finite state graph has at most

```text
2^f · (|K|+1)^c · 2^(2|B|)
```

states for `f` free tracks, `c` closed tracks, `K` closed graph nodes, and `B`
original bounds. The transition alphabet is finite as well.

Compute the greatest fixed point of states admitting some locally valid
transition whose required successor states survive. For soundness, choose one
surviving transition per state. Each `(state, free-track)` component becomes a
node in a finite regular graph and follows the chosen transition's matching
child component. Closed components remain their exact input graphs. For each
original bound separately, the ordered track pairs represented by its active
tokens form a post-fixed structural simulation: local checks hold, and every
required Record or Function child pair remains in that same relation. This
directly witnesses each original inequality.

For completeness, any satisfying assignment, including a nonregular tree
assignment, supplies a synchronous state and actual head vector at every
common address. The finite set of states occurring in this unfolding is
post-fixed, so the initial state survives. Choosing one surviving transition
per state may replace the supplied assignment; it does not assert that equal
abstract states had equal original subtrees. Soundness instead constructs a
new regular assignment satisfying all retained obligations. Root-only
constraints require no equality between subtrees at different addresses.

The label/atom normalization preserves active obligations restricted to
`I*`: Function child paths and their variance are unchanged; every retained
upper Record field keeps its child obligation; erased fields disappear from
both endpoints, so their obligations are no longer requested; atom renaming
preserves identity agreement. This is existence preservation, not full-fiber
preservation.

## Exact boundary and next theorem

The construction cannot handle open descriptor equations such as
`q = Function(x,e)`: that equation requires equality between `q` at
`Arg·w` and `x` at `w`, while states relate tracks only at one common address.
Treating `q` as a separate closed track would lose the equation and can admit
false solutions. This is an exact boundary of the construction, not a
counterexample to a stronger finite method or to general regular-witness
existence.

The next structural theorem must retain shifted root/child equations together
with all joint comparison obligations. Separately, principal residuals,
effective projection for open Records/feedback, source-wide generation and
acceptance, Function/effect compatibility, and lifecycle remain open. The
current implementation gate is unchanged.

## Review and verification

An independent Astra theorem audit found no counterexample or substantive
proof gap within the stated root-only fragment. It required explicit tagged
coordinates, finite atom normalization, complete child-state construction,
fully seeded initial obligations, and the relation-based post-fixed
soundness/completeness argument above. It confirmed that the open-descriptor
address shift is outside the construction. No compiler edits, tests, builds,
Oracle inspection, or measurements were performed.
