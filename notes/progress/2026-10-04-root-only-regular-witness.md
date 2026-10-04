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
fragment and constructs one regular witness. A reviewed corollary below gives
an exact automaton for the normalized image of the regular solution fiber;
neither result describes the full unnormalized fiber or supplies a principal
residual representation.

## Finite synchronous construction

Let `Λ` contain all labels in the closed input graphs. Before completeness,
erase every field outside `Λ` throughout an arbitrary satisfying assignment.
Let `A` contain every input atom identity and, when the atom domain has
identities outside that finite set, one fixed representative for all such
identities. Map each non-input atom to that representative, keeping input
atoms fixed. If there are no non-input atoms, `A` contains only the input
identities. Together, label erasure and atom mapping define an idempotent
normalization `N` that preserves every original direct structural comparison
and its retained child obligations.

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
tracks: an atom from `A`, Function, or Record with a mask from `Λ`. Closed
tracks follow their exact heads. Reject mismatched heads, atoms, or
obligations whose endpoint is absent. For each coordinate present in any
track, construct a successor state, even when no obligation currently uses
that child; it records all resulting track presences, closed anchors, and
obligations. Thus selected heads always have complete well-formed child
graphs. Coordinates absent in every track may terminate or use one
all-absent state.

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

## Exact recognition of the normalized regular fiber

The same finite automaton also recognizes the complete normalized projection
of regular solutions. Let `N` be the normalization above. Consider finite run
graphs whose nodes carry an automaton state and a simultaneous head vector,
with coordinate edges to child run nodes. Each node must be in the greatest
fixed point, and its transition must satisfy local head, anchor, presence,
and bound-obligation checks. Acceptance is coinductive local validity with no
additional fairness condition. Distinct run nodes may carry the same
automaton state with different heads or successors. A run is regular when
this graph is finite. Project its free components to a tuple of regular types
and forget the automaton annotations. Then

```text
{ projections of regular accepting runs }
  = { N(η) | η is a regular solution of the root-only package }.
```

For the forward direction, each original bound's active tokens at run nodes
form a post-fixed direct structural simulation, so the projected tuple
satisfies every original inequality and is already normalized. For the
reverse direction, normalize any regular solution and decorate its unfolding
with the free-track graph nodes, exact closed anchors, and active
bound/orientation set at every address. These annotations range over a finite
product, making a regular run. Local checks follow from the original
comparisons. Its states form a post-fixed set and therefore lie in the
greatest fixed point.

Run memory must be allowed to distinguish occurrences that have the same
automaton state. For example, for `X <: X`, the solution
`X = Function(Int, Int)` has the same state at its root and result child
(present `X`, no closed anchors, the same positive obligation), but different
head vectors. A strategy that chooses exactly one transition per state
constructs one witness and does not recognize this whole normalized fiber.
Allowing multiple run nodes with a repeated state restores exact recognition.
This corollary recognizes only the image under label/atom normalization; it
does not preserve unmentioned-field extensions or provide a principal Yulang
type/residual.

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

A second independent Astra theorem audit found the exact normalized-fiber
corollary sound under finite regular run graphs. It identified and repaired
one necessary distinction: a run graph may contain separate nodes with the
same automaton state and different head vectors; a one-transition-per-state
strategy is only the witness extractor, not the fiber recognizer. The
reviewer found no remaining counterexample or substantive gap within this
scope. No implementation authority follows.
