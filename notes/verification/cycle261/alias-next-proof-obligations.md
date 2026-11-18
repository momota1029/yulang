# Executable alias closure: next proof obligations

This is a proof plan, not a proved compiler. The existing `Alias` constructors are
`refl`, `edge`, `symm`, `trans` over the finite `state.aliases` list.

Proposed state: a duplicate-free vertex universe and a duplicate-free visited sublist.
Universe includes root, all queried site identities, and both ends of every alias edge.
The iteration adds both endpoints adjacent to a visited endpoint. Its strict-progress
measure is the number of universe vertices not yet visited. One can also use a list of
remaining vertices and filter out all newly discovered neighbors, matching the existing
rebase finite-write measure, without claiming those graph vertices are language facts.

The sufficient invariant package is:

1. root ∈ visited, visited ⊆ universe, visited.Nodup;
2. ∀ name ∈ visited, Alias state root name (soundness);
3. strict loop iterations reduce remaining.length;
4. at the final fixed point, for every (a,b) ∈ state.aliases,
   a ∈ visited ↔ b ∈ visited (undirected edge closure).

Completeness needs no separately assumed shortest-path bound. First prove for any
Alias state a b that a ∈ visited ↔ b ∈ visited by induction on that Alias derivation:
refl is Iff.rfl, edge is invariant4, symm reverses iff, trans composes iff. Applying this
with a=root and invariant1 gives every actual alias in visited. Coupled with invariant2,
this is an iff for every queried identity.

Then prove filter predicate equality on the *original* ordered sites list and flatMap
outputs without changing duplicates. This yields a list equality with the existing
noncomputable requests, not only a membership approximation. `SourceSnapshot261` can
then replace the noncomputable selection with this executable equivalent.

Do not extend the claim to changing source snapshots or arbitrary packet inspection.
The universe is recomputed from one actual finite snapshot, and the source-wide fixed
request basis and Plan/capture transport obligations remain separate.

Experiment coverage: exhaustive 64 undirected four-vertex graphs, five roots (including
an isolated outside root), one disconnected query, plus a path through a non-site vertex
and preserved output duplicates/order. All 320 graph/root cases agree with union-find.
This is not an independent Lean build, source reachability test, or proof of the algorithm.
