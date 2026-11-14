# Cycle175 table certificate: structural cost and next indexing step

Status: read-only source analysis. The correctness/equivalence theorems are
Lean-checked; the operation counts and asymptotic bounds below are NOT formal
Lean cost theorems. No additional compiler/benchmark invocation was made for
this analysis.

## Parameters and exact structural counts

Let D be the number of declarations, E the sum of their requirement-list
lengths, N = D + E = `roleNodes registry |>.length`, and F the requested fuel.
Multiplicity is retained. For each Nat role r, let e(r) count requirements
across declarations whose parent role is r, and n(r) count occurrences of r in
`roleNodes`. Define M = sum_r n(r) * e(r). Then sum_r e(r)=E,
sum_r n(r)=N, and M <= N*E. M can exceed E because the table currently retains
duplicate role entries, including roles that appear repeatedly as children.
These equalities describe the list traversals in the definitions, not new
repository lemmas.

`heightTable registry (f+1)` has exactly ONE recursive call to fuel f and passes
its result as the old table to `advance`. It does not recursively call itself
inside the child fold. Under ordinary eager execution:

- There are F calls to `advance` and F*N table-entry computations.
- Every `advance` recomputes `roleNodes` once, then maps all N entries.
- Each of these N entries calls `childRoles`; that function tests all D
  declaration parent roles and visits/emits e(r) selected child roles.
  Thus one round makes N*D parent-role equality tests and M child fold steps.
- Each child fold step performs one `lookup old child`, one increment and one
  max. The first round's old table is empty. Every later old table has N pairs.
  Linear first-match lookup performs at most N key-equality tests. Therefore
  table construction performs at most max(F-1,0)*M*N table-key tests.
- The final `checkTable` traverses at most D declarations and E clauses
  (List.all can short-circuit). Per visited clause it performs two lookups and
  one strict height comparison, hence at most 2*E*N additional key tests.
- The uniform wrapper computes the same N once more to choose F=N. Empty
  registry has N=0, F=0 and no edge work; the inequalities still hold.

These counts assume no optional compiler common-subexpression elimination;
such optimization could reduce actual calls but is not required by the proof.
The shared table is a single let-bound value at the final checker. Duplicate
IDs are never inspected by this certificate; correctness does not assert
independent declaration validity/Checked.

## Coarse bound and what it does not mean

Counting Nat equality/ordering/max/addition as unit operations and list
traversal/append/map linearly in visited cells gives the coarse upper bound

  O(F * (N + N*D + M*(N+1)) + D + E*(N+1)).

Using M <= N*E gives

  O(F * (N + N*D + N*E*(N+1)) + D + E*(N+1)).

For F=N this is polynomial; the deliberately loose worst-case envelope is
O(N^4) when E<=N. It is not claimed tight. On duplicated chain inputs n(r) and
e(r) stay bounded, so M=O(N); this expression becomes O(N^3), not exponential.
The observed speedup at length12 is evidence only for that synthetic fixture.

The model ignores arbitrary-precision Nat comparison costs, allocator/GC,
Lean VM/compiler transformations, and proof elaboration. Role IDs need not be
small. Heights are bounded by fuel through the proved equality with
computedHeight and the existing height bound, but this note does not claim a
bit-complexity or wall-clock guarantee. Total table-pair production is F*N;
this is NOT asserted to be a measured or formally bounded peak resident size.
The recurrence is not tail recursive, so stack handling for large F is a
separate implementation concern.

## Remaining bottlenecks

1. Every stored role is searched linearly for every child edge.
2. Child adjacency is rebuilt by a full D-declaration scan for every table
   entry in every round.
3. Repeated role names cause duplicate table entries and duplicate folds.
4. `roleNodes` is rebuilt each round, although the registry is unchanged.
5. The final edge checker repeats each parent lookup for all its clauses.

## Semantics-preserving Array/index candidate (not implemented)

Build a finite enumeration of unique role Nat values from roleNodes and a
role-to-index map. Build adjacency arrays once by scanning declarations and
requirements. Keep a lookup default of zero only for roles outside the
inventory. Compute successive height arrays of size V (number of unique
roles), and use constant-index reads in edge folds. Keep the original fuel
F=N first: this avoids changing even the bound while proving the new backend.
No declaration/candidate/source identifiers or language rules need change.

Required proof obligations, in order:

1. The unique enumeration covers exactly all parent and child roles. Each
   enumerated role has a unique in-bounds index, and decoding that index gives
   the original Nat. An external role must not alias a valid index/default.
2. Indexed adjacency has exactly the same children as `childRoles`, including
   multiplicity if that is the chosen representation. If edges are deduped,
   prove separately that the max fold is unchanged; do not silently drop them.
3. After every round f, each indexed height equals `computedHeight registry f`
   at the decoded role. Use separate old/new arrays so updates are synchronous;
   in-place updates without this invariant would change bounded heights.
4. The final Boolean edge check equals `check registry F` for every registry
   and F, without DAG, Checked or ID-uniqueness assumptions. Recover
   certify equality and existing exactness consumers by rewriting.
5. Re-run empty, duplicate-key/edge, disconnected-cycle and reorder tests;
   rerun one bounded paired performance comparison before claiming benefit.

Ignoring finite indexing construction, ideal per-round work becomes O(V+E)
and total O(F*(V+E)+D+E). Construction cost depends on the chosen finite map:
naive List index lookup remains O(N*V), while balanced maps introduce key
comparison/logarithmic costs. These are design estimates, not Lean proofs.
Using a smaller F=V or a topological-worklist algorithm could be a later
independent optimization, but would need additional bounded-completeness or
fixpoint proofs. Neither is needed merely to replace storage with arrays.
