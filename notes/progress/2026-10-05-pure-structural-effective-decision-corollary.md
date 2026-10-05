# Effective finite search for the pure structural package

Date: 2026-10-05
Status: unreviewed derivation from a Reviewed theorem; proof-search result only
Governing result: [finite-fence completion](../design/2026-10-04-structural-fmp-fence-completion.md), Theorem FMP and §§2, 6, 9–11
Implementation authority: none

## Claim and input boundary

For a fixed finite normalized pure structural package `P`, satisfiability is
decidable by finite search under this effective-input condition:

1. the package explicitly lists its finite roots, flat descriptor terms,
   descriptor equations, and structural bounds;
2. constructor heads appearing in those terms have a finite, decidable
   signature (arity and variance), and Record labels have decidable equality;
3. for each root permission set and each rigid identity syntactically present
   in `P`, membership in that permission set is decidable.

Permission sets may be mathematically arbitrary or infinite. The algorithm
only asks finitely many membership questions because the FMP construction
introduces no rigid identity absent from an input anchor. If the input
encoding cannot answer those finite queries, this corollary makes no
effectivity claim for that encoding.

Let `N` be the finite flat-term universe size from FMP §2. The search need
only enumerate deterministic constructor graphs with at most `8^N` states.
Each graph node is labelled by an input constructor head, an input rigid atom,
or a Record whose field mask is a subset of the finite set of input Record
labels; include the empty Record. Child edges match the selected head's arity.
Assign each package root to a graph state.

For each candidate, check descriptor equations and original inequalities on
the graph's regular-tree unfolding, check root permissions by reachability,
and accept iff all checks hold. Structural comparison is decidable on a
finite product graph: start with all node pairs and remove pairs that fail
the local atom/head/Record-width condition or whose required variance-directed
successor pair has already been removed. The descending sequence stabilizes
after finitely many pair removals. Invariant children use the existing exact
tree-equality condition. Permission checks inspect the finite set of rigid
labels reachable from each root.

## Proof of the decision claim

**Soundness of acceptance.** Every enumerated graph is finite and guarded, so
its unfolding assigns proper regular trees to the roots and descriptor nodes.
The finite greatest-fixed-point check is exactly the structural simulation
definition on those unfoldings. The explicit checks therefore produce a
permitted solution of `P`.

**Completeness of the bounded search.** If `P` has any permitted assignment
of arbitrary proper trees, Theorem FMP constructs a permitted simultaneous
regular solution with at most `8^N` states. The construction labels each
state with a fixed head or atom selected from a finite input anchor, or with
a Record mask formed by union of masks of input Record anchors; an
unanchored state uses the existing empty Record. Its recursive successor
profiles still range over the same finite term universe. Thus this witness
is among the enumerated candidates. Permission preservation is part of
Theorem FMP's same-address shadow proof, and the enumerator independently
checks the resulting reachable rigid identities against each original root
permission set. Therefore every satisfiable package is accepted by some
candidate.

The candidate set is finite and effectively enumerable under the stated
input condition. Each candidate check terminates, so the procedure terminates
with SAT iff `P` is satisfiable, and UNSAT otherwise. The bound is enormous;
this establishes decidability, not a practical solver or resource policy.

## Boundary

This corollary concerns only the exact normalized pure structural package of
Theorem FMP. It does not decide the finite constrained residual together with
`Guard`, `Phi`, `K,D`, effects, role-sensitive Function observations, or
source admission. It gives no principal public projection, no source-to-
package theorem, and no production inference authority. Those remain in the
separate `RES`, `EFF`, callback, and principality gates. In particular, this
result does not turn the open residual-factorization candidate into an
effective joint solver.

This derivation has not received independent review. The key conformance
check for review is that every label in the FMP witness construction is
indeed drawn from the finite input anchor signature described above, while
scope preservation continues to use the theorem's root-specific shadow
argument rather than a new global permission assumption.
