# Regular witnesses from two-sided constructor bounds

Date: 2026-10-04
Status: Reviewed conditional theorem package
Scope: pure mandatory structural satisfiability with finite, source-checkable two-sided constructor bounds
Base: `research/simple-sub-intrusion` at `eb7bc50d`
Implementation authority: none; the accompanying Python program is a research witness checker
Supersedes: none
Reviewed-by: independent compiler_referee, theorem and research checker, 2026-10-04; no findings

## 1. Result and its relation to the open gate

There is a terminating existence procedure for a substantial multiple-open-
anchor fragment of the current structural package. Every flexible root must
have a constructor-bearing lower bound and a constructor-bearing upper bound,
possibly reached through directed variable inequalities. The anchors may be
recursive, open, mutually dependent, and numerous. No existing anchor needs
to be a solution. The procedure constructs new simultaneous regular trees.

For this fragment, the following are equivalent:

1. the original package has an assignment of possibly nonregular trees;
2. its finite structural closure has no contradiction; and
3. it has a simultaneous regular assignment.

If there are `n` variables after flattening, a witness has at most
`(2^n - 1)^2` nodes. This is an existence bound, not a proposed compiler
resource limit. The witness does not replace the principal residual or
preserve every solution.

The construction specializes the pre-closed-system argument of Emmanuel
Coquery and François Fages, *Subtyping Constraints in Quasi-lattices*,
FSTTCS 2003, DOI [10.1007/978-3-540-24597-1_12](https://doi.org/10.1007/978-3-540-24597-1_12).
The [author-uploaded full manuscript](https://www.researchgate.net/publication/2843336_Subtyping_Constraints_in_Quasi-lattices)
§3.1, Definition 11, Theorem 3 and Corollary 1 gives the relevant result.
The [authors' publication list](https://lifeware.inria.fr/wiki/Main/Publications)
also identifies the paper. The proof below makes the transfer to this
repository's mandatory Records, signed constructors, and recursive descriptor
equations explicit rather than citing a theorem for matching tree domains.

This closes a sufficient class of the regular-completion gate in
[open residual factorization](2026-10-03-open-residual-factorization.md).
It does not settle the unrestricted finite-model property. In particular,
the paper's unrestricted pre-closure algorithm in §3.2 requires nullary
constructor extrema. Function and maximal-width Record constructors do not
satisfy that requirement.

## 2. Exact signature and source-checkable premise

After the existing successful scoped rational equality quotient and its
descriptor-owned scope checks, use the pure structural relation:

- primitive and rigid atoms compare by identity;
- mandatory Records compare by width and covariant retained fields;
- Function has a contravariant argument and covariant result;
- other fixed constructors, when included, compare only with the same head
  and have fixed covariant, contravariant, or invariant coordinates.

All coordinate labels are tagged by their owning constructor, apart from
Record labels within the same Record family. There are finitely many input
Record labels, atoms and constructor heads. For existence, labels absent
from the input may be erased consistently from an arbitrary solution. All
input Record equations retain their exact masks. The constructed witness
uses only input atoms and labels.

The theorem uses the sufficient permission condition of Theorem S: every
input rigid identity is permitted at every descriptor-free root. No new rigid
identity is introduced. Arbitrary `Guard`, `Phi`, joint `K,D` predicates,
effects, optional Records and adapter/concrete-compatibility judgments are
outside this theorem. In particular, this is not a claim that successful
Yulang concrete comparisons compose transitively.

Flatten the finite guarded descriptor graph by allocating a variable for
every quotient node. Retain one nonvariable flat term

```text
t_q = constructor(q_1, ..., q_r)
```

for each descriptor equation `q = t_q`. Each child is a variable reference;
recursive references are not unfolded. Encode that equation as two clauses
`q <= t_q` and `t_q <= q`. Let `V` be all these variables together with the
original free roots, and `T` the finite set of nonvariable flat terms.
Original bounds are retained, with their original endpoints and identities.

The finite closure `R` below is computed on `V ∪ T`. The premise is

```text
for every x in V, there are s,t in T with s R x and x R t.       (PC)
```

Descriptor variables satisfy (PC) from their paired equation clauses. For an
original free root, this requires a directed path from a constructor-bearing
endpoint and a directed path to one. Merely having an undirected incident
anchor is insufficient. The check inspects a finite generated package and
does not ask for a regular witness or for arbitrary-tree satisfiability.
When a source generator emits such a package, checking (PC) is its separate
source-generation certificate. No claim is made that all Yulang generators
or general scheme instantiations emit such packages.

## 3. Finite closure and equality preservation

Seed `R` with the original clauses and paired descriptor clauses, then repeat:

1. add reflexive and transitive consequences on the fixed universe `V ∪ T`;
2. for every related pair of nonvariable terms, check their heads;
3. decompose a compatible pair into its variable-child inequalities.

For Records the lower mask must contain the upper mask; decompose just the
upper's fields. For a fixed head, use the same direction on positive
coordinates, the reverse direction on negative coordinates, and both
directions on invariant coordinates. Different fixed heads, different atoms,
or a missing mandatory upper field are contradictions. No new variable or
term is created during closure. At most `(|V|+|T|)^2` pairs can be added.

These steps are valid for the stated structural relation. To see
transitivity directly, compose two structural simulations: an intermediate
Record supplies the required mask inclusions and child comparisons; a
negative coordinate reverses both premises; an invariant coordinate supplies
both directions. Equivalently, induct on finite-depth structural
approximants. Reflexivity is witnessed by identical subtrees.

Mutual structural subtyping implies tree equality modulo bisimulation. The
root heads agree; mutual Record width makes the masks equal; children again
have mutual comparisons, including at negative coordinates. Consequently
the paired clauses enforce every original descriptor equation exactly,
even on infinite trees. Replacing an equation by these clauses is an
existence-proof translation within this structural order, not a rewrite of
the production concrete comparison rule.

Each closure consequence holds in every input model. Thus a contradiction
rules out arbitrary-tree models. Conversely, assume closure succeeds and
(PC) holds. The rest of the note constructs a regular model.

## 4. The finite witness graph

For nonempty subsets `A,B ⊆ V`, define

```text
L(A) = { s in T : s R a for some a in A }
U(B) = { t in T : b R t for some b in B }.
```

Call `(A,B)` admissible if `a R b` for every `a ∈ A,b ∈ B`.
By (PC), `L(A)` and `U(B)` are nonempty. By transitivity,
every lower term in `L(A)` is related to every upper term in `U(B)`.
Their heads have therefore passed all pairwise decomposition checks.

### 4.1 Head choice

If the compatible terms have an atomic or other fixed head, choose their
common head. If they are Records, choose

```text
M(A,B) = union of masks of all upper terms in U(B).
```

Every lower mask contains `M(A,B)`, since it contains every upper mask.
This chosen head is below every upper head and above every lower head.
It can be a new Record mask not present as an input anchor.

For a coordinate `l`, let `L_l(A)` and `U_l(B)` be the sets of child
variables of the corresponding lower and upper flat terms that possess `l`.
Every chosen coordinate has both sets nonempty. For a Record field, it
occurs in at least one upper term and in every lower term. For a fixed head,
every term possesses every coordinate of that head.

### 4.2 Child choice and its invariant

Create a graph node `gamma(A,B)` with the chosen head and successors

```text
positive l:  gamma(L_l(A), U_l(B))
negative l:  gamma(U_l(B), L_l(A)).
```

Decomposition of the related lower/upper terms supplies every cross pair
needed to make each successor admissible. This is why one nonempty bound on
each side matters: the construction never has to invent an unconstrained
child to replace a missing set.

For an invariant coordinate put `S_l = L_l(A) ∪ U_l(B)` and use
`gamma(S_l,S_l)`. Decomposition supplies both directions between every lower
and upper child. Since both sets are nonempty, transitivity makes all members
of `S_l` mutually related, so this successor is admissible. All such members
have identical lower-term sets and identical upper-term sets. This explicitly
retains the equality requirement; treating an invariant child as only a
positive child would be incorrect.

Memoize a state before creating its children. There are at most
`(2^|V|-1)^2` nonempty pairs. Every edge follows a constructor coordinate,
so the resulting graph is guarded and finite. Finally assign

```text
rho(x) = gamma({x},{x})   for every x in V.
```

Every occurrence of the same source variable has the same root. This global
sharing preserves the shifted root/child equations that an automaton which
only compares tracks at one common address cannot enforce.

## 5. Proof that the assignment satisfies all clauses

The comparison lemma is

```text
L(A) subset L(C) and U(D) subset U(B)
    imply gamma(A,B) <= gamma(C,D),                           (G)
```

for admissible states. Prove (G) by induction on finite comparison depth,
or as a simultaneous post-fixed simulation over graph-node pairs.

At Record roots, the union of the upper masks for `B` contains the union
for `D`, which gives the correct width direction. At fixed heads, the
nonempty inclusions and compatibility force the same head. On positive
coordinates, the lower-child inclusion and reverse upper-child inclusion
persist after taking lower- and upper-term sets. On negative coordinates
they swap, yielding the reversed child comparison required by the head.
For an invariant coordinate the two child unions are internally equivalent
under `R`. The common nonempty lower-child subset connects the unions, so
their members have identical lower- and upper-term sets. Applying the
inductive comparison in both directions gives equal child trees. Thus (G)
holds at every finite depth and hence coinductively.

Now verify each kind of clause.

- **`x R y`:** transitivity gives `L({x}) ⊆ L({y})` and
  `U({y}) ⊆ U({x})`; apply (G).
- **`x R t` with `t ∈ T`:** the chosen head of `rho(x)` is below
  the head of `t`. For a positive retained child `z=t/l`, all lower children
  are related to `z`, while `z` belongs to the upper-child set. Therefore
  `L(L_l({x})) ⊆ L({z})` and `U({z}) ⊆ U(U_l({x}))`.
  Apply (G) to get the child comparison. A negative child reverses these
  sets and the desired order. For an invariant child, all members of its
  union are mutually related to `z`, so (G) applies in both directions.
- **`s R x` with `s ∈ T`:** use the symmetric argument. In a selected
  positive Record field, `s/l` is in the lower-child set and is related
  to every upper child; negative coordinates reverse the comparison.
- **`s R t` with both nonvariable:** the root check passed and the
  required child clauses are already in `R`; use the variable case.

These are a simultaneous finite-depth proof: a constructor/variable clause
at depth `d+1` uses (G) only at depth `d`, and (G) at depth `d+1` uses
itself at depth `d`. No solved query is assumed.

All original inequalities now hold. The paired descriptor inequalities
give the original equations by antisymmetry. The graph contains only input
rigid atoms, so the stated permission condition is preserved. This proves
the theorem and the witness-size bound.

## 6. A recursive example which no anchor selector solves

Let `E={}`, let `E <= Z <= E`, and retain the open recursive descriptor

```text
Y = Function(Z,Y).
```

For a finite label set `S`, write `R_S = { l:Y | l in S }`. Introduce

```text
L1 = Function(R_{a},       R_{f,g,h})
L2 = Function(R_{b},       R_{f,g,k})
U1 = Function(R_{a,b,c},   R_{f})
U2 = Function(R_{a,b,d},   R_{g})

L1 <= X     L2 <= X     X <= U1     X <= U2.
```

All four anchors are open through `Y` and `Z`. Each descriptor variable
gets paired equation clauses, and both free variables `X,Z` have two-sided
constructor bounds. The premise therefore holds.

No anchor is a suitable choice for `X`. Either lower anchor fails the
other lower-bound check (the argument obligations reverse and the result
masks also disagree). Either upper anchor fails the other upper-bound check
because its result lacks `g` or `f`. These failures do not depend on the
value chosen for `Z`.

Nevertheless the following simultaneous regular assignment works:

```text
Z = E
Y = Function(E,Y)
X = Function(R_{a,b}, R_{f,g}).
```

The argument combines demands using Function contravariance; the result
combines the upper Record masks. This constructs a fresh graph instead of
choosing an incident descriptor. It is outside the prior
[anchor-selector witness](../progress/2026-10-04-multi-anchor-selector-witness.md)
construction. The new class and the selector class are not nested: a
one-sided selector instance need not satisfy (PC).

## 7. Exact unresolved scope

Finite closure also terminates when (PC) fails, but successful closure alone
is then not a satisfiability result from this theorem. The checker must
report an unmet premise, not reject the source as ill-typed. Unbounded and
one-sided roots can already have regular solutions such as `X <= {}`.

The remaining unrestricted problem is how to handle missing constructor-
bound directions without an unbounded allocation of fresh child variables
or loss of existing models. Introducing global least/greatest types would
change the signature; it is not a permitted proof step. Nor does a witness
for this pure projection settle Function effects or joint scope/evidence
constraints.

The original residual conjunction remains the description of all solutions.
No extremality or principality of `rho`, exact projection algorithm, complete
raw-source theorem, practical complexity guarantee, or compiler cutover
follows. No production code or existing test contract changes.

## 8. Verification record

The standalone research checker is
`tools/check_preclosed_structural_witness.py`. It implements the finite
closure and reachable pair-state construction, then checks the original
clauses through a separate finite structural simulation. Its examples and
bounded enumeration are diagnostic evidence for the construction; the
arbitrary-tree theorem is established by the proof above. Independent review
and exact execution results are recorded in the paired progress note.
