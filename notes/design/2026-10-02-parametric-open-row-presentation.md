# Finite parametric presentation of open typed-row constraints

Date: 2026-10-02
Status: Draft; mathematical package independently reviewed; not successor implementation authority
Scope: open point-valued typed rows, exact constraint projection, positive row recursion
Approved-by: none
Drafted-by: primary, with bounded architect audit
Reviewed-by: independent compiler_referee and spec_auditor package review; recursive zero-preservation premise repaired and closed by fresh compiler_referee delta review, 2026-10-02
Supersedes: none; extends the closed point-row lemma in the coupled-interface draft

## 1. Claim and source boundary

The previous closed point-row formula enumerates witnesses in two finite
rows. Open tails need not be expanded into all their future request instances.
This package constructs a finite **parametric** formula for their constraints,
proves exact projection of genuinely local row variables, and solves monotone
recursive row equations without enumerating the request universe.

These are mathematics of the existing request-support coordinate, not a new
source semantics. The selected Yulang extensions still determine which
complete computation relation supplies that coordinate: inert argument
reification, actual receiver entry, explicit consumption, typed boundary
transport, and primitive shallow handling. This is a **new successor
presentation candidate**, not a Simple-sub-original theorem. Its row
interpretation and source-generation completeness are not established by the
construction. No Oracle behavior or supported source capability is removed.

In particular, the one-request/two-request shallow-handler discriminator in
the coupled-interface draft still prohibits exact handler subtraction from
support alone. This theorem applies to constraints on support already derived
from a complete relation, or to an independently proved conservative support
transformer. It cannot decide ordered visibility, grant capture authority,
erase latent effects, or discharge the entire `CIncl` relation in
typed-computation-core §7.

## 2. One assignment, pointwise membership

Fix an assignment `ν` of ordinary type/effect-family argument endpoints and
rigid imports. Let `U` be the universe of typed requests `(family, argument
tuple)`. A named point `q_i(ν)` denotes one such request; it is not an
interval independently instantiated at each occurrence. Equality of points
requires equal family heads and invariant argument tuples under **the same**
`ν`. The underlying type equality decision is not supplied here.

A row assignment `η` maps row variables to subsets of `U`. We prove the
results both when rows range over arbitrary subsets and when all rows range
over finite subsets. No finite-versus-infinite source-row choice is required.
The permitted finite expression grammar is zero-preserving away from its
named points:

```text
r ::= empty | {q_i} | X | r union r | r intersect r | r minus r
    | if p(ν) then r else r
    | head_h(r)
```

`minus` is relative set difference; `head_h` keeps members with head `h`.
There is no absolute complement, universal-row literal, cardinality or
nonemptiness predicate in this fragment. A wildcard/open tail is a row
variable, not an implicit enumeration of the universe. Whether particular
source syntax denotes such a variable remains a source typing obligation.

Define a Boolean membership circuit `M_r(ν,u,b)` where `b_X` stands for
`u ∈ η(X)`:

| Row expression | Membership circuit |
|---|---|
| `empty` | `false` |
| `{q_i}` | `u = q_i(ν)` |
| `X` | `b_X` |
| union / intersection / relative difference | `M_r ∨ M_s` / `M_r ∧ M_s` / `M_r ∧ ¬M_s` |
| conditional | `(p ∧ M_r) ∨ (¬p ∧ M_s)` |
| `head_h(r)` | `head(u)=h ∧ M_r` |

Induction on expressions proves
`M_r(ν,u,(u∈η(X))_X) iff u∈⟦r⟧_(ν,η)`.
It also proves that all expressions are false outside their named points
when every row-variable input bit is false. The finite circuit is uniform
in `u`; a new client request supplies an argument, not a new rule.

## 3. Exact finite constraint construction

Generate an inclusion `r ⊆ s` as `M_r ⇒ M_s` and equality as
`M_r ⇔ M_s`. Conjoin these circuits into `Φ`. Let `K(ν)` retain all global
source-owned family well-formedness and ordinary endpoint constraints.
In particular, the shared-binder conditions called `GroupEq` in the
closed-row lemma remain in `K`, before and after row projection.

The constraint block denotes

```text
R(ν,η) iff K(ν) and
                 forall u in U. Φ(ν,u,(u∈η(X))_X).
```

By the membership theorem, this is exactly the simultaneous row constraints
at that assignment, including all possible open tails and all disjunctive
matches. If `K` is false, an empty support does not make the block valid.
No branch chooses a new family argument or a second assignment.

Allow a **finite union of whole blocks** to retain alternative complete
constraint derivations. Their conjunction is computed by a finite product
of branches and conjunction within each block. The branch belongs to the
whole relation: in general

```text
(forall u. Φ1(u)) or (forall u. Φ2(u))
    is not equal to forall u. (Φ1(u) or Φ2(u)).
```

For `U={a,b}`, the left can specify `X={a}` or `X={b}`; the right also
allows `X=empty` and `X={a,b}`. Global alternatives are not moved underneath
the membership quantifier. The presentation adds no source selector; finite
relational union already supplies these alternatives.

This gives exact constraint generation with no set-membership oracle: each
membership use expands by the displayed structural rules. It does not
decide which underlying type assignments realize its equality/`K` predicates.
For a later operation instance `o(ν)`, specializing a membership circuit at
`u=o(ν)` produces finitely many ordinary point equalities and retained row
membership queries. There is one finite schema for all instances, although
the set of grounded queries over arbitrary future clients may be unbounded.
Thus this is not a proof of one fixed grounded Boolean basis `PΩ` for all
clients.

## 4. Exact hiding of local row variables

Partition the row variables into retained `X` and hidden `Y`, with `h=|Y|`.
Assume every occurrence/dependency of `Y` being hidden occurs in this block;
none remains in a root, latent view, continuation/store interface, `K`, or
another unjoined obligation. In a complete interface, its incidence `D`
must establish that premise; absence from immediate residual support is
insufficient. Join all affected constraints before projecting.

In addition, hidden `Y` may occur only through its pointwise membership
inputs in `Φ`: it must not occur in a named point's family-argument type,
a global guard, or a coefficient determined by `ν`. Such occurrences are
nonpointwise dependencies, even when written inside this block. A shared
identity cannot be split into an independent membership variable and type
endpoint to evade this condition; their original dependency must remain
joined and falls outside this projection theorem.

Construct by finite Boolean enumeration

```text
Ψ(ν,u,x) = OR over y in {false,true}^h of Φ(ν,u,x,y).
```

**Projection theorem.** For retained assignment `η_X`,

```text
exists row assignment η_Y. R(ν,η_X union η_Y)
iff K(ν) and forall u. Ψ(ν,u,(u∈η_X(X))_X).
```

Forward implication takes the actual hidden membership vector at each `u`.
For the reverse implication, enumerate the `2^h` vectors in a fixed order.
For each `u`, choose a satisfying vector and put `u` in hidden row `Y_i`
exactly when that vector's `i`th bit is true. This defines a single row
assignment across the whole universe, and the pointwise circuit then holds
everywhere. A fixed finite search defines the choice; no independently
chosen type endpoint or handler witness is introduced.

For **finite** rows, let `W` be the union of the finitely many named points
and all retained row supports. Outside `W`, all singleton/retained inputs
are false and the all-zero hidden vector satisfies every original inclusion
or equality. Choose this vector there, and choose a satisfying vector only
inside `W`. Each hidden witness is therefore a subset of finite `W`.
The reverse implication remains valid for finite-row assignments. Repeated
projection keeps this zero-witness property. This argument would fail for
an absolute complement or a requirement to include all of an infinite `U`;
those constructs were deliberately excluded from the theorem's grammar.

Apply the construction separately to each whole block of a finite union:
existential projection distributes over that union without moving its
branch choice inside `forall u`.

**Exactness/principal relation.** The resulting formula denotes every and
only retained row assignment extendible to a solution. Hence any constraint
relation admitting all such extensions contains this image, and any sound
exact presentation of the image is equivalent to it. This is least relational
image, not a selected row matching or an independent marginal solution for
each exported row. For example, eliminating `Y` from `X=Y` and `Y=Z`
retains `X=Z`; it does not make `X` and `Z` independent.

Type endpoints are held fixed throughout. Replacing the theorem with
`forall u. exists beta,y. Φ` when `beta` is a shared family argument would
be invalid. A requirement for one `beta` to equal `Int` at request `a` and
`Bool` at request `b` has no solution; separate choices of `beta` at those
points would wrongly accept it. Nor may nonpointwise row dependencies be
discarded. This local projection theorem is not yet generalization, fresh
instantiation or SCC intrusion of the complete interface.

## 5. Positive recursive row graphs

For `n` recursive row variables, suppose

```text
Y_i = F_i(Y_1,...,Y_n; X,ν),  1 <= i <= n,
```

where each `F_i` is a membership circuit compiled from the zero-preserving
row-expression grammar of §2 and is monotone in the recursive `Y` bits.
Relative difference is allowed only where it preserves that monotonicity;
an occurrence in the subtracted operand does not get a positivity proof
merely from source effect syntax. Fixed parameters and their complements
may be used as Boolean coefficients within those zero-preserving expressions,
not as independent row constructors. Monotonicity alone is insufficient:
`F(Y;X)=¬X` is monotone in `Y` but yields `U` when `X` is empty, and is not
an admitted row-expression circuit.

To compute the **least** solution, set all recursive membership circuits
to false and iterate the vector `F`. At each fixed `(ν,u,η_X)`, this is a
monotone map on `n` Boolean bits. Starting from bottom, each strict increase
turns at least one formerly false bit true. After at most `n` increases the
sequence is stable. Thus the same `n` symbolic iterations work simultaneously
for every request and every parameter assignment; no request universe is
enumerated. The membership theorem proves that the resulting row vector is
a fixed point and is contained in every other fixed point, by the usual
induction from bottom.

For finite parameter rows, let `W` contain all named points of these equations
and all parameter-row supports. Outside `W`, parameter and singleton inputs
are zero, and the bottom recursive vector is zero. If an iterate is zero
there, the §2 structural zero-preservation property makes the next iterate
zero there as well, regardless of the fixed coefficients. Induction therefore
supports every iterate on finite `W`, so the least solution is finite.
Recursive back edges therefore have a finite
graph/circuit presentation even when execution exposing their requests is
unbounded. Shared circuit nodes avoid tree unfolding. This concerns recursive
**row equations**, not recursive Function contracts or dynamic handler heaps.

Constraint equations and least recursive definitions must not be confused.
The equation `Y=Y` as a constraint permits every row; its least fixed point
is `empty`. The former retains all solutions via §3, while the latter is
valid only when the source-derived abstract rule specifies least closure.
No solver may silently replace the former by the latter. Nonmonotone
recursive constraints remain finite blocks under §3, but have no claimed
least-solution theorem here.

## 6. Costs, invariant transport and remaining milestone

Membership generation is linear in the finite expression/constraint DAG
when nodes are shared. Hiding `h` rows uses at most `2^h` circuit substitutions
per block before Boolean simplification; composing whole-block alternatives
may multiply their counts. Positive recursion requires at most `n` circuit
vector rounds, retaining shared previous-round nodes. These are finite but
not uniformly small bounds. They do not include deciding the underlying
type theory or enumerating an open request universe.

All equations are interpreted under the same `ν` and retain the global
`K` and live dependency incidence. Consistent injective renaming of named
endpoints/row variables merely renames the circuits: structural membership,
finite Boolean substitution, branch union and the finite fixed-point rounds
commute with that renaming. No typed-family constraint is recovered from
concrete materialization. General solver substitutions still have to preserve
the chosen invariant argument interpretation and complete interface premises;
this observation does not discharge Milestone 4.

This package closes the open-tail representability and local row-projection
question for its exact grammar, extending the previous closed point-row
result. It is a finite parametric schema, compatible with either finite or
arbitrary support rows. Positive recursion has a finite regular presentation;
size growth under Boolean projection is a finite resource issue. None of
these facts is a class-3 obstruction or a classification of the full effect
interface.

The next source obligation remains **complete invocation contracts**:
construct the finite relational checking/interaction presentation whose
support constraints belong here, preserving ordered handlers, typed value
paths, mutable state and future/resumed use. A row schema for every future
request does not generate every future caller context or closure body.
Existing selected-fault/certificate and source-simulation results can then
use this row algebra; they cannot be instantiated solely by this theorem.
Required executable conversions, final Oracle acceptance, generalization,
fresh instantiation, SCC intrusion and implementation remain separate gates.
