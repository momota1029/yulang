# Structural FMP by finite fence profiles

Date: 2026-10-04
Status: Reviewed mathematical theorem; normalized pure structural FMP proved
Classification: A
Reviewed-by: two independent compiler-referee reviews, arbitrary/scope and finite-profile/source-conformance domains; no findings
Scope: the existing normalized pure structural package, including arbitrary rigid permission sets
Base inspected: `76e7715f77ae0bdf4926cc494b8c496cc2f6afd8`
Integration base: `00e317226966827b42a14bef125bd088e60f83d5`
Implementation authority: none
Supersedes: the open FMP/BR status of the finite-feedback result; no semantic rule

Review and verification: [paired progress record](../progress/2026-10-04-structural-fmp-proof.md).

## 1. Result, authority and attribution

**Theorem FMP.** Fix a finite normalized pure structural package `P`. If `P`
has a scope-permitted assignment of arbitrary proper trees, then it has a
scope-permitted assignment represented by one finite guarded graph. If `N`
is the number of variables and flat constructor terms in §2, at most `8^N`
graph states suffice. In particular,

```text
Sat_I*(Gamma_P)
  => exists finite surjective monoid quotient mu. Sat_mu(Gamma_P).
```

By the reviewed free-closure and regular-quotient characterizations, this
proves the requested statement with its fixed-package quantifiers:

```text
for every fixed normalized P,
  [for every finite surjective mu, Gamma_P is inconsistent on mu]
  => [the free-address least closure of Gamma_P has a finite conflict].
```

The proof does not require Structural S, preclosure (PC), one-sided anchor
restrictions, common permission sets, or a new source-generation hypothesis.
It preserves the proper-tree carrier, mandatory Record width, Function
variance, exact descriptor equations, and the identities of original bounds.

The governing semantic boundaries are
[scoped structural projection, §§2 and 6](2026-10-03-scoped-structural-projection.md),
[scoped constraint solving](2026-10-03-scoped-constraint-solving.md), and
[open residual factorization](2026-10-03-open-residual-factorization.md).
The existing bridges used only at the end are
[least forced completion](../progress/2026-10-03-open-residual-factorization.md#least-forced-completion-for-arbitrary-solutions-2026-10-04)
and the
[complete finite-quotient equivalence](../progress/2026-10-04-direct-main-gate-attacks.md#exact-regular-completion-premise).

**Attribution.** The method is the finite distance-state construction in
Dilip Sequeira, *Type Inference with Bounded Quantification*, PhD thesis,
University of Edinburgh, 1998,
[ECS-LFCS-98-403](https://www.lfcs.inf.ed.ac.uk/reports/98/ECS-LFCS-98-403/ECS-LFCS-98-403.pdf).
Relevant locators are §4.1 (native Record distance decomposition),
Proposition 4.2.2 (closure), Definitions 4.2.3–4.2.10 and Theorem 4.2.11
(finite states and exact term substitution), and §4.3 (Record choice).
The source develops regular types; its theorem alone is not the required
arbitrary-tree implication. Here §3 proves the needed arbitrary-tree
diameter, §§4–8 give the specialized finite algebra and constructor argument,
§9 retains globally shared recursive descriptors, and §10 proves the
additional permission transfer. No result about adding global extrema is
used. The specialized proof below can be checked directly from its finite
tables and coinductive simulations.

The bound `8^N` is an existence bound. This note selects no compiler
algorithm, resource limit, source rejection, existential type feature,
principal residual representation, or production Function/effect semantics.

## 2. Exact input and mathematical order

Start after the existing successful scoped rational equality normalization.
There are finitely many original roots, shared guarded descriptor nodes,
original inequalities, and permission sets. Each descriptor node has an
equation

```text
q = t_q = C(q_1,...,q_r),
```

where the children are references to the same finite root set. A Record
descriptor includes its exact finite mask. Atoms are nullary terms.
Let `V` contain these node variables and every original flexible root;
let `T` contain the nonvariable flat descriptor terms. Put `E = V union T`
and `N = |E|`. Every child of a term in `T` is in `V`. Recursive references
are not unfolded and no new child variable is generated during the proof.

Retain each original inequality and encode each descriptor equation by
`q <= t_q` and `t_q <= q`. Finite presentations with explicit constant
endpoints are flattened in the same way. Let this finite list be `C_P`.
Duplicate equal syntactic terms may be kept as separate occurrences; this
only enlarges `N`.

All comparisons in this note use the existing *pure structural order* on
proper, possibly infinite trees, modulo tree bisimulation:

- atoms compare only with the identical primitive or rigid name;
- fixed heads compare only with the same head, using their declared
  positive, negative, or invariant coordinates;
- `Record(F,s) <= Record(G,t)` means `G subseteq F` and
  `s_l <= t_l` for every `l in G`.

Function has a negative argument and positive result. Invariant coordinates
require equality. Child coordinates are tagged by their owning fixed head;
Record coordinates use their field labels. There are no optional or padded
children and no global Top or Bottom.

This order is reflexive and transitive by composition of structural
simulations. For Records, the intermediate mask supplies both required
inclusions; negative coordinates reverse both comparisons; invariant
coordinates preserve equality. Mutual subtyping is tree equality: heads
agree, both width inclusions make the masks equal, and the child trees are
again mutually related. Thus the paired clauses express each exact
descriptor equation on arbitrary as well as regular trees. These are
mathematical proof steps in the pure order, not an instruction to compose
the wider production concrete-comparison judgments.

Fix an arbitrary permitted solution `alpha` of `P` for the implication to be
proved. Interpret each flat term by its actual constructor applied to the
`alpha` values of its referenced children. No regularity is assumed of
`alpha`, of those children, or of any intermediate tree in §3.

## 3. A uniform diameter for arbitrary proper trees

A finite up-fence from `s` to `t` is an alternating sequence
`s <= ... >= ... <= ...`; a down-fence starts with `>=`. Repeated points
are allowed. Its length is its number of edges. We use positive lengths,
so equality has distance `(1,1)`. Write `d(s,t)=(u,d)` for the least
up- and down-lengths when a finite fence exists. Inserting an initial
equality changes the starting orientation, so either both lengths exist
or neither exists, and they differ by at most one.

### Lemma 1: connected-component diameter at most `(3,3)`

If two arbitrary proper trees are joined by a finite fence, they admit both
an up-fence and a down-fence of length three.

**Proof.** A finite fence cannot change a non-Record constructor family or
an atomic identity. At a fixed head its child endpoints are again connected;
on an invariant coordinate all trees along the fence have the identical
child. These statements follow by inspecting each comparison edge.

For all connected pairs `(s,t)`, simultaneously define two intermediate
trees `U_1(s,t), U_2(s,t)` for an up-fence and two `D_1(s,t), D_2(s,t)` for
a down-fence, as follows.

- For Record endpoints, choose the quadruples
  `(s, {}, t, t)` and `(s, s, {}, t)`, respectively. Both are valid because
  every Record is below the existing empty Record.
- For equal atoms, all four entries are that atom.
- For endpoints with the same fixed head `C`, construct the intermediate
  `C` trees coordinatewise. A positive coordinate uses its child pair's
  up intermediates in the up construction and down intermediates in the
  down construction. A negative coordinate exchanges the two constructions.
  An invariant coordinate copies the common child into every entry.

Every recursive call occurs below a constructor. These equations therefore
define proper trees by guarded corecursion, even for nonregular endpoints.
The three intended edges of the up and down quadruples, together with the
Record boundary edges and copied equalities, form simultaneous post-fixed
structural simulations. At a negative coordinate the exchanged construction
has exactly the reversed three orientations. Thus

```text
s <= U_1(s,t) >= U_2(s,t) <= t,
s >= D_1(s,t) <= D_2(s,t) >= t.
```

No finite-state assumption was used. QED.

The lemma bounds distances only within a connected component. It never
replaces absence of a finite fence by a finite distance. In particular,
different atoms and incompatible fixed heads remain disconnected.

## 4. Finite distance calculus and sound closure

Let `D` be the following seven distance bounds, ordered coordinatewise.

| Symbol | Pair | Meaning of `d(s,t) <= symbol` |
|---|---|---|
| E0 | `(1,1)` | `s = t` |
| U | `(1,2)` | `s <= t` |
| Dn | `(2,1)` | `s >= t` |
| B | `(2,2)` | a common upper and a common lower exist |
| H | `(2,3)` | a common upper exists |
| L | `(3,2)` | a common lower exists |
| C | `(3,3)` | a finite fence exists |

`E0` is a distance symbol; `E` without a subscript remains the finite term
universe. `Dn` distinguishes the distance symbol from the set `D`.
There is also an undefined value `infty` for absence of any derived finite
bound. It is not a tree or a constructor.

Meet `a meet b` is coordinatewise minimum. Endpoint reversal `inv` fixes
`E0,B,H,L,C` and exchanges `U,Dn`. Variance conjugation `star` swaps the two
coordinates: it exchanges `U,Dn` and `H,L`, fixing `E0,B,C`. These two
involutions must not be confused.

For finite bounds, define `a (+) b` by concatenating fences, minimizing
orientations, and capping at `(3,3)` using Lemma 1. Its complete table is:

| `(+)` | E0 | U | Dn | B | H | L | C |
|---|---|---|---|---|---|---|---|
| E0 | E0 | U | Dn | B | H | L | C |
| U | U | U | H | H | H | C | C |
| Dn | Dn | L | Dn | L | C | L | C |
| B | B | L | H | C | C | C | C |
| H | H | C | H | C | C | C | C |
| L | L | L | C | C | C | C | C |
| C | C | C | C | C | C | C | C |

For example `U (+) Dn = H` expresses a common upper, while
`Dn (+) U = L` expresses a common lower. One way to verify every entry is
to concatenate the two alternating fences and contract consecutive edges
with the same orientation by transitivity. Before truncation, for
`a=(u,d)` and `b=(v,w)`, the two resulting minima are

```text
u + (w if u is even else v) - 1,
d + (v if d is even else w) - 1.
```

The table is associative, monotone, has identity `E0`, and distributes over
nonempty finite meets in both arguments. Also

```text
inv(a (+) b)  = inv(b) (+) inv(a),
star(a (+) b) = star(a) (+) star(b).
```

Both involutions preserve meets. These identities follow entrywise from
the displayed finite table. The accompanying
[finite-algebra check](../progress/evidence/2026-10-04-fence-completion-algebra.py) exhausts
the pairs/triples used in them. All later algebra uses this capped table;
it does not cap an undefined distance.

### 4.1 Necessary head and child consequences

A finite bound between two nonvariable flat terms requires the same fixed
head, the same atomic identity, or two Records. For Records with masks
`F,G`, bounds `E0,U,Dn` respectively require

```text
F = G,       F superseteq G,       F subseteq G.
```

The other four bounds impose no shallow mask condition. At the head level
any two masks have both the empty-mask upper and union-mask lower.

The child consequences of a bound `e` are:

| Parent terms | Coordinate | Derived child bound |
|---|---|---|
| same fixed head | positive | `e` |
| same fixed head | negative | `star(e)` |
| same fixed head | invariant | `E0` |
| Records, `e in {E0,U,Dn}` | field common to both masks | `e` |
| Records, `e in {B,L}` | field common to both masks | `L` |
| Records, `e in {H,C}` | any field | no consequence |

These consequences are sound on arbitrary trees. At a fixed head, project
each fence edge, reversing signs on a negative coordinate and obtaining
equality on an invariant coordinate. At a Record comparison, every common
field has the stated comparison. A common lower Record must contain both
masks; its common-field payload is a common lower of those payloads. This
gives `L` for parent `B` or `L`. No such payload conclusion follows from
a common upper: the empty Record can omit the field. No absent child is
ever introduced or inspected.

Only this necessary direction is needed for closure soundness and §10.
The later finite construction proves sufficiency for the original package;
we do not assume that pairwise realizable arbitrary profile constraints
already have a simultaneous tree solution.

### 4.2 The finite matrix `d_I`

Initialize a partial distance matrix on `E x E` with all diagonal values
`E0` and all clauses of `C_P` at bound `U`. Repeatedly add reversal,
composition by `(+)`, meet, and the child consequences above. All values
are in `D`; unconnected entries remain undefined. When two nonvariable
terms have a finite bound, check the shallow conditions of §4.1. There are
only finitely many entries and each can decrease only finitely many times,
so the process reaches a finite closed matrix `d_I` or a shallow conflict.

Every update is true in `alpha`: reversal and meet are immediate,
composition is fence concatenation followed by Lemma 1, and child
decomposition was just proved sound. Therefore no conflict occurs and

```text
d(alpha(s), alpha(t)) <= d_I(s,t)
```

whenever the right side is defined. This is the arbitrary-tree-to-finite-
closure bridge. It is independent of the regular-model conclusion.

The closed matrix has reflexivity, reversal, the triangle inequality, and
the stated decomposition properties. Its defined pairs form equivalence
classes: reversal gives symmetry and composition gives transitivity.
Undefined means only that no finite bound was derived, not that the two
values in every model must be disconnected.

## 5. Profiles, expansion and comparison

A profile is a partial map `S:E -> D`. It is **admissible** when, for every
`s,t` in its domain,

```text
d_I(s,t) is defined and d_I(s,t) <= inv(S(s)) (+) S(t).       (Ad)
```

An admissible nonempty profile is contained in one defined component of
`d_I`. Its constructor anchors are the nonvariable terms in its domain.
Shallow consistency of `d_I` and (Ad) make their constructor family unique;
an atomic family contains just one identity. Different Record masks are
allowed. A profile containing only variables has no constructor anchor.

For any profile `S`, define its expansion `X(S)` at `t` by

```text
X(S)(t) = meet { S(s) (+) d_I(s,t) : s in dom(S), d_I(s,t) defined },
```

if this set is nonempty, and leave it undefined otherwise. The meet is
finite and nonempty whenever taken. Thus `X(S)` has precisely the union of
the defined components meeting `dom(S)`. The empty profile expands to the
empty profile.

### Lemma 2: expansion

1. `X(S)(s) <= S(s)` on the original domain.
2. If `S` is admissible, then `X(S)` is admissible.
3. `X(S)` is triangle-closed:
   `X(S)(t) <= X(S)(s) (+) d_I(s,t)` whenever defined.
4. `X(X(S)) = X(S)`.

**Proof.** Part 1 uses the diagonal `E0`. For part 2, take any contributors
`a,b` from `dom(S)` to expanded entries `s,t`. Closure and (Ad) give

```text
d_I(s,t)
 <= inv(d_I(a,s)) (+) d_I(a,b) (+) d_I(b,t)
 <= inv(S(a) (+) d_I(a,s)) (+) (S(b) (+) d_I(b,t)).
```

All entries exist because an admissible profile is contained in one
component. Meet over the contributors `a,b` and distribute to obtain
`d_I(s,t) <= inv(X(S)(s)) (+) X(S)(t)`. Empty profiles are immediate.
Part 3 follows from the triangle inequality for `d_I`, associativity and
meet distributivity. Part 3 gives one direction of part 4; part 1 gives
the other, and their domains agree by component closure. QED.

Write `S . T` if the domains agree and, at every domain entry `t`,

```text
S(t) <= U  (+) T(t),
T(t) <= Dn (+) S(t).                                      (Rel)
```

If `S . T`, then `X(S) . X(T)`: the expanded domains agree, and both
inequalities extend to each contributor by associativity and then to the
meet by distributivity. This assertion needs equal *raw* domains; §8
does not apply it before establishing domain equality for Record descent.

For each original term `t`, set

```text
start_t = X({t:E0}) = d_I(t,-).
```

Singleton profiles and hence all start profiles are admissible. A clause
`s <= t` implies `start_s . start_t` by the two triangle inequalities
through `d_I(s,t) <= U` and its reversal. If `d_I(s,t)=E0`, the two start
profiles are identical, including their domains.

## 6. Head choice and raw child profiles

For an admissible profile `S`, choose its graph head `g(S)` as follows.

- A fixed-head constructor anchor selects that common fixed head.
- An atomic anchor selects that exact identity.
- A Record anchor selects `Record(M(S))`, where
  `M(S)` is the union of masks of all Record anchors `t` with `S(t) <= U`.
- If there is no constructor anchor, select the existing empty Record.

The Record union can be empty. It uses only the finite input field alphabet.
No atom is selected by default. The first three cases are disjoint by (Ad)
and shallow consistency; the fourth includes the empty profile.

For each selected child coordinate `i`, form a raw profile `R_i(S)` from
the constructor anchors in `S` that have that coordinate. At fixed heads,
each anchor contributes its child at the positive bound `S(t)`, the negative
bound `star(S(t))`, or the invariant bound `E0`, respectively.

At a selected Record field `l`, use the partial projection

| Parent bound `e` | E0 | U | Dn | B | H | L | C |
|---|---|---|---|---|---|---|---|
| `pi(e)` | E0 | U | Dn | L | undefined | L | undefined |

Only an anchor actually containing `l` can contribute. Meet multiple
contributions to the same child variable. Put

```text
K_i(S) = X(R_i(S)).
```

This construction uses the original finite term set throughout. It does
not introduce a variable for each successively observed child address.

### Lemma 3: shallow choice and ordered masks

For every constructor anchor `t` of `S`, its shallow distance from `g(S)`
is at most `S(t)`. If `S . T`, their chosen heads are structurally compatible;
for Records, `M(S) superseteq M(T)`.

**Proof.** Fixed heads and atoms follow from the unique anchor family. In
the Record case, if `S(t) <= U`, the mask of `t` is included in `M(S)`.
If `S(t)` is `E0` or `Dn`, and `r` is any upper-near anchor with
`S(r) <= U`, then (Ad) gives

```text
d_I(t,r) <= inv(S(t)) (+) S(r) <= U.
```

Shallow consistency therefore makes the mask of `t` contain that of `r`;
hence it contains `M(S)`. These two conclusions give exactly the mask
conditions for `E0,U,Dn`. For all other bounds any two masks meet the
shallow condition.

For related profiles the anchor sets coincide. In the Record case
`T(t) <= U` implies `S(t) <= U (+) U = U`, proving mask inclusion. With
no anchors both chosen heads are `{}`. QED.

## 7. Every successor is admissible

### Lemma 4: successor consistency

If `S` is admissible and `i` is a selected coordinate, then `R_i(S)` and
`K_i(S)` are admissible.

**Fixed heads.** For any two parent contributions, (Ad) gives their binary
distance bound. Decompose it on the coordinate. Positive coordinates keep
that bound. For negative coordinates use

```text
star(inv(a) (+) b) = inv(star(a)) (+) star(b).
```

For invariant coordinates, any finite parent distance decomposes to child
equality; all contributed child terms thus have pairwise bound `E0`.
After duplicate children are reduced by meet, distributivity proves (Ad)
for the raw profile. Lemma 2 proves it for the expanded profile.

**Records.** Fix a selected field `l`. There is a **landmark** Record term
`r` containing `l` with `S(r) <= U`; this follows from the definition of
`M(S)`. The raw contribution values are in `{E0,U,Dn,L}`. For two such
values `a,b`, the required bound `inv(a) (+) b` is:

| First / second | E0 | U | Dn | L |
|---|---|---|---|---|
| E0 | E0 | U | Dn | L |
| U | Dn | L | Dn | L |
| Dn | U | U | H | C |
| L | L | L | C | C |

Except for the four entries `H,C`, the bound follows directly from (Ad)
for the two parent terms followed by the Record rule of §4.1. This checks
both possible parents `B,L` of a raw `L` contribution: either parent
decomposes to child `L` whenever that consequence is needed.

For the four exceptional entries, use `r`:

- A raw `Dn` contribution has parent value `Dn`, so (Ad) from its parent
  `t` to `r` gives `d_I(t,r) <= U`; hence `d_I(t_l,r_l) <= U`.
- A raw `L` contribution has parent value `B` or `L`, so (Ad) gives
  `d_I(t,r) <= L`; hence `d_I(t_l,r_l) <= L`.

Compose the child bounds through `r_l`. The four resulting bounds are

```text
(Dn,Dn): U (+) inv(U) = H,
(Dn,L):  U (+) L      = C,
(L,Dn):  L (+) inv(U) = C,
(L,L):   L (+) L      = C.
```

These are all exceptional cases. Meet reduction of duplicate child
contributions again follows from distributivity; then apply Lemma 2. QED.

## 8. Related profiles have correctly related successors

### Lemma 5: successor comparison

If `S . T`, then their selected successors satisfy the direct structural
requirements: positive children have `K_i(S) . K_i(T)`, negative children
have `K_i(T) . K_i(S)`, and invariant children are the identical profile.
For Records this is required for every field selected by `T`.

**Fixed heads.** The raw contribution supports agree, because the parent
domains agree. Positive projection and meet distribute through (Rel).
Negative projection conjugates both inequalities, exchanges `U,Dn`, and
therefore reverses the relation. Expansion preserves these relations.
For an invariant coordinate every raw contribution is `E0`; the two parent
domains give exactly the same raw child profile, so their expansions are
identical. This supplies equality, not just one child comparison.

**Records.** By Lemma 3, `M(S)` contains `M(T)`. Fix `l in M(T)` and a
landmark `r` containing `l` with `T(r) <= U`. Then `S(r) <= U` too. Write
`S_l = K_l(S)` and `T_l = K_l(T)`.

First, for each raw `T` contribution from a parent term `t`, prove that
`t_l` belongs to the expanded domain of `S_l` and

```text
S_l(t_l) <= U (+) pi(T(t)).                                (F)
```

The complete cases are:

| Parent value in T | Argument in expanded S | Target bound |
|---|---|---|
| E0 or U | `S(t) <= U`; a raw child contribution exists at most U | U |
| Dn | T-admissibility gives `d_I(t,r) <= U`, hence `t_l <= r_l`; use the S raw landmark at most U and the reversed child bound | `U (+) Dn = H` |
| B or L | T-admissibility gives `d_I(t,r) <= L`, hence child bound L; use the S raw landmark at most U | `U (+) L = C` |

The landmark composition in the second row is from the unknown child to
`r_l` and then from `r_l` to `t_l`; this is why its second bound is `Dn`.
Rows `H,C` do not contribute to a raw Record child profile.

For the opposite direction, inspect any raw `S` parent contribution.
The inequality `T(t) <= Dn (+) S(t)` forces a raw `T` contribution and

```text
pi(T(t)) <= Dn (+) pi(S(t)).                               (R)
```

Indeed parent values `E0,U,Dn,B,L` in `S` respectively give upper bounds
`Dn,L,Dn,L,L` in `T`. Every bound below one of these has defined projection,
and the projection is at most the same listed bound. This exhausts (R).

Consequently the raw `S` support is contained in the raw `T` support,
whereas (F) puts the entire raw `T` support in the expanded `S` support.
Expansion closes exactly under finite `d_I` connectivity, so the expanded
supports agree. No equality of the raw supports was assumed.

Meet over repeated contributions and use Lemma 2's triangle closure to
extend (F) from raw `T` children to every entry of `T_l`; distributivity
gives `S_l <= U (+) T_l`. Apply the same argument to (R), now expanding
the raw `S` entries, to obtain `T_l <= Dn (+) S_l`. Thus `S_l . T_l`.
QED.

## 9. The finite regular solution and exact descriptor sharing

Take the least set of profiles containing every `start_t`, `t in E`, and
closed under the selected successors `K_i`. Label each profile by `g(S)`
and place the indicated child edges to `K_i(S)`. Lemmas 2 and 4 make all
reachable profiles admissible. Each is a partial function on `N` terms
with seven finite values plus undefined, so there are at most `8^N`
profiles. All edges lie below selected constructors. This is one finite
guarded graph of proper trees. Let `theta(t)` be its unfolding from
`start_t`.

### Lemma 6: exact flat-term substitution

For a nonvariable term `t=C(c_1,...,c_r)`, the graph at `start_t` has its
exact head and mask, and its `i` successor is **exactly** `start_(c_i)`.

**Proof.** `start_t(t)=E0`; Lemma 3 therefore forces the exact head and
Record mask. Raw descent along `i` contributes `c_i` at `E0`, so the
expanded successor `S` has `S(c_i)=E0`. Because this successor is expanded,

```text
S(z) <= d_I(c_i,z) = start_(c_i)(z)
```

on the start-child domain. Conversely, admissibility of `S` gives, for
every `z` in its domain,

```text
d_I(c_i,z) <= inv(S(c_i)) (+) S(z) = S(z).
```

This also proves that `z` belongs to the start-child domain. The other
domain inclusion follows by expansion from the entry at `c_i`. Thus the
profiles are identical. QED.

The original paired descriptor clauses give `d_I(q,t_q)=E0`, so
`start_q=start_(t_q)`. Lemma 6 therefore proves every original descriptor
equation, including shared children and mutually recursive equations,
simultaneously. It is not an independent reconstruction or default choice
at each use of a descriptor.

### Lemma 7: original inequalities

On the finite graph take all profile pairs `(S,T)` satisfying `S . T`.
Lemma 3 gives the required heads and Record mask inclusions. Lemma 5
supplies each required child pair, reversing negative coordinates and
identifying invariant children. Thus these pairs form a post-fixed
structural simulation. Every original inequality `s <= t` starts with
`start_s . start_t`, so `theta(s) <= theta(t)`.

One can retain the identity of each original inequality by starting a
separate signed simulation at its own endpoint pair and following only
that bound's required children. No bound is discharged by replacing it
with a quotient of other comparison identities. QED.

At this point `theta` is an unscoped regular solution. Permissions are
proved next; they are not assumed to be preserved by a representative
chosen for a merged state.

## 10. Rigid permissions: a same-address shadow

Say an arbitrary tree `a` realizes profile `S` relative to the original
solution `alpha` if

```text
d(a, alpha(t)) <= S(t) for every t in dom(S).               (Shadow)
```

If `a` realizes a raw profile, it realizes its expansion: every contributor
uses the sound inequality
`d(alpha(s),alpha(t)) <= d_I(s,t)`, followed by composition, truncation
and meet. This uses only the already fixed `alpha` and the soundness of
§4.2.

### Lemma 8: path shadow and permission preservation

For every original root `q` and every live path `w` in `theta(q)`, the
subtree `alpha(q)|w` exists and realizes the reached graph profile.
If the head selected there is a rigid identity `kappa`, that original
subtree is the identical atom `kappa`.

**Proof by induction on the finite path.** At the root the assertion is
soundness of `d_I(q,-)`. Suppose it holds at a reached profile `S`, with
shadow subtree `a`.

If `S` has a fixed-head anchor, finite connectivity forces `a` to have
that same head. Every selected child exists in `a`; necessary decomposition
from §4.1 shows that its actual child realizes each raw contribution, with
the appropriate variance or invariant equality. Hence that child realizes
the expanded successor.

If `S` has a Record anchor, `a` is a Record. For every selected field `l`
there is an anchor `t` containing it with `S(t) <= U`; therefore
`a <= alpha(t)` and mandatory width makes `l` present in `a`. For each
raw contribution at `l`, apply necessary Record decomposition to `a` and
that anchor. The rule depends on their distance bound and shared field,
so extra fields of `a` do not invalidate it. The actual child again
realizes the raw profile and then its expansion.

If the selected head is an atom, an atomic anchor exists. Any finite fence
to that discrete atom consists entirely of the same atom, so `a` is
identical to it. There is no next child. If `S` has no constructor anchor,
its selected `{}` may differ from the head of `a`, but has no children
and introduces no atom. Thus the path induction also terminates safely in
this case.

This proves the assertion at every finite live path. In particular every
rigid leaf of `theta(q)` occurs with the same identity at the same path in
`alpha(q)`. The latter is permitted at root `q`; hence so is the former.
The argument is repeated for **every root/path occurrence** reaching a
state, so a state shared across different permission sets satisfies all
of them. No common-permission or representative hypothesis is used. QED.

Rigid scope here means the existing per-root restriction on names occurring
anywhere in its tree. The proof preserves each such restriction separately,
including descriptor-owned root permissions already present in the package.
It introduces no fresh rigid identity and no permission-dependent carrier.

## 11. FMP, conflict reflection and the old boundedness residual

Lemmas 1–8 prove, for the fixed arbitrary permitted input solution `alpha`,
a permitted regular solution `theta` of the **same** package `P`. This
establishes Theorem FMP's regular-completion assertion with bound `8^N`.

Apply the existing complete regular-solution/finite-quotient equivalence:
the finite graph supplies regular root-domain, head, field-presence and
original activation predicates; a common finite monoid recognizing these
predicates supplies a finite surjective quotient model of `Gamma_P`.
The monoid must preserve the complete package, including descriptor-prefix
equations and domain/child coherence. That is exactly the reviewed
equivalence cited in §1, not a quotient of the head labels alone.

For the user's conflict-reflection statement, fix `P` and assume that all
finite surjective quotients are inconsistent. If its free least closure
had no finite conflict, the existing closure characterization would supply
an arbitrary permitted model. The theorem just proved would supply one
finite quotient model, contradicting the assumption. Therefore the free
least closure has a finite conflict. The quantifier over quotients never
changes the package.

The previously open BR from
[finite feedback quotients, §5](2026-10-04-structural-finite-feedback-quotients.md)
is consequently proved:

```text
for every fixed P,
  [for all n, r_P(n) is finite]
  => [there exists B such that for all n, r_P(n) <= B].
```

Indeed that note proves equivalence of BR with the same fixed-package FMP.
Equivalently, if no cofinal quotient has a model, reflection supplies one
finite free conflict derivation; its fixed feedback rank bounds all the
quotient first-conflict ranks. For a satisfiable package, a finite quotient
model exists and every sufficiently fine member of the cofinal tower has
one, so its ranks are eventually infinite. The construction does not
claim that arbitrary non-cofinal chains of failing quotients terminate.

## 12. Why this closes the prior obstructions

The old local signature folds lose child consequences of overlapping
anchors. Here the profile includes distances to **all original terms**,
and finite closure includes common-upper/common-lower consequences before
any state is shared. For example, two upper Records with an overlapping
field force a common lower of the two payloads via distance `L`; conflicting
payload heads are detected. A mere finite head signature would miss that
obligation.

The failed empty-side powerset construction kept its old comparison
invariant `(G)` after dropping nonempty lower/upper premises. Here an
unanchored child can use `{}`, but every selected Record child has an
upper-near landmark; §§7–8 use that landmark to prove precisely the
successor consistency and comparison cases that direct projection alone
does not supply. The seven distances retain information unavailable in
the old powerset invariant.

For the recorded `q=Function(X,R), X <: q` obstruction, `start_X` has
distance `U` to the Function term. Argument descent contributes `X:Dn`;
expansion through `X <= q` retains the Function anchor at distance at most
`Dn (+) U = L`. Thus this argument state cannot be treated as unanchored
or defaulted to `{}`. The finite-distance invariant explicitly retains the
one-sided variance dependency that the failed construction erased.

The graph is built jointly with exact successor identities from Lemma 6.
It neither selects a representative arbitrary subtree per state nor takes
an information meet of such trees. The only meet operation is on seven
finite numerical distance bounds. No residual-finiteness argument is used
to synchronize unbounded Horn stages. Instead a complete regular model is
constructed first, and only then is the reviewed quotient bridge applied.

What remains outside the result is whole-production source correspondence,
effect and joint predicate solving, and principal residual/factorization
questions. It also does not prove that the free **least** closure itself is
regular, or that a chosen length-cutoff/folding family eventually works.
None of these claims is needed for the requested FMP.
