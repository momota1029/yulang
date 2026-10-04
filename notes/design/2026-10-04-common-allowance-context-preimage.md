# Common allowance: joint presentation and safe context preimages

Status: Reviewed limited mathematical results; principal-allowance realization open
Date: 2026-10-04
Scope: finite forward source presentations, exact complete-domain preimage laws, and the remaining principal-allowance representation and map obligations
Implementation authority: none
Supersedes: none

## 1. Result and remaining target

The user-directed
[principal scheme criteria](../progress/2026-10-04-principal-scheme-acceptance-criteria.md)
require a representable common allowance for every original solution and
factorization of every valid public view. This note proves forward
presentation and semantic universal-property results, and identifies the
additional *universal context-preimage* condition needed to turn them into
complete Function comparisons and admissible scheme instances.

It does not claim that the intended shared effect schemes are proved or
refuted. In particular, retaining a finite source relation is not itself a
proof of descriptor representability or of the required instantiation maps.
An arbitrary relation-valued object is not silently made a substitution value
for an existing effect variable.

Fix an original joint fiber `xi = (nu,K,D)` and its original solution set
`S_xi`. Preserve the full residual, scopes, type and effect endpoints, source
occurrences, request witnesses and dependent roots. If `a` is an admissible
public allowance in the existing descriptor language and `Q_xi(s,a)` denotes
all required *direct complete Function* checks and scope conditions, the
target remains

```text
forall s in S_xi. exists a. Q_xi(s,a),
```

together with

```text
forall valid public V. exists admissible m_V
    factoring V through the generated constrained presentation.
```

One map may depend on `V`. Neither a stronger `exists m. forall V` demand nor
a failure of literal row substitution is a counterexample to this target.
The permitted maps and complete descriptor interpretation matter.

## 2. Finite forward amalgams retain every old solution

Use the finite decorated immutable source envelope of
[Theorem C](2026-10-04-source-generated-callback-structural-theorems.md)
§§2.1–2.4, or another independently certified finite source relation with
the same joint-scope discipline. At an original solution `s`, write

```text
T_s = the complete source relation, with all required root/use views.
```

This denotes all finite generated observations, not one chosen execution.
Its intensional description is the original finite graph with `s` as a
parameter. Local primitive relation descriptions and decorations count
toward its size. Recursive references share registered labels.

Let `X` be its original complete tuple. For finitely many invocation
occurrences `j`, retain the existing typed projections `p_j` and the
relations they select. Define the derived amalgam `A_s` to be `T_s` with
these selected views retained. It is the same relation with named
projections, not a new solver value kind.

At a common request coordinate, an outward support view can be written

```text
Req_A(s,X,q) = or_j Req_j(s,p_j(X),q).
```

All disjuncts refer to the same `X`. If local witnesses must be hidden, bind
them once after joining their dependencies. Do not replace this by separately
chosen `X_j` witnesses. A repeated support point may be displayed once while
its original distinct occurrences remain in the residual.

### Forward-presentation theorem

The metatheoretic graph of the derived view

```text
E_xi = { (s,A_s) | s in S_xi }
```

has exactly `S_xi` as its forgetful image. Its view is described by a finite
source relation template and the original finite projection references.

**Proof.** For every `s`, interpret the supplied finite relation template at
that same `s`; its denotation `T_s` is a uniquely determined relation even
when it has infinitely many finite-history witnesses. Naming its existing
projections does not choose an execution, add a typing constraint, or alter
the old tuple. Thus `(s,A_s)` exists. Conversely membership of `E_xi`
retains the predicate `s in S_xi`. Finite description follows from the
constructor graph and finite set of projection references. QED.

This is totality of a *derived semantic view*. It is not yet
`forall s. exists a. Q_xi(s,a)`: `A_s` has not been shown to be an admissible
effect descriptor at every repeated public occurrence. Nor does a possibly
empty behavioral relation justify accepting an empty or invalid source
challenge fiber. Original admission obligations remain in `S_xi`.

### Source examples covered by this construction

| Source pattern | Joint relation retained |
| --- | --- |
| `call f x = f x` | The one complete invocation, including actual entry and the whole argument carrier. |
| `compose f g x = f (g x)` | The `g x` carrier joined to `f`'s Force/rebind/body/result consumer under one source tuple. Default full hygiene is still required by the source rules. |
| `twice f x = {f x; f x}` | Two distinct invocation occurrences composed by bind, with the second conditioned on the first's return and current state. |
| `higher f g x = f g x` | First-stage return joined to the second-stage callee through the same returned Function descriptor and latent roots. |

These are proof notation for the source-core graphs; the current raw HIR
does not implement those applications/blocks. In `higher`, currying the
outer declaration does not itself execute either inner stage; both occur
when its final body is entered. General branching such as `choose` needs
its independently specified source branch rule before this construction can
claim source conformance for that syntax.

The complete source image determines whether a request or suffix is reached.
An argument or first call can diverge before the next segment runs. A union
of naked local bounds cannot replace that sequencing relation. This is why
the complete tuple is retained throughout.

## 3. Safe universal context preimage

### 3.1 The exact image/preimage law

Hold the full shared assignment fixed. Let `I` be the space of complete
input/provider interfaces with their retained source and scope dependencies,
and `O` the approved complete typed observations. A source context denotes
a relation `T subset I times O`. Its image of `R subset I` is

```text
L_T(R) = { o | exists i in R. T(i,o) }.
```

For an independently given observation bound `V subset O`, define the
**universal** preimage

```text
U_T(V) = { i | forall o. T(i,o) implies o in V }.
```

Then

```text
L_T(R) subset V  iff  R subset U_T(V).
```

**Proof.** In the forward direction, take `i in R` and any `T(i,o)`. That
`o` belongs to `L_T(R)`, hence to `V`. In the reverse direction, take
`o in L_T(R)` and its original witness `i in R`; membership of `i` in
`U_T(V)` puts `o` in `V`. QED.

The full provider assignment is chosen once, before the source transition.
Repeated uses of a callable and intermediate latent values are coordinates
of this same relation. This proof does not distribute source execution over
unions of independently materialized row marginals.

### 3.2 Admission cannot be recovered from an empty image

An output inclusion alone omits the first half of complete Function
comparison. Write a public complete view as `V=(D_V,P_V)`, and let
`Adm_T(i,h)` be the independently generated predicate admitting challenge
`h` for actual input interface `i`. A challenge includes its source carrier,
provider and finite future-history dependencies; it is not just a value
type. Write `T(i,h,o)` for the complete observation relation.

Define

```text
U_T^safe(V) = {
  i |
  forall h in D_V. Adm_T(i,h)
  and
  forall h in D_V. forall o.
    T(i,h,o) implies o in P_V(h)
}.
```

The safe-preimage theorem is

```text
R subset U_T^safe(V)
iff
  (forall i in R. forall h in D_V. Adm_T(i,h))
  and
  (forall h in D_V.
     { o | exists i in R. T(i,h,o) } subset P_V(h)).
```

**Proof.** Apply §3.1 separately at every `h` and retain the independent
universal admission predicate. Expanding the two sides gives the same
quantifiers over `i,h,o`. QED.

This is the exact domain/observation condition from
[typed core §9](2026-10-02-typed-computation-core-elaboration.md), stated as a
predicate on complete provider interfaces. It covers every finite latent and
resumption history in `T`. No observed return is needed to admit a divergent
carrier; conversely, an inadmissible challenge does not become valid merely
because the output relation happens to be empty.

In this note, validity under this specific containment law is defined by the
right-hand side, independently of any generated scheme or query result.
The repository presents this law as a sufficient semantic route for complete
comparison. We do not assert that it characterizes every possible separately
justified adaptation accepted by endpoint-dependent resolution.

## 4. Why a finite positive graph does not finish this proof

The source generator gives a finite intensional description such as

```text
T(i,h,o) iff exists Z. F_G(i,h,o,Z).
```

If all of these displayed `Z` are eligible existential local witnesses, the
observation half of the safe preimage can be written

```text
forall h,o,Z.
  h in D_V and F_G(i,h,o,Z) implies o in P_V(h).
```

Together with the admission clause, this is a finite *written* expression.
It does not enumerate the infinite challenge or observation universes. With
rigid or alternating source binders, keep the original scoped membership
predicate `T` opaque in §3.2; do not apply this existential-only expansion to
move or flatten those binders.

Finite written syntax is not a proof that this predicate lies in the chosen
finite inference language. In particular, the positive graph language of
Theorem C and the ordinary existential relation operations do not supply a
general universal preimage operator.

### Finite separation example

Let

```text
I = {i},  O = {good,bad},  V = {good}
T0 = {(i,good)}
T1 = {(i,good),(i,bad)}.
```

Then `T0 subset T1`, but

```text
U_T0(V) = {i},     U_T1(V) = empty.
```

Every formula built positively from a variable relation atom `T`, fixed
predicates, conjunction, union and existential projection is monotone in
`T`. Structural induction on formulas proves this: each listed operation
preserves inclusion of its relation arguments. Universal preimage is
antitone in `T`, as the example witnesses. Therefore there is no uniform
positive expression in the variable `T` defining `U_T(V)` for all `T,V`.

This refutes the general inference from finite positive forward presentation
to uniform positive universal-preimage construction. It does not refute
Yulang principality, claim every fixed finite relation needs negation, or rule
out an existing complete Function atom representing the universal condition.
With a fixed explicitly finite universe one may enumerate observations;
source templates do not establish such an enumeration for all future clients.
Calling a missing universal condition a supplied "restriction predicate"
does not construct its representation.

## 5. Complete-contract joins and the domain condition

There is also a precise limit to the proposal "intersect domains and union
bounds." First suppose the contracts already share a challenge universe and
observation universe. Use the semantic containment preorder

```text
A <=sem B iff
  D_B subset D_A
  and forall h in D_B. P_A(h) subset P_B(h).
```

For a nonempty finite family `A_j`, define

```text
D_* = intersection_j D_j
P_*(h) = union_j P_j(h),     h in D_*.
```

Then `A_*` is their least common upper contract in this semantic preorder.

**Proof.** For each `j`, `D_* subset D_j` and `P_j(h) subset P_*(h)` on
`D_*`, so `A_j <=sem A_*`. If all `A_j <=sem B`, then `D_B subset D_*`
and every `P_j(h)` is contained in `P_B(h)` on `D_B`. Their union is too,
so `A_* <=sem B`. QED.

For a required original challenge set `Delta`, this construction retains
all those challenges **iff**

```text
Delta subset intersection_j D_j.
```

This follows directly from `D_*`'s definition; a nonempty intersection alone
is not enough. The preorder here compares semantic contracts. It does not
authorize transitively composing production concrete comparison successes.

Different source stages need not share their local challenge universe.
For example, in `higher f g x`, let `g` be Function-valued and `x` Int-valued,
with `f` receiving the former and returning a Function receiving the latter.
Identifying both local carrier coordinates before intersecting domains would
require one returned value to have incompatible Function and Int heads,
although the two-stage source call has ordinary admissible executions.

Instead retain the actual source tuple and typed projections
`p_j : X -> Challenge_j`. The legitimate joint domain condition is

```text
RequiredSourceTuples subset intersection_j p_j^-1(D_j).
```

Similarly, combining observations requires their existing source-typed
context maps, including pending suffixes, rather than an invented identification
of local observations. This separates a valid semantic join theorem from an
unproved installation of that join at repeated abstract Function ports.

## 6. The two remaining realization obligations

The positive forward result in §2 and the safe-preimage equivalence in §3
leave a concrete representation problem, with two parts.

### 6.1 Complete-port representation

Source elaboration must give the completed checked interfaces `B_j(s,a)`
and the allowed abstract-component interpretation at their original typed
paths. A sufficient route is to represent the safe-preimage relation by the
existing direct complete Function query/evidence relation:

```text
admissible complete-query evidence for the generated interfaces
iff
membership in U_T^safe(V).
```

Here the source translation, domain rules, endpoints, scopes and original
evidence must be specified on both sides. This is a target equivalence for
this containment-based proof route, not a proved statement about the current
resolver or a necessary restriction on every alternative sound adaptation.
If the existing query atom has this meaning, its universal condition can
remain in the original finite residual; no new logical constructor or
independent effect-subtyping relation is needed.

Soundness alone gives at most one direction. All-view completeness requires
that an independently valid view not be lost by the generated query. Merely
writing `A <: B` in a residual does not prove its completed port interpretation.
The source-indexed
[callback reference realization](2026-10-04-source-indexed-callback-realization.md)
constructs whole generated bounds for its linked case; it does not supply
this general abstract-component or comparison-completeness theorem.

For fiber-total common allowance, the derived `A_s` must additionally have
one admissible descriptor realization `a_s` with the required source-owned
occurrence maps. That realization must preserve the original required
challenges and establish every **direct** complete Function check. Section
2's derived relation alone does not prove such an `a_s` exists.

### 6.2 Admissible scheme maps

An extensional relation inclusion or an arbitrary relational witness map is
not automatically an admissible type-scheme instantiation. For every valid
finite public presentation `V`, the proof must construct the allowed `m_V`,
including the old constrained presentation's local identities and scopes,
and show it commutes with the completed occurrence maps and preserves the
original joint residual.

[Parametric linking](2026-10-02-parametric-component-linking.md) §2 requires
multiple occurrences of one port to use the same substitution target.
[Concrete compatibility](2026-10-03-concrete-compatibility-boundary.md),
under "Necessary conditions from the intended Function cases," also says
sharing an effect term does not equate events or require exact input/output
support equality. These requirements are compatible: one target can have
distinct already-defined source views. They do not license assigning a fresh
effect variable an arbitrary tuple of stage relations and inventing a selector
for each occurrence.

Thus a construction using one common root must exhibit that single admissible
target and its existing, uniformly transported paths. Alternatively a direct
completed subsumption check may witness a valid public view. The proof must
use the actual allowed map/evidence class, rather than demand equality by
literal row substitution or assume arbitrary relation maps are allowed.

The existing whole-presentation generalization/reindexing theorem transports
a supplied finite presentation exactly. It does not itself construct these
maps or prove every public view is represented. In particular, pointwise
existence of a descriptor for each solution does not supply one syntactic
`m_V` for a whole public solution family.

## 7. What a completed proof would now have to do

For a finite source component, retain its original residual and source graph,
and emit fresh public allowance coordinates with their completed direct
Function constraints. If §6.1 supplies each `a_s`, choose that witness for
each old `s`; the retained original residual gives the reverse projection.
This proves `forall s in S_xi. exists a. Q_xi(s,a)` without equating old
effect endpoints or selecting one regular model.

For each independently valid public `V`, §3 turns complete validity into
safe-preimage membership. If §6.1 represents that membership and §6.2 gives
the admissible map realizing it for the whole presentation, `m_V` witnesses
the required factorization. Existing whole-presentation renaming then
preserves the result at independent uses.

The quantifiers stay `forall s exists a` and `forall V exists m_V`. The
remaining obligations concern complete-port/descriptor realization and
admissible maps; positive forward finite presentation and the semantic
preimage equivalence are proved here. This is a sharper localization of
one proof route, not a claim that every possible proof must use it or that
the source language has a counterexample.

The seven accepted public schemes remain acceptance criteria. In particular,
the Read/Write two-stage example does not refute their principality: a single
wide allowance can sometimes reach a tighter public view through one direct
higher-order comparison with argument contravariance. A proof excluding all
allowed maps would be required for a genuine negative result.

The pure structural FMP theorem supplies regular witnesses for its own
normalized pure fragment. It supplies neither the `a_s` realization nor the
`m_V` maps above. No new carrier, descriptor semantics, existential source
types, rejection rule or compiler implementation is introduced by this note.

## 8. Review record

Independent read-only compiler-referee and specification-auditor reviews
(M3, 2026-10-04) found no blocking, major or minor defect in this note's
limited mathematical and conformance claims. Both reviewers expressly
retained the descriptor-realization and admissible-map obligations; the
full principal/common-allowance gate remains open. See the
[follow-up record](../progress/2026-10-04-callback-principality-direct-followup.md)
for the combined result and exact review scope.
