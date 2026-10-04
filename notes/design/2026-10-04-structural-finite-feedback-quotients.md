# Finite feedback quotients and the exact remaining FMP premise

Date: 2026-10-04
Status: Reviewed mathematical theorem package; historical classification C, FMP/BR subsequently proved
Reviewed-by: two independent compiler-referee reviews and one focused coherence delta review
Scope: the existing normalized pure structural address Horn system
Base inspected: `be138584741a007e084aabe1c0e66641dac497b2`
Integration base: `8ddd2df276d5f6179a80c8e8610ac349e413d54f`
Implementation authority: none
Supersedes: none

Review and verification: [paired progress record](../progress/2026-10-04-structural-fmp-feedback-rank.md).

**Subsequent result:** [finite fence completion](2026-10-04-structural-fmp-fence-completion.md)
proves the full normalized pure structural FMP, including arbitrary rigid
permissions, and therefore proves (BR). The open-status and negative-target
statements below describe this earlier investigation. Its finite-feedback
theorems, exact rank equivalences and construction-specific counterexamples
remain valid. The later proof constructs a complete regular model directly;
it does not exchange the finite-horizon quantifiers here.

## 1. Classification and governing facts

**Classification C.** The unrestricted finite-model property is not proved,
and no fixed package refuting it is constructed. The new positive result is
a finite-feedback quotient theorem: every fixed finite number of head/activation
feedback rounds, with full domain coherence saturated, can be preserved by
one finite surjective monoid quotient. Its proof includes domain and child
coherence.

Consequently the remaining FMP premise can be expressed by one conditional
boundedness statement about the first-conflict ranks along a fixed cofinal
tower of finite quotients. All finite-stage quotients, their domain scaffolds,
and the quantifier reduction are proved below. The boundedness statement
itself remains unproved. This is an exact certificate localization, not a
claim that no further mathematical reduction is possible.

The input and relation are those of
[scoped structural projection, §§2 and 6](2026-10-03-scoped-structural-projection.md),
[scoped constraint solving, §§1–3](2026-10-03-scoped-constraint-solving.md), and
[open residual factorization, §§2–4](2026-10-03-open-residual-factorization.md):
identity atoms, mandatory Record width and covariant retained fields,
Function argument contravariance/result covariance, and the admitted fixed
constructors with declared variance. Exact descriptor equations and original
comparison identities are retained. Finite lexical rigid permissions remain
attached to their original tracks. No comparison transitivity is added.

The proof uses the reviewed results in these exact records:

1. [Least forced completion and the clash-free trace/unary correspondence](../progress/2026-10-03-open-residual-factorization.md#least-forced-completion-for-arbitrary-solutions-2026-10-04):
   the primitive positive rules, default-Record completion, regularity of
   each finite `F/G` alternation, and completeness of their union up to the
   first conflict.
2. [The complete finite-quotient equivalence and conflict-reflection gate](../progress/2026-10-04-direct-main-gate-attacks.md#exact-regular-completion-premise):
   regular solutions are equivalent to models over finite surjective monoid
   quotients of the complete address package.
3. [Structural S, §§5–8](2026-10-04-source-generated-callback-structural-theorems.md#5-structural-a-finite-source-generated-ledger),
   and [two-sided constructor bounds, §§2–7](2026-10-04-preclosed-structural-regular-witness.md):
   existing sufficient classes and their boundaries. Neither premise is
   imposed on the present result.

Fix one finite normalized package `P` and write its free-address Horn system
as `Gamma_P`. Its tagged finite child alphabet is `I`. Under the existing
closure characterization,

```text
Sat_I*(P)  iff  the free least closure has no finite conflict.
RegSat(P)  iff  exists finite surjective monoid quotient mu. Sat_mu(P).
```

Arbitrary `Guard`, joint `Phi/K,D`, effects, optional Records and concrete
adapter compatibility are outside this pure structural theorem. The result
adds no source-generation hypothesis. It also supplies no new bridge from
actual production Function/effect constraints to this pure projection.

## 2. Stages, complete coherence and conflict rank

Use the original root tracks and, for each original inequality `b`, its own
trace languages `A_b^+` and `A_b^-`. A trace is one word followed from both
original endpoints, with an orientation bit. An invariant coordinate supplies
both orientations; it never identifies endpoints or original inequalities.

Let `U` denote the forced head and Record-presence predicates. In the reviewed
notation:

```text
F(A) = complete unary saturation for the supplied activation languages A;
G(U) = root-seeded comparison-path closure under the supplied unary guards U.
```

`F` includes descriptor-prefix transport, same-word guarded head transfer,
upper-to-lower field transfer and `Present_l -> Head_Record`. `G` includes
arbitrarily long legal suffix descent, with the existing head/presence guards
and declared variance. Neither operation follows an absent or padded child.

Put `A_0` equal to the original root activations, let `U_0` be descriptor-only
unary saturation, and set

```text
U_(j+1) = F(A_j),
A_(j+1) = G(U_(j+1)).
```

The regularity claims below concern a free-conflict-free package. In that
case the stages are monotone and every finite stage is regular by the cited
trace/unary theorem. An unsatisfiable package is followed only up to its first
legal conflict; no expansion below an already contradictory head is used.

### 2.1 Expanding the already-required domain/head coherence

The old free-address `F/G` description cannot by itself be used as an
exhaustive fixed-quotient checker. A quotient may identify a root with a child
although the old liveness rules have not forced a head at the root. For
example, with the admitted restricted alphabet `I={arg,ret}`,
`q=Function(q,q)`, an independent free root `x`, and the one-element quotient,
`x` is live at both its root and its arg/ret addresses.
Choosing the empty Record there is invalid; a Function self-loop is valid.
This was the substantive defect in the first version of this note.

For the proof, make the complete package's domain/head/child coherence
explicit. A coordinate `c=Child(C,i)` is tagged by its fixed constructor;
Record field coordinates are separately tagged `l`. This is the existing
compressed active-domain encoding, with constructor-owned tags as specified
in [the preclosed witness signature, §2](2026-10-04-preclosed-structural-regular-witness.md#2-exact-signature-and-source-checkable-premise)
and [Structural S, §7](2026-10-04-source-generated-callback-structural-theorems.md#7-theorem-s-regular-completion-with-grounded-checks-and-one-open-anchor).
It is not a padded-domain or shared-numbered-coordinate interpretation.
Among the implications of coherent structural-tree domains are

```text
D_q(wc) -> D_q(w),
D_q(w Child(C,i)) -> H_q^C(w),
D_q(w l) -> Present_l(q,w),
Present_l(q,w) -> H_q^Record(w), D_q(w), D_q(w l),
H_q^C(w) -> D_q(w) and every declared child of C is live.
```

Retain the converse child restrictions: a forced atom has no children; a
forced fixed head has no coordinates outside its declared tagged children;
a Record has only field children and its field children are exactly its
present fields. Incompatible heads, forbidden exact-mask fields and forbidden
rigid identities are the existing denials. Descriptor transport applies to
`D`, heads and presence; every original activation and descent rule is kept.

These clauses are **logical consequences of the full domain/head/child
coherence already required in `Gamma_P`**, not new conditions on source
packages. A present tagged child in an actual structural tree determines
its parent's constructor family; a present Record child determines that
field's presence. They hold over free addresses and, by quotient lifting,
in every model of the complete package on every finite monoid. Adding these
entailed clauses for saturation therefore preserves exactly the models on
each fixed quotient. Call this explicit proof presentation `Gamma_P^coh`.
No compiler rule or new rejection criterion is selected.

Define `Fbar(A)` to saturate **all non-activation clauses** of this presentation,
including the domain implications above. Keep `G`'s original guarded
activation rules. On arbitrary quotients `Fbar` can force heads from live
children. It is not asserted to be the old liveness-only operation. On the
free stages generated from this fixed package's seeds, Lemma 1 below proves
that these extra coherence
implications add no new heads or presence: their antecedent children already
have the required forced-parent ancestry. Thus the reviewed free `U_j/A_j`
stages remain regular envelopes for this complete saturation.

On a finite quotient, a feedback round comprises `Fbar` saturation followed
by guarded `G` saturation, including immediate domain checks; descriptor-only
conflicts have rank zero. Saturations stop at the first legal conflict.
Write

```text
p_P(mu) = first round producing a conflict,
          infinity if no round produces one.
```

Changing whether a check at a round boundary is charged to that round or the
next changes ranks by at most a fixed indexing offset. Fix the convention
above throughout. No argument uses an exact numerical value at a boundary.

### Lemma Q: complete saturation on a fixed finite quotient

Each round terminates, because there are only finitely many positive facts.
If no conflict occurs, the monotone sequence stabilizes in finitely many
rounds at a set closed under all the clauses of `Gamma_P^coh`.

At any live state with no forced head, there is no live child: a live child
would force a head by the reverse coherence implications. Such a state can
therefore be assigned `Record{}`. At a forced Record state, the live field
children are exactly its forced present fields. At a forced ranked state,
the live children are exactly the declared ones; at a forced atom there are
none. The denials exclude all competing heads and forbidden children.

Construct a finite graph on the live pairs `(q,m)`, with these selected heads
and children `(q,m mu(c))`. Prefix closure and local child equivalence show
that its root unfoldings have exactly the domain predicates in the saturated
set. In particular every live class is reachable: choose a word representing
it, apply parent closure to all prefixes, and follow the resulting legal
children from the root.

Descriptor transport makes forced observations and their absence agree at
`(q,mu(i)m)` and `(q_i,m)` for every `m`; uniform defaults agree too. The graph
therefore satisfies every exact descriptor equation, mask and shared-root
reference. Its rigid leaves are all permitted forced rigid identities.

Every active pair has either the same forced head at both endpoints, by
head transfer, or no forced head at either. In the latter case both endpoints
are childless empty Records. In the former case width transfer and the
saturated `G` rules supply every required child comparison, with the original
orientation and bound identity. These active relations are direct post-fixed
structural simulations. Thus all original bounds hold, as do all the complete
domain/head constraints. The graph gives a model on the **same quotient**.
Conversely every quotient model respects each entailed rule and excludes
every denial. Hence

```text
p_P(mu) < infinity  iff  Gamma_P is inconsistent on mu.
```

The equivalence uses model conservativity of `Gamma_P^coh`, not an assumed
extension of the free-address defaulting argument. QED.

This rank counts mutual feedback. It does not count descriptor-rewrite
length, path length, primitive proof height, graph size, or source size.
One `Fbar` or `G` saturation can contain arbitrarily long finite derivations.

## 3. Finite-stage domain scaffolds

The quotient theorem must retain domain/child coherence, not only unary head
collisions. The following lemma supplies regular domain predicates at every
finite stage without adding default heads to the forced closure.

### Lemma 1: coherent regular completion of each unary stage

For a free-conflict-free `P` and every finite `j`, there are simultaneous
regular trees `T_j(q)`, with domains `D_j(q)`, such that:

1. every forced head/presence occurrence of `U_j` is reachable and has that
   observation in `T_j`;
2. every endpoint of a trace in `A_j` is in the corresponding `D_j`;
3. every original exact descriptor equation and exact mask holds in `T_j`,
   and every original rigid permission is respected;
4. `D_j(q)` is contained in `D_(j+1)(q)` for every track.

These trees need not satisfy all original inequalities. They witness legal
domains for a partial stage, not full satisfiability.

**Construction.** Start each track at its root. At a reachable address, retain
its forced atom or ranked head, or its forced Record head and exactly its
forced fields. If no head is forced, use `Record{}`. Presence already forces
a Record head, so an unforced-head default has no forced children. Recurse
only along the legal children of the selected head/mask.

**Reachability and monotonicity proof.** Induct simultaneously on stages and
on the finite unary derivations within each stage. Seeds are at live roots.
A transfer in `F(A_(j-1))` occurs only at an endpoint of a prior activation
trace. That endpoint was reachable in `T_(j-1)`. Old forced heads remain;
clash-freedom forbids changing one to a different head. Old forced fields also
remain. An old default was the empty Record and had no children, so replacing
it by a newly forced head can add children but cannot invalidate an old
path. This proves domain monotonicity at the same time as transfer liveness.

For descriptor transport `(q,iw) <-> (q_i,w)`, `i` must be an existing exact
child of `q`. Adding the prefix uses the seeded exact root head and child `i`.
Removing the prefix starts at the child track's live root. In either direction,
descriptor saturation transports the observations at **every proper ancestor
of `w`**, so the entire remaining path is reachable. This is not an inference
of reachability from an isolated deep fact. There is no such transport rule
for an exact absent field or an invalid ranked coordinate. A forced present
field adds a legal payload child. These cases exhaust unary generation.

Now `G(U_j)` starts at live roots. Each ranked transition is guarded by the
common forced head and follows a declared child; each Record transition is
guarded by forced presence at both endpoints. Thus every appended endpoint
is live in `T_j`. Reversing or duplicating orientation does not affect this
reachability argument. The newly reached child need not have a forced head.
This proves the activation invariant and completes the simultaneous induction.

**Exact equations.** Unary saturation equates all forced observations at
`(q,iw)` and `(q_i,w)`. Uniform defaulting therefore equates their canonical
heads/masks as well. The parent descriptor supplies child `i`; induction on
finite descendant depth, equivalently bisimulation, gives

```text
T_j(q)|_i = T_j(q_i),
D_j(q,iw) iff D_j(q_i,w).
```

Shared roots and guarded recursive equations are covered by this same
simultaneous argument. Every exact Record mask was positively seeded; an
additional forbidden field would already be a free closure conflict. All
rigid leaves come from forced rigid-head facts and obey their original track
permissions. Defaults introduce no rigid identity.

**Regularity.** Take a product DFA for the finitely many regular head and
presence languages in `U_j`. The product state, with the root track, determines
the selected canonical head/mask and all permitted outgoing coordinates.
Follow only those coordinates, using an absent sink for the others. This
finite graph presents `T_j`; the same graph recognizes `D_j`. This proves
regularity without assuming anything about the infinite union of stages.

The canonical default heads are used only in constructing these trees and
domains. They are **not inserted into `U_j`**. Moreover every live child in
`D_j` has a forced parent head (and, for a Record, a forced present field):
the construction gives no children to a default. Consequently `(U_j,D_j)`
satisfies all reverse-coherence implications of §2.1 using the forced
predicates alone. Forward child liveness, parent closure, descriptor transport
and exact child exclusions hold by construction. This is precisely why
`Fbar` on a free stage adds no missing shape information beyond its regular
envelope. It does not assert that liveness can never force a head on an
arbitrary quotient. QED.

## 4. Finite-feedback quotient theorem

### Lemma 2: simultaneous recognition transfers stage clauses

Let a finite family of address languages be recognized by one surjective
monoid homomorphism `mu : I* -> M`. Represent a language `L` by `mu(L)`.
Recognition means

```text
L = mu^(-1)(mu(L)).
```

Consequently membership at a quotient element means membership at **every**
representative, rather than just a selected occurrence. For each primitive
address Horn clause, choose one word `w` representing its quotient argument.
All its same-address premises hold at this same `w`, and

```text
mu(iw) = mu(i) mu(w),
mu(wi) = mu(w) mu(i).
```

Thus every such clause valid between the free represented predicates is
valid between their quotient interpretations. This includes joined premises,
descriptor shifts, suffix descent and denial clauses. Primitive descriptor
transport is used explicitly; arbitrary address-equality chains are not
silently compressed into new rules. The primitive package has no extra
word-equation antecedents or trace filters to be guessed.

### Theorem 3: every finite feedback horizon has a safe finite quotient

For every fixed normalized `P`,

```text
Sat_I*(P)  implies  for every k there is a finite surjective mu
                   such that p_P(mu) > k.                    (FH)
```

**Proof.** Compute the regular free stages through `k+1` and the regular
domain scaffolds of Lemma 1. Take one common transition monoid recognizing
all their head/presence, activation and domain languages, with every root,
original-bound identity and orientation kept distinct. Include the finite
root-seed languages. Restrict to the image of `I*`, so the homomorphism is
surjective. Products of finitely many DFA transition monoids are finite and
recognize all these languages simultaneously.

For each stage, interpret its predicates by their monoid images. The
represented `(U_(j+1),D_(j+1))` contains the unary/domain seeds and is closed
under `Fbar` with represented input `A_j`. In particular, every reverse child
implication holds in its forced heads/presence, by the last paragraph of
Lemma 1; default output heads are not needed for this closure. The represented
`A_(j+1)` contains its own root activations and is closed under `G` with
represented input `U_(j+1)`.
Lemma 2 proves these assertions on the quotient. Induction and leastness of
the finite saturations give

```text
actual quotient forced U_(j+1)  subset  represented free U_(j+1),
actual quotient A_(j+1)  subset  represented free A_(j+1).
```

Domain closure stays inside the appropriate represented `D_j` or `D_(j+1)`:
these contain root liveness and activation endpoints, are prefix closed,
satisfy descriptor-domain transport, and contain exactly the legal ranked
and forced-present payload children. Domain growth is monotone across the
phase boundary. A shape-forced quotient head also stays within represented
`U`: its live-child premise lies within represented `D`, whose corresponding
parent head or field is forced already. This explicitly handles quotient
collisions like §2.1's one-element example, rather than ignoring their shape
consequences. No default-head facts are introduced into `U`.

All stage predicates lie within the conflict-free free closure, and Lemma 1
supplies their legal shape. Head incompatibility, exact-mask violation,
forbidden rigid identities and incompatible child/domain requirements are
therefore absent. By Lemma 2 they remain absent on the represented quotient
stages. Denials have positive premises, so taking the actual smaller positive
closures cannot create a denial. No conflict occurs through the chosen
horizon. QED.

This is not representative folding. Its finite equivalence recognizes every
predicate of the chosen stages **in all contexts**; its monoid law preserves
both address actions. It overcomes joined-premise mixing at a fixed horizon
by saturation of whole fibers. It supplies no single finite equivalence for
all stages, and does not regularize the least closure.

## 5. Cofinal quotient tower and exact residual statement

List, up to labelled isomorphism, all finite surjective `I`-generated monoid
quotients with at most `n` elements. There are finitely many: multiplication
tables and the images of the finitely many generators are finite choices.
Let `eta_n : I* -> M_n` be the image of their product. The tower is refining,
and every finite quotient is a factor of `eta_n` for all sufficiently large
`n`. No decision-complexity or practical enumeration claim is made.

Put `r_P(n)=p_P(eta_n)`.

### Lemma 4: refinement and free conflict

If `nu` refines `mu`, a finite conflict derivation on `nu` maps to one on
`mu` with no larger feedback rank. Descriptor multiplication, original-bound
labels, orientations, seeds and primitive positive rules all commute with
the projection. If the coarser closure conflicts earlier, the inequality is
already satisfied; no derivation below that earlier conflict is needed. Hence

```text
p_P(mu) <= p_P(nu),
r_P(n) <= r_P(n+1).
```

A free finite conflict occurs by some finite feedback round, by the existing
finite-stage correspondence. Mapping that finite derivation gives a uniform
finite bound on `p_P(mu)` for **every** finite quotient.

Conversely, if `r_P(n)` is uniformly bounded by `B` but the free closure is
conflict-free, Theorem 3 gives a quotient `mu` with `p_P(mu)>B`. Cofinality
gives an `eta_n` refining it, so `r_P(n)>=p_P(mu)>B`, a contradiction. Thus

```text
free finite conflict  iff  sup_n r_P(n) < infinity.           (BC)
```

Also, a model on any finite quotient pulls back to a model on every finer
quotient. By cofinality,

```text
exists finite mu. Sat_mu(P)
    iff some r_P(n)=infinity
    iff r_P(n)=infinity for all sufficiently large n.          (FM)
```

### The single unproved premise

Combining (BC), (FM) and the existing closure characterization, FMP is
equivalent to the following statement, with `P` fixed inside its quantifiers:

```text
For every normalized P,
  [for every n, r_P(n) < infinity]
      implies
  [there is B < infinity such that for every n, r_P(n) <= B].  (BR)
```

Equivalently, conditional on **every** finite quotient of this one `P` being
inconsistent, their minimum conflict ranks are uniformly bounded. This is
the same exact missing conflict-reflection premise, now reduced to excluding
one numerical behavior: finite first-conflict ranks escaping to infinity
under cofinal refinement.

There are exactly three possibilities for a fixed package:

| Free / regular status | Behavior along the cofinal tower |
|---|---|
| Free-address inconsistent | `r_P(n)` is uniformly bounded and finite |
| A regular solution exists | `r_P(n)` eventually equals infinity |
| Free-address satisfiable, no regular solution | every `r_P(n)` is finite, but `r_P(n)` tends to infinity |

The third row is exactly the genuine-counterexample target. This note neither
constructs it nor excludes it. In particular, (FH) proves
`forall k exists mu`, while FMP needs `exists mu forall k`. No exchange of
these quantifiers is inferred from compactness, monotonicity or residual
finiteness.

One can construct a refining sequence safe through successively larger finite
horizons by taking products of the quotients in Theorem 3 and successively
more enumerated quotients. Each product is taken over its image. This does
not ensure that any member is safe for all future rounds.

## 6. Why an unconditional quotient-rank bound is false

The all-quotients-fail antecedent in (BR) cannot be removed or replaced by a
quantifier over only the quotients which happen to fail.

Consider this **one fixed regular-satisfiable package**:

```text
i = Int
q = Function(x,i)
b: x <: q.
```

It has the regular solution `x=q=T`, where `T=Function(T,Int)`. The same tree
at both endpoints gives a direct reflexive comparison. There are no Records
with fields and no rigid names. Its two-node `Function`/`Int` tree graph gives
a finite quotient model by the existing transition-monoid construction.

Write `a=arg`, `r=ret`. Suppressing only the displayed orientation bit, the
free stages are

```text
A_n = {a^j : 0 <= j <= n} union {a^j r : 0 <= j < n}.

U_(n+1):
  Head_Function(x) = {a^j : 0 <= j <= n}
  Head_Function(q) = {a^j : 0 <= j <= n+1}
  Head_Int(x)      = {a^j r : 0 <= j < n}
  Head_Int(q)      = {a^j r : 0 <= j <= n}
  Head_Int(i)      = {epsilon}.
```

The orientation at `a^j`, and at its result child, is positive for even `j`
and negative for odd `j`. Head transport works in both directions, so these
formulas respect Function contravariance. They follow by induction: the new
spine activation permits the next head transfer; descriptor transport adds
one `a` prefix on `q`; `G` then adds the next spine and result traces.

Let `T_N=I^{<=N} union {z_N}` be the length-cutoff monoid: concatenate while
the result has length at most `N`, and otherwise return its absorbing overflow
element `z_N`. This is a finite surjective quotient. The overflow symbol is
a monoid element, not a type or a new solver extremum.

Every such quotient is inconsistent for this fixed package. In the free
closure, `q` has Function at every `a^m` and Int at every `a^m r`. For `m>N`
both words map to `z_N`; their finite derivations map to the quotient and
give a head conflict there.

Nevertheless the minimum feedback rank of these conflicts is unbounded.
For any fixed horizon `k`, the displayed stage languages, their canonical
domains and their root seeds have bounded word length (at most `k+2` suffices
with the indexing above). Choosing `N>k+2` makes all their fibers singletons
on those supports and excludes overflow from the represented predicates.
The stage-transfer proof then preserves the first `k` rounds.

Thus

```text
exists fixed regular-satisfiable P.
  for every k, exists finite mu.
    k < p_P(mu) < infinity.
```

This disproves a bound on **all inconsistent quotients of every package**.
It does not disprove (BR) or FMP: the same `P` has a different, satisfying
finite quotient. The length-cutoff sequence alone is not cofinal in all finite
monoid quotients. Treating its universal failure as every-quotient failure
would reverse the required quantifier over quotient families.

## 7. Direct constructor-completion attack

The existing preclosed powerset theorem cannot be extended merely by allowing
empty bound sets while keeping its comparison lemma unchanged. This is an
obstruction to that specific theorem extension, not to FMP.

In that theorem, write

```text
L(A) = {s in T : some a in A satisfies s R a},
U(B) = {t in T : some b in B satisfies b R t}.
```

Its comparison lemma is

```text
L(A) subset L(C) and U(D) subset U(B)
    imply gamma(A,B) <= gamma(C,D).                          (G)
```

Take the regular-satisfiable package `x<=Int`, `y<=Bool`. Its finite closure
has `L({x})=L({y})=empty`. If empty-sided states were admitted, then
`g_x=gamma({x},empty)` and `g_y=gamma({y},empty)` would have identical empty
lower/upper profiles. (G) forces mutual comparison between them. It also
forces `rho(x)<=g_x` and `rho(y)<=g_y`, since the reverse upper inclusion
against the empty set holds. Original clauses require `rho(x)=Int` and
`rho(y)=Bool`. One proper structural tree would therefore be above both
distinct identity atoms, which is impossible.

This rules out retaining (G), independently of how default heads are chosen.
Tracking additional head information can avoid this particular contradiction,
but requires a new comparison invariant. Synthetic Function descriptors then
introduce child contexts such as `x/arg` and `x/ret` which need not be children
of any original flat term. No finite recycling theorem for those contexts
was established. Assuming their finite joint compatibility would assume the
regular-completion result rather than prove it.

## 8. Exact scope remaining after this earlier result

The new theorems establish fixed-quotient completion for the explicit,
model-conservative coherence presentation, finite-horizon quotient safety and
the exact bounded-rank/trichotomy reduction. They do not establish (BR), an effective
bound in the input size, a regular least closure, a full regular witness,
decidability of the unrestricted fragment, principality or full-fiber
projection.

A genuine negative result still has exactly this quantification:

```text
exists ONE fixed normalized P.
  Sat_I*(P) and
  for EVERY finite surjective monoid quotient mu, not Sat_mu(P).
```

No such package was found. The finite-stage proof makes its required behavior
more specific: along any cofinal refining tower its conflicts must be delayed
beyond every fixed number of mutual feedback rounds, while still occurring
at a finite round on each individual quotient. Long paths, nonstabilizing
free stages, failed representatives, or a non-cofinal family of failed
quotients do not suffice.

No assumption that production satisfies Structural S, the two-sided bound
predicate, or (BR) has been added. No new carrier, descriptor rule, Record
rule, variance rule, rigid-scope condition, rejection policy, existential
inference support or compiler implementation is selected.
