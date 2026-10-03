# Open residual factorization for scoped regular constraints

Status: Reviewed
Date: 2026-10-03
Scope: candidate factorization theorem for open structural bounds after scoped rational equality quotienting
Reviewed-by: compiler_referee and spec_auditor (M3, 2026-10-03); initial structural-outcome repairs, conditional factorization-lemma review, and operation-instance context delta found no remaining findings in reviewed scopes; bounded compiler_referee delta review of §7.1's one-class atomic-Record fiber found no findings; bounded compiler_referee and spec_auditor review of §7.2's closed-regular-endpoint shape-and-field fiber found no findings; bounded compiler_referee and spec_auditor review of §7.3's closed structural interval inhabitation found no blocking/major findings, and its minor Record-arity wording ambiguity was repaired by primary inspection
Implementation authority: none
Supersedes: none

## 1. Purpose and boundary

The [scoped constraint-solving package](2026-10-03-scoped-constraint-solving.md)
closes equality quotienting and closed structural comparison, but leaves open
flexible heads and Record extensions as residual bounds. This note proposes a
principal constrained presentation for that fragment. It does not claim an
effective decision procedure for arbitrary open bounds or complete source
inference.

The governing authority remains the [SCC intrusion redesign charter](2026-09-29-scc-intrusion-redesign-charter.md),
especially its requirements to retain joint constraints, lexical binder
identity, principality, and scope checks. This is a theorem candidate within
the finite contractive regular structural fragment of the two packages above.
It selects no source rejection rule, public scheme syntax, resource bound, or
implementation architecture.

## 2. Input package

Let a finite input package be

```text
C = Eq ∧ B ∧ Perm ∧ Guard ∧ Phi
```

where `Eq` is rational regular-constructor equality, `B` is the set of
structural subtype clauses, `Perm` gives each flexible class its permitted
rigid-name set, `Guard` records generation-time scope checks, and `Phi` retains
the original joint symbolic coordinates, including `K,D` and request-witness
identity. Equality quotienting produces a finite guarded descriptor graph
`Q`, a root map `q`, free classes `F`, and propagated permission sets. Each
scope-respecting assignment `eta : F -> Reg` has a unique guarded extension
`eta_hat_Q` to descriptor nodes, modulo regular-tree bisimulation.

All query guards are recorded before structural head inspection. A guard
failure remains a distinct outcome; it is never reinterpreted as a structural
head mismatch or a semantic disequality.

## 3. Finite normalization and residual graph

Normalize each structural bound on the fixed quotient with a canonical
worklist of ordered node pairs. A state is `(b, j, u, v)`: original bound
identity `b`, its immutable guard/evidence context `j`, and quotient endpoint
identities `u,v`. Alias merging cannot split one obligation into independently
chosen copies. Each derived child keeps `b` and inherits `j`; do not mint a
new provenance identity for each recursive path. If the governing source
relation gives a child a different guard context, that context becomes its
`j` and remains part of the state key.

For each pair, first apply the package's generation-time scope guard. Then:

- matching primitive atoms discharge the pair;
- matching rigid atoms discharge only when binder identities are equal and
  admitted by the selected scope discipline; spellings and depths do not
  identify rigid binders;
- if either endpoint is a descriptor-free flexible class, retain the pair as
  an open residual edge;
- for matching known Function heads, enqueue the contravariant argument and
  covariant result pairs;
- for matching known Record heads, require every upper Record label in the
  lower Record and enqueue only those field pairs;
- for matching declared-variance constructors, enqueue the same or reversed
  child pairs as declared, and both directions for invariant coordinates;
- for distinct known heads or a missing required Record label, report failure
  of that structural clause, subject to the earlier guard result.

Memoize each pair before expanding its children. The quotient graph is finite,
so each pair is expanded at most once and recursive descriptor feedback closes
through graph back-edges. Do not infer equality from mutual profile equality
or discard an original invariant endpoint. Keep `Guard` and `Phi` correlated
to their original roots through `q`.

Normalization has three outcomes:

```text
GuardFailure(g) | StructuralFailure(b, pair) | Success(R)
```

Check each queried or derived pair's scope guard before its local structural
rule, including on recursive back-edges. A `GuardFailure` remains a distinct
scope outcome and is not converted into a structural unsatisfiability claim.
A `StructuralFailure` is a failed mandatory local condition after that pair's
guard admitted it; for the input structural clause it proves there is no
structural solution. `Success(R)` contains the finite conjunction of open
residual edges and the descriptor-determined comparisons discharged by
normalization. The factorization below applies only to `Success(R)`.

An edge with a flexible endpoint stays a structural comparison under its
recorded guard/evidence context over the full regular assignment. That
residual judgment rechecks the same scope guard on every comparison it derives.
In particular, `X <= {}` remains one residual edge and ranges over every
finite-label Record assignment to `X`; the normalizer does not choose a Record
skeleton or invent row variables.

## 4. Candidate principal factorization

For an assignment `eta` to the free classes, interpret all residual edges
using the same regular graph `eta_hat_Q`. Conditional on
`Normalize(Q,B,Guard) = Success(R)`, the proposed factorization is:

```text
Sol(C) = {
  eta_hat_Q composed with q |
  eta satisfies Perm_Q and
  eta_hat_Q satisfies R ∧ Guard_q ∧ Phi_q
}
```

The equality quotient contributes the relative most-general factorization
already stated in the scoped equality package. For each subtype clause,
normalization preserves its meaning: a structural rule is equivalent to its
required child comparisons; Record width is equivalent to the required upper
labels and their field comparisons; and a bound with an unresolved flexible
head is retained without weakening. Replacing each clause by these equivalent
conditions in a finite, memoized graph therefore preserves the full solution
set. Conversely, a satisfying residual assignment witnesses each retained
open boundary pair, while the discharged descriptor comparisons have already
passed their local and recursive obligations. This gives the claimed
factorization for every admitted assignment, including productive recursive
feedback, modulo bisimulation.

The claim is principality of a **constrained residual presentation**. It does
not claim that the residual bounds are satisfiable, that a contradiction
between open bounds is decidable, or that any client language already exposes
this presentation as a public scheme.

### 4.1 Normalization equivalence lemma (candidate proof)

Fix a successful equality quotient `Q`, an assignment `eta` respecting its
permissions, and one original bound `b`. Let `P_b` be the finite set of
reachable states `(b,j,u,v)` discovered by normalization, `R_b` its flexible-
head terminal states, and `D_b` its descriptor-known states. Let `S_eta` be
the greatest structural subtype relation on the instantiated regular graph;
scope guards are checked at every pair under the state context `j`. For a
residual state, `S_eta` means the full guarded judgment retained on that
boundary, including its recursive comparisons. Then, conditional on all
guards being admitted,

```text
eta satisfies the original bound b
iff
eta satisfies every residual state in R_b.
```

For the forward direction, suppose the root interpretation is in `S_eta`.
Because `S_eta` is a fixed point of the structural simulation operator,
membership of a descriptor-known pair forces membership of every required
successor. Induction on finite discovery-path length therefore puts every
reachable residual terminal in its retained guarded judgment. This is
reachability induction, not induction on recursive type depth; repeated
back-edges are already states in `P_b`.

For the reverse direction, assume every residual terminal passes its guarded
judgment. Form the relation consisting of `S_eta` together with the interpreted
pairs of every state in `D_b`. Each added Function pair has its reversed
argument and ordinary result successors; each Record pair has every required
upper-label successor; each declared-variance pair has exactly its same,
reversed, or invariant-both-direction successors. Identical admitted atoms
are nullary successes. Every successor is either another pair in `D_b` or a
residual terminal already in `S_eta`. Thus the augmented relation is
post-fixed, so greatestness places every added pair, including the original
root, in `S_eta`. This also covers recursive descriptor feedback without
unfolding.

If normalization finds a local descriptor mismatch or missing Record label,
the forward argument shows `StructuralFailure(b,pair)`: any valid root would
force the offending reachable pair into `S_eta`, contradicting its local
condition. A `GuardFailure` is outside this equivalence and makes no
structural-unsatisfiability claim. Applying the lemma to every `b` and
combining it with the reviewed equality-quotient factorization gives the
solution-set equation above, while `Phi` and its original endpoints stay
unchanged.

Finiteness is conditional on stable finite evidence contexts. With `N`
quotient nodes and `J` possible immutable contexts per original clause, there
are at most `|B| |J| N^2` states; finite constructor arities and finite Record
label sets give finite successor work. The intended simplest case is one
inherited `j` per original clause. The design packages do not yet prove that
every source-generated comparison has this stable-context property; it
remains an explicit premise and source-generation obligation.

The [operation-instance package §8](2026-10-02-operation-instance-binding-package.md)
partially supports inherited contexts for its finite acyclic unsealed equality
construction: deferred comparisons retain their generating lexical context,
and the common comparison entry invalidates and requeues checks when aliases,
levels or dependencies change. Separate sibling openings retain distinct
identities. This does not establish a finite `J` for every source-generated
subtype comparison, sealed packet lifecycle, or the complete source solver;
those remain outside this conditional lemma.

## 5. Composition with projection summaries

For every satisfying `eta`, compute the scoped structural projection summaries
on the entire instantiated quotient:

```text
Sigma = Proj_H(eta_hat_Q)
```

where `Proj_H` is the greatest-fixed-point construction from the reviewed
scoped structural-projection package, with its invariant coordinates retained
on original endpoints. `Sigma` is a uniquely derived view of the same
assignment, not a separately instantiable solution port. This prevents an
alias, recursive dependency, or two occurrences of one class from receiving
independently guessed profiles.

For eligible clauses with visible targets, the prior root-factorization
theorem may then be applied under its stated premises. Original `Eq`,
`K,D/Phi`, endpoint identities, and scope evidence remain attached to the same
assignment. This composition establishes semantic correlation of the views;
it does not yet provide a finite effective symbolic solver for `R` together
with `Sigma` when unknown Records and feedback vary across assignments.

## 6. Correlation witnesses

Independent per-bound solutions are not a principal joint presentation. For
example:

```text
Eq(X,Y),  X <= {f:Int},  Y <= {f:Bool}
```

Each bound alone is satisfiable, but the shared field would need to subtype
both distinct atoms. The equality quotient must identify `X` and `Y` before
joint residual acceptance; checking each edge independently invents a
spurious solution.

Likewise, projection profiles cannot be chosen as arbitrary Boolean fixed
points. For the productive equation `X = Function(X,Int)`, multiple Boolean
fixed points need not be the profile of the represented regular tree. The
projection must be the specified greatest-fixed-point semantics of that
whole tree. Original invariant coordinates cannot be reconstructed from
profiles unless the relevant predicate is constant on projection fibers.

## 7. Exact remaining obligations

Before this candidate can be treated as a closed theorem package:

1. Establish from the source judgment that guard/evidence contexts are stable
   and finite along derived comparisons; the bound above is conditional on
   this fact.
2. Prove that failure reporting distinguishes a disproved structural clause
   from a scope-guard failure and does not turn either into an unauthorized
   source-level rejection.
3. Define an effective satisfiability procedure, or retain the residual
   judgment without claiming acceptance completeness. The factorization above
   alone leaves contradictory open bounds unresolved.
4. Construct a finite effective joint representation of projection
   summaries, unknown Record labels, aliases, and feedback. Closed-import
   profile branches alone do not discharge this obligation.
5. Establish the source-generation and uniform scoped-typing bridge. The
   fixed-strategy uniform-parent result does not establish that bridge or
   finite source syntax.

### 7.1 Exact structural fiber for one atomic-Record class

This subsection closes a bounded structural satisfiability case after a fixed
successful equality quotient. It is not a source rejection rule or an
effective solver for the full residual package. Let one descriptor-free class
`X` have supplied, immutable bound contexts and constraints

```text
L_i <= X        (i in I_L)
X <= U_j        (j in I_U)
```

where every `L_i` and `U_j` is a finite mandatory Record with unique labels,
and every field value is a primitive atom or a rigid atom compared only by
identity. Ignore `Perm`, guards and `Phi` for the structural fiber in this
subsection; conjoin them on the same witness below. Define

```text
U = ⋃_{j∈I_U} labels(U_j)
```

Every upper occurrence of one label `f` must have the same atom; call it
`u_f`. When `I_L` is nonempty, also define

```text
I = ⋂_{i∈I_L} labels(L_i)
A = { f∈I | all L_i(f) are the same atom }
```

For `f∈A`, call that common atom `a_f`. The unguarded structural conjunction
has a solution exactly when upper occurrences agree for every `f∈U` and, if
lower bounds exist, `U⊆A` with `u_f=a_f` for every `f∈U`.

Its complete structural fiber is:

- If lower bounds exist: `X = Record(D,t)` where `U⊆D⊆A` and `t(f)=a_f`
  for every `f∈D`.
- If there are no lower bounds: `X = Record(D,t)` for any finite `D⊇U`,
  with `t(f)=u_f` on `U`; every field in `D\U` has an arbitrary
  contractive regular assignment in the declared structural domain.
- If there are no bounds: every assignment in that regular domain, including
  non-Records.

For necessity, any supplied Record bound forces `X` to have a Record head.
Each `L_i<=X` requires every selected label of `X` to occur in every lower
record and requires `L_i(f)<=t(f)` at that label. Identity-only atomic
comparison gives `D⊆A` and `t(f)=a_f`. Each `X<=U_j` requires all labels in
`U_j` to occur in `X` with the same atom, yielding `U⊆D`, upper agreement,
and (when there are lower bounds) `U⊆A` and `u_f=a_f`. Conversely, when
these conditions hold, `D=U` with fields `u_f` witnesses structural
feasibility; all other assignments listed in the fiber satisfy the same
width and identity checks. A finite acyclic record is contractive.

In particular, lower-field disagreement only forbids selecting that field
into `X`; it is not a contradiction unless an upper bound requires it. Thus
`{f:Int}<=X` and `{f:Bool}<=X` admit `X={}`. Conversely,
`X<={f:Int}` and `X<={f:Bool}` conflict on required `f`. An empty lower
record forces `D=∅`, so it conflicts with any nonempty required upper. With
no lower bounds, `X<={}` has `U=∅` and admits every finite Record extension,
including arbitrary contractive regular fields; choosing `{}` proves
existence but is not the entire fiber.

The full joint condition remains the intersection of this structural fiber
with the original permissions, bound guards, and `Phi`/`K,D` predicates on
one assignment. `Guards(T,ω)` checks every original bound guard and each
child-comparison guard reached while evaluating that assignment in its
original immutable context:

```text
∃ T in StructuralFiber, ω:
  Perm_Q(T,ω) ∧ Guards(T,ω) ∧ Phi_q(T,ω)
```

This does not assume `Phi` satisfiable, nor that separate structural and
symbolic witnesses can be combined. Guard failure remains `GuardFailure`;
permission failure is not an atomic mismatch; report structural contradiction
only after relevant guards admit the comparisons. An unguarded structural
witness does not establish a permitted or fully joint witness. This lemma
does not generate replay tasks, alter the fixed quotient, eliminate
projection summaries, or authorize source rejection. Optional Records,
non-identity atom subtyping, nested flexible fields, multiple interacting
open classes, effects, Functions, casts, feedback and effective `Phi` solving
remain outside it.

Effectful Function and operation compatibility, declared bounds, typed-family
transport, lifecycle/generalization/freshening, full acceptance, termination,
and resource limits remain later gates. The compiler implementation remains
unauthorized.

### 7.2 Shape-and-field fiber for closed regular Record endpoints (candidate)

This extension replaces the atomic-field premise of §7.1 with fixed regular
field endpoints. It remains inside the pure structural relation of
`scoped-structural-projection.md`; it adds neither an effective field solver
nor a source rejection rule. Fix the successful equality quotient and one
descriptor-free class `X`, with finitely many bounds

```text
L_i <= X        (i in I_L)
X <= U_j        (j in I_U)
```

Every `L_i` and `U_j` is a finite mandatory Record with unique labels. Every
field endpoint is a fixed contractive regular graph in the scoped structural
fragment, with no unresolved flexible class. Define

```text
U = ⋃_{j∈I_U} labels(U_j)
I = ⋂_{i∈I_L} labels(L_i)           when I_L is nonempty
F_f = { t ∈ Reg |
       L_i(f) <= t for every lower record containing f,
       t <= U_j(f) for every upper record containing f }
```

The bounds in `F_f` are exactly those contributed by the supplied records;
an empty family on one side adds no obligation. The complete unguarded
structural fiber is:

```text
at least one bound:
  X = Record(D,t), D finite, U ⊆ D,
  D ⊆ I when lower bounds exist,
  t(f) ∈ F_f for every f ∈ D

no bounds:
  X is any graph in Reg, including non-Records
```

When lower bounds exist, put `A = { f ∈ I | F_f ≠ ∅ }`; the allowed shapes are
exactly `U ⊆ D ⊆ A`, provided every required `f ∈ U` has nonempty `F_f`.
With no lower bounds, every finite shape `D ⊇ U` is allowed provided required
cells are feasible; fields in `D \ U` have arbitrary regular values. Thus
structural existence is equivalent to `U ⊆ I` and nonempty required cells
when lower bounds exist, nonempty required cells with upper bounds only, and
automatic inhabitation of the declared domain when there are no bounds.
This is a nonemptiness criterion, not an effective procedure for deciding
`F_f`.

For necessity, Record width forces `U ⊆ D`, and each lower Record forces every
selected label into `I`. Covariant depth supplies exactly the field
obligations listed in `F_f`. For sufficiency, choose `D=U` when there is an
upper bound and select one witness from each required `F_f`; if there are
lower bounds, `U ⊆ I` supplies the width conditions on every lower. The
original structural clauses then hold directly by Record width and field
comparison. No comparison between two endpoints through `X` is generated,
and no concrete-success transitivity is used.

Fixed recursive endpoints do not add unknowns: each field graph denotes its
regular tree. A selected candidate field may itself be recursive or share
graph nodes with another field; finite disjoint copies of its rooted regular
graph still assemble a contractive Record. Graph-sharing identity has no
structural meaning beyond unfolding/bisimulation in this fragment. This
argument stops applying if endpoints contain unresolved `X` or another
flexible class, identity-sensitive evidence, or constraints requiring
cross-field sharing. Permissions, guards and `Phi` may also couple otherwise
independent fields; the full fiber remains their conjunction on the same
assembled assignment:

```text
∃ T ∈ StructuralFiber, ω:
  Perm_Q(T,ω) ∧ Guards(T,ω) ∧ Phi_q(T,ω)
```

This theorem characterizes Record shape and field obligations. It does not
decide those field obligations, eliminate the joint predicates, imply that
source-generated packages meet its closed-endpoint premise, or authorize a
source-level rejection. Empty required cells remain structural obstructions
only after their original guards admit the comparisons.

### 7.3 Finite inhabitation of a closed structural interval (candidate)

This subsection gives an effective test for the **unguarded structural
nonemptiness** of a field fiber `F_f` from §7.2. It does not decide the full
intersection with permissions, guards, or `Phi`; a structural witness that
fails one of those predicates cannot establish that the full intersection is
empty. Work in the pure regular structural grammar of
`scoped-structural-projection.md` §§2 and 6. Endpoints are finite, closed,
contractive regular graphs after the fixed equality quotient, and the
underlying structural relation compares atoms by identity. There are no
flexible endpoints, optional Records, effects, casts, adapters, identity-
sensitive graph constraints, `Top`/`Bottom`, unions, or intersections.

Let `V` be the finite set of endpoint graph nodes, including all reachable
constructor children. A state is a pair of subsets:

```text
S = (L,U),       L ⊆ V, U ⊆ V
Meaning(S) = { t ∈ Reg | a <= t for every a∈L, and t <= b for every b∈U }
```

There are at most `4^|V|` states. For each state, either its local head
condition fails or it has a finite set of required child states:

| State endpoints | Local condition and successor states |
|---|---|
| `L=U=∅` | Choose `{}`; no successors. |
| Nonempty endpoints with different root heads | Fail. |
| Atom endpoints | Every endpoint is the same atom; no successors. |
| Function endpoints | Argument `(U.arg,L.arg)`; result `(L.result,U.result)`. |
| Constructor `C`, `+` child | `(L.child,U.child)`. |
| Constructor `C`, `-` child | `(U.child,L.child)`. |
| Constructor `C`, `=` child | `(L.child∪U.child,L.child∪U.child)`. |
| Record endpoints | Choose labels `D=⋃_{b∈U} labels(b)`. If `L` is nonempty, require `D⊆⋂_{a∈L}labels(a)`. For each `f∈D`, require `({a(f):a∈L},{b(f):b∈U, f∈labels(b)})`. |

Every nonempty endpoint set must have the same root head. Functions and
fixed-arity declared constructors must also have the same arity, after which
the table applies coordinate-wise. Record label counts may differ; their
width conditions are handled by the Record row. Invariant coordinates
deliberately put every incident endpoint child on both sides. At a Record
state, lower width requires each chosen label in every lower record, while
upper width requires every upper label in the candidate. Choosing their union
is sufficient for structural existence: extra candidate fields add lower
obligations and satisfy no new upper obligation. This minimal-shape choice
does not claim that extra fields are absent from the complete fiber in §7.2.

Build the finite state graph reachable from the initial interval. Let
`Good(S)` be the greatest fixed point of local validity and survival of every
required child state:

```text
Good(S) = locally_valid(S) ∧ ∀ child S'. Good(S')
```

It can be computed by removing locally invalid states and propagating removal
to predecessors. For every surviving state, construct one witness node with
its prescribed head and edges to its surviving child states. Every cycle
passes through a Function, Record field, or constructor edge, so the result
is a finite contractive regular graph.

**Exactness.** For soundness, place `(a,w_S)` for `a∈L(S)` and `(w_S,b)` for
`b∈U(S)` in one simultaneous structural simulation. Each table row expands
these pairs to exactly its required child pairs; invariant coordinates add
both directions. Thus a surviving state has a witness in `Meaning(S)`. For
completeness, any witness `t∈Meaning(S)` validates the local head condition.
At a Record state, its required fields witness every union-label successor;
at Functions and declared constructors its children witness the listed
successors. The set of inhabited states is therefore post-fixed and is
contained in the greatest fixed point. No proof step compares an element of
`L` directly with an element of `U` by composing their separate successful
comparisons through the candidate `t`.

Consequently, for §7.2 the unguarded structural fiber is nonempty exactly
when every required Record label has an inhabited interval state and the
Record shape inclusions hold. This decides structural existence and produces
one structural witness. It does not preserve the entire candidate-field
fiber after external `Phi`, guard, or permission predicates are conjoined;
another structural witness may satisfy those predicates. Keep the complete
fiber and the same-assignment joint condition when checking them. Any resource
cutoff for the exponential state space needs a separate approved boundary;
this theorem chooses no limit or rejection behavior.

## 8. Verification direction

After the full theorem package is repaired and reviewed, a finite exhaustive
model check may exercise small regular graphs and compare the original clauses with the
normalized residual graph. Include the alias contradiction above, `X <= {}`
with Records of several label sets, permitted-name intersections across
aliases, productive recursive equality, and guarded recursive subtype pairs.
Such checks would support the proof; they would not replace it. No tests,
builds, or measurements were run for this draft.
