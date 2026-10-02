# Open residual factorization for scoped regular constraints

Status: Reviewed
Date: 2026-10-03
Scope: candidate factorization theorem for open structural bounds after scoped rational equality quotienting
Reviewed-by: compiler_referee and spec_auditor (M3, 2026-10-03); initial structural-outcome repairs, conditional factorization-lemma review, and operation-instance context delta found no remaining findings in reviewed scopes
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

Effectful Function and operation compatibility, declared bounds, typed-family
transport, lifecycle/generalization/freshening, full acceptance, termination,
and resource limits remain later gates. The compiler implementation remains
unauthorized.

## 8. Verification direction

After the theorem is repaired and reviewed, a finite exhaustive model check may
exercise small regular graphs and compare the original clauses with the
normalized residual graph. Include the alias contradiction above, `X <= {}`
with Records of several label sets, permitted-name intersections across
aliases, productive recursive equality, and guarded recursive subtype pairs.
Such checks would support the proof; they would not replace it. No tests,
builds, or measurements were run for this draft.
