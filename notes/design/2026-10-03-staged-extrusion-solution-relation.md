# Staged extrusion: relative solution-relation package

Status: Draft
Date: 2026-10-03
Reviewed-by: compiler_referee and spec_auditor, 2026-10-03; no findings in the stated relative theorem package
Scope: candidate theorem for one exact ordered extrusion trace and finite consequence replay
Implementation authority: none
Supersedes: none

## 1. Authority and reference boundary

[Charter §§20, 22–23](2026-09-29-scc-intrusion-redesign-charter.md)
retain existential request identity, require generation-time guarding of every
derived comparison, and place levels on variables. This package develops the
relation-preservation obligation left by the conditional staged-extrusion
scope lemma in [operation-instance §8](2026-10-02-operation-instance-binding-package.md).
It selects no implementation, new source rule, guard exception or acceptance policy.

Reference behavior is the already pinned
[paper/source audit](../progress/2026-09-30-simple-sub-paper-mlsub-audit.md)
and [preallocation lemma](../progress/2026-09-30-simple-sub-extrusion-preallocation-lemma.md):
`mlsub-compare` commit `9bae772624c23b52a93c1b226157e16898b4d9db`,
`Typer.scala::extrude`. No new source execution or compiler result is claimed.
The original algorithm has no existential request-opening semantics.

## 2. Frozen input and exact discovery trace

Fix a finite initial bound graph `G`, one boundary `B`, and an ordered root
extrusion. The initial variable set `V` includes variables in the root.
No external constraints or mutations enter during discovery.
Constructor syntax is a finite acyclic DAG; recursive bounds pass
through variables. Original variables retain their immutable levels and identities.
Each bound denotes its corresponding inequality, and original edges remain.
Use the original polarity-keyed first-visit memo `(v,p)`, with `p` positive or
negative. A variable at level `<= B` is an unchanged anchor.

Discovery runs in a private shadow, starting from `G`. A first deep visit
allocates `R(v,p)` at `B`, installs its memo entry before recursion, and performs
the original source-side link and ordered immutable-list snapshot reads:

```text
positive: v <= R(v,+); R.lower := map(e+, snapshot(v.lower))
negative: R(v,-) <= v; R.upper := map(e-, snapshot(v.upper))
```

The source link precedes the snapshot. Snapshot traversal and final list
assignment follow the original nested continuation order. Opposite polarities
retain distinct representatives. Earlier source links can appear in a later
snapshot; an already selected snapshot does not change during its traversal.
Reserved-name preallocation is valid only under the exact trace simulation
conditions of the preallocation lemma, with an initially empty operational memo.

Every source-link and copied-bound edge is emitted through the common guard
at generation, before admitted insertion. Provisional mutation is invisible
outside the attempt until success. A failed guard prevents publication.
Relation replay has a separate ledger: replay must not invoke the original
mutating `constrain` into the active discovery shadow, since its added bounds
could change later snapshots. Common `Compare` is the obligation entry; it
does not mandate the reference mutator as its implementation.

**Trace correspondence.** On a successful discovery trace, the shadow is the
exact unguarded reference trace up to fresh-name renaming. Induct on the
small-step trace, relating memo entries, selected list snapshots, map frames,
source links and returned terms. A successful guard permits the same next
write; separate replay cannot change any discovery read. This claim concerns
successful traces only and does not assert equal guarded acceptance.

## 3. Unscoped graph solutions and diagonal extension

Let the carrier be a preorder with interpretations of the admitted structural
constructors respecting their variance. Functions reverse order in their
argument and preserve it in their result; Records preserve field order.
A solution `nu` interprets all variables jointly and satisfies every graph edge.
This section deliberately forgets scope/dependency admissibility.

Let `Ge` be the discovery graph before adding an enclosing retry obligation.
For every solution `nu` of `G`, define its diagonal extension by

```text
nu_e(v) = nu(v)                    for each original variable
nu_e(R(v,p)) = nu(v)               for each fresh representative
```

Under this assignment, both source-link polarities are reflexive. Structural
extrusion preserves the value of a copied term, since each replaced variable
has the same assigned value. Each selected bound is an initial bound or a
source link already inserted by discovery; both hold under the diagonal.
Thus copied bounds also hold. This argument follows the finite execution and
its snapshots; it does not freeze all snapshots to the initial graph.
Original edges are retained, so restriction of any `Ge` solution satisfies `G`.
Consequently, with projection hiding only the fresh extrusion representatives,

```text
projection_original(Solutions(Ge)) = Solutions(G).
```

An additional retained family/evidence relation `Phi` may mention original
coordinates only and remains literally untouched. The diagonal argument
preserves `G and Phi` pointwise under the same joint assignment; it proves
no evidence-rewriting theorem. Independently solving marginal endpoint graphs
is not this projection. No effect-interface theorem follows.

## 4. Signed approximation and the enclosing retry

For every solution of `Ge`, each visited `(term, polarity)` return in the
trace satisfies its corresponding signed inequality:

```text
t <= e+(t)                  e-(t) <= t.
```

Only visited signs are asserted; a visit need not allocate both signs.
For a deep variable, these are its source links; anchors are reflexive.
For constructor syntax, use finite structural induction with variables as
leaves. In a Function argument, the recursive sign flips and contravariance
reverses its inequality; results and Record fields preserve it. Memoized
recursive bound cycles need no infinite-tree induction: their variable-leaf
cases already follow from installed links.

Let `a` be an unchanged expression over original variables.
Suppose the enclosing original obligation is `t <= a`, with retry
`e+(t) <= a`. Every retry solution satisfies the original by transitivity.
Conversely every solution of `G` and `t <= a` extends diagonally; there
`e+(t)` has the same value as `t`, so the retry holds. The negative case
compares original `a <= t` with retry `a <= e-(t)` and uses the dual chain.
Therefore each corresponding extended-and-retried graph has exactly the
original obligation's solution relation after projection of fresh ports.
This is an unscoped, relative representation theorem, not source principality.

## 5. Finite discovery and consequence-only replay

If `V` is the initial variable set, at most `2|V|` representatives are
allocated. Each deep original `(v,p)` is expanded once. Newly introduced
source-link endpoints are at `B` and are anchors even if later snapshots
visit them; they do not create new deep-variable memo keys. Each snapshot is
finite, constructor descents are finite, and bound recursion returns through
the first-visit memo. Thus discovery terminates for the stated finite input.
This is a finiteness argument, with no useful linear runtime bound claimed.

Fix a finite generated term set `T` for replay, of size `N`, and prohibit new
allocation or constructor generation during that replay. Add only inequalities
entailed by the current relation, such as transitivity and justified structural
decomposition. Decomposition requires a carrier-specific reflection law:
from a constructor inequality, its generated component obligations must follow.
Variance alone proves construction from component inequalities, not reflection.
No decomposition outside such admitted laws is covered.

Adding an entailed edge preserves every full joint assignment, and retaining
existing edges preserves the converse. Induction over replay therefore
preserves the complete solution relation, followed by the same eligible
projection. At most `N^2` distinct ordered comparison pairs can be added.
Use a deduplicated worklist, processing each pair once for the fixed state
and premises. It terminates within this pair bound; this does not prove termination
of a solver that changes terms, dependencies, allocations or labelled states.
Guard certification and its dependency invalidation still require the
conditional coverage premises of operation-instance §8.

## 6. Scoped extension is a separate obligation

The diagonal may be inadmissible for a scoped solution: a boundary port
cannot necessarily depend on the opened witness on which `nu(v)` depends.
Preserve the original `kappa` identity through every source link and copied
bound. A fresh representative is a port, never a new operation witness or
an independent request instantiation. The unscoped theorem cannot silently
replace the uniform arm's scoped joint relation.

**Conditional countermodel.** Suppose the chosen carrier has a
witness-independent greatest value `U` and a covariant Record constructor.
For `kappa_l <= X_(l+1)` and enclosing `Record{f:X} <= Y_l`, positive
extrusion copies `kappa_l <= R_l`. The original and unguarded extended
constraints admit the uniform assignment

```text
X := kappa; R := U; Y := Record{f:U}.
```

The boundary assignments `R,Y` are witness-independent, but the §22 guard
rejects the generated `kappa_l <= R_l` edge. This conditionally separates
scoped semantic extension from raw-edge guard acceptance. It neither selects
a Top exception nor exhibits an actual Yulang source counterexample.
Source expressibility, declared bounds and guard completeness remain open;
not every scope-rejected graph is thereby proved unsatisfiable.

## 7. Exact next gate

Before implementation, establish a scoped extension criterion relating the
uniform source typing judgment, admissible boundary approximations and the
selected generation-time guard. It must state when an original scoped joint
solution extends, when rejection is justified, and how source-generated bounds
and declared request interfaces satisfy that criterion without changing witness
identity. Resolve the conditional countermodel's source applicability there.
Complete effectful Function checking, lifecycle, source principality and full
solver termination remain later obligations. Relative exact representation
of this finite graph does not certify any of them.
