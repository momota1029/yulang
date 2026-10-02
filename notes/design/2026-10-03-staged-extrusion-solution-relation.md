# Staged extrusion: relative solution-relation package

Status: Draft
Date: 2026-10-03
Reviewed-by: compiler_referee and spec_auditor, 2026-10-03; no findings in the original §§1–6 package or the separate §7 uniform-parent / §8 next-gate delta
Scope: candidate relative solution, finite replay and uniform-parent theorems for one exact ordered extrusion trace
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

## 7. Uniform parent tuple for a fixed original strategy

Fix an outer assignment `o`, a **nonempty** joint hidden domain `H_o`, and
an original strategy `nu_h` satisfying `G and Phi` for every `h in H_o`.
`Phi` is unchanged and mentions original coordinates only. All original
coordinates, including previously allocated anchors, keep that strategy.
Require a complete lattice `D` with the ordinary constructor variance of §3.
Fix one finite exact discovery trace. Only its actually generated signed
ports are new coordinates; the theorem does not generate missing signs.

Let `P+` and `P-` index its positive and negative ports. Their uniform
assignments form the complete lattice

```text
P = D^(P+) × (D^op)^(P-).
p ⊑ q iff p_positive <= q_positive and q_negative <= p_negative.
```

Evaluation `eval_h(t,p)` uses `nu_h` on original variables and `p` on new
ports. The same `p` is used for every `h`; it may depend on fixed `o`.
Bound cycles give finite mutually dependent equations in these coordinates,
without unfolding recursive trees.

### Normalize the operator, retaining the entire graph

The raw copied-bound operator need not be monotone in `P`. Positive
`Function(X,X)` visits `X-` first, producing `N` and inserting it into
`X.lower`. The later `X+` visit produces `Q` and copies `N <= Q`.
A raw positive component containing `N` decreases as that negative
coordinate increases in the signed order. Ordinary constructor variance
does not justify applying a monotone fixed-point theorem to that operator.

For the operator only, omit copied snapshot entries originating from this
call's earlier source-link writes. Retain every edge of `Ge` itself. An
original-variable snapshot consists of its initial bounds and such earlier
links: the exact discovery writes no other bounds into original variables.
An earlier added link in a selected side is the same variable's opposite
port, already at `B`, so its copied obligation is `N <= Q` for that variable.
The source links require, for every `h`,

```text
N <= nu_h(v) <= Q.
```

Since `H_o` is nonempty, these links entail the omitted copied obligation.
Thus this normalization removes only redundant operator terms, not graph
edges or original constraints. Initial `G` bounds, including prior-call
anchors, remain in the operator without this omission.

For each generated port, let `L_v` or `U_v` be its initial selected-side
bound list. Write `e+(b)` or `e-(b)` for that entry's recorded returned term
in this trace. Define the normalized operator componentwise:

```text
F_v+(p) = join_{h in H_o} (nu_h(v) join
                           join_{b in L_v} eval_h(e+(b),p))
F_v-(p) = meet_{h in H_o} (nu_h(v) meet
                           meet_{b in U_v} eval_h(e-(b),p)).
```

Empty bound lists use the lattice's empty join or meet. Only generated
coordinates and actually recorded bound-return terms occur in these formulas.
The joins/meets over `h` use the joint domain and the same original strategy;
they do not choose independently admissible marginal assignments.

### Monotonicity and exact uniform extension criterion

For fixed `h`, the positive return of an original input term is monotone
from `P` to `D`, and its negative return is antitone. Here original input
terms mean the enclosing original root and retained original-bound occurrences.
Their initial syntax contains no ports generated by this call, so each generated
leaf aligns with its path polarity; original anchors are constant in `p`.
Removed dynamic source-link snapshot returns are explicitly excluded from
this lemma: a return `e+(N)=N` need not be monotone when `N` is a negative port.
Prove the restricted claim by finite constructor induction with variables
as leaves. Positive ports are monotone projections; negative ports are
antitone projections.
A Function argument flips the recursive sign and its contravariance reverses
the resulting order again. Results and Record fields preserve their sign.
This establishes both claims without induction through recursive bounds.

Joins of positive terms are monotone. Meets of negative terms are antitone
in `D`, hence monotone in the negative component's `D^op`. Therefore the
normalized `F : P -> P` is monotone. For a tuple `p`, its components satisfy
all source links and initial copied-bound inequalities for every `h` exactly
when `F(p) ⊑ p`. The omitted dynamic copied links then follow as above.
Conversely, the full graph includes those source and copied obligations.
Thus, while `G and Phi` remain jointly retained and true under `nu_h`,

```text
p uniformly extends nu_h to the full Ge iff F(p) ⊑ p.
```

### Least tuple and retry consequence

Let `A = {p | F(p) ⊑ p}` and `m = meet_P A`. This set is nonempty,
since the greatest element of `P` belongs to it. For every `p in A`,
monotonicity gives `F(m) ⊑ F(p) ⊑ p`, hence `F(m) ⊑ m`.
Then `F(F(m)) ⊑ F(m)`, so `F(m)` also belongs to `A`; consequently
`m ⊑ F(m)`. Therefore `m = F(m)`, and `m` is the least pre-fixed tuple.
Write it `mu F`. This is the meet-of-pre-fixed-points form of
[Tarski, §1 Theorem 1, pp. 286–287](https://msp.org/pjm/1955/5-2/pjm-v5-n2-p11-s.pdf),
whose theorem and proof were read for this package; no other applications
from that paper are claimed here.

`mu F` uniformly assigns all new ports independently of `h`. For an unchanged
outer endpoint `a(o)`, a positive retry requires
`eval_h(e+(root),p) <= a(o)` for all `h`; a negative retry requires
`a(o) <= eval_h(e-(root),p)` for all `h`. These predicates are downward
closed in `P` by the signed term monotonicity, since the root is an original
input term. If any extending tuple passes
the corresponding retry, the least tuple `mu F` passes it too. Failure at
`mu F` excludes extensions satisfying that retry for **this generated graph
and fixed strategy**. This does not assert equality between the original
uniform retry relation and the extruded retry relation.

### Limits of this relative result

The theorem fixes `nu_h` and a semantic complete lattice; it proves neither
source nor inference principality. No finite syntactic representation or
effective supremum over `H_o` has been constructed here; this is not a
non-finiteness result. If `D` and `H_o` are finite
and explicit and constructors effective, bottom iteration terminates; this
is no general compiler complexity bound.

Witness-independent ports do not certify the exported root's scope: a hidden
`kappa` may survive as an unchanged anchor in that root. Arbitrary new-port
invariant/evidence predicates are not assumed downward closed; their full
relations must remain retained, and the retry consequence does not cover them.
This package uses a common graph and signed order, adds no source obligation,
and selects no Top exception, guard bypass or source rejection rule.

## 8. Exact next gate

Before implementation, establish a scoped extension criterion relating the
uniform source typing judgment, admissible boundary approximations and the
selected generation-time guard. The fixed-strategy semantic uniform-parent
criterion of §7 does not yet supply that source bridge or exported-root scope.
The gate must state when an original scoped joint
solution extends, when rejection is justified, and how source-generated bounds
and declared request interfaces satisfy that criterion without changing witness
identity. Resolve the conditional countermodel's source applicability there.
Complete effectful Function checking, lifecycle, source principality and full
solver termination remain later obligations. Relative exact representation
of this finite graph does not certify any of them.
