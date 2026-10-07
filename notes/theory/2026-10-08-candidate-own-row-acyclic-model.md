# Candidate own-row retention on the acyclic forwarding triangle

Date: 2026-10-08
Status: independently reviewed bounded assignment-to-closed-artifact theorem; no compiler semantic closure
Baseline: `8cadc7453404237c789c488db8c62c8b9cd747bf`
Gate: `CandidateOwnRowGeneralizationModelUnresolved`, restricted acyclic relation
Authority: research only; no production routing or language decision
Lease: this note and `tools/research_candidate_own_row_acyclic.py`

## Objective, sources and claim classes

Characterize the supplied candidate transformation for one positive Function
root with a negative argument row `a`, positive result row `c`, and forwarding
`a <= b <= c` (plus the redundant direct edge `a <= c`). Keep one valuation
per row identity and arbitrary externally fixed coordinates. The root is a
fourth identity with only the Function lower constructor; its own symbol is
excluded, matching the candidate's nonroot condition.

Governing sources are the research playground design's **Direction** and
**Boundaries**, and the parameter candidate progress note's **Generalization
experiment and rejected global repair** and **Frozen mechanism correspondence**.
Accepted constraints: ordinary mode stays false, unconditional diagonal repair
was rejected by unchanged `my f x=f`, and guarded recursion remains unresolved.
F5 foundation §§6, 8, 23 and 33 supply polarity/identity/eligibility context;
this experiment does not reinterpret their language contract.

The result has three distinct parts:

- A conditional lattice derivation: under the original direct inequalities,
  own-row expansion preserves each row pointwise, hence the full joint relation.
- An exact conditional projection characterization for this triangle: after
  forgetting direct inequalities, the observable relation agrees precisely
  when fixed coordinates in the challenge interval are ordered consistently.
- Bounded executable evidence plus a minimized counterexample to unrestricted
  forgetting of direct inequalities. This is not a counterexample to the
  current compiler: correspondence to actual fixed-coordinate preservation is
  unproved.

No established Yulang theorem, scheme principality, fresh-use equivalence,
recursive correctness or production cutover claim follows.

## Explicit model and hypotheses

Let `L` be a bounded lattice, with order `<=`, join `∨`, meet `∧`, Bottom `0`
and Top `1`. These are **candidate model assumptions**, not source typing
definitions. A valuation `ρ` assigns one lattice element to each payload row
identity. Repeated occurrences always use the same `ρ` coordinate.

The three slots may alias contiguously: `(a,a,a)`, `(a,a,c)`, `(a,c,c)` or
`(a,b,c)`. Reflexive edges are discarded and duplicate edges deduplicated.
Noncontiguous `(a,b,a)` with distinct `a,b` creates a direct cycle and is outside
this acyclic family. Ordered distinct identities are `r0,...,r(n-1)`, `1<=n<=3`.

The direct constraint predicate is `C(ρ) := ∧(ρ(ri) <= ρ(rj))` over the retained
edges. The only constructor observation is the **supplied** Function challenge

`F(u,v; x,y) := (u <= x) ∧ (y <= v)`.

It flips the argument comparison and preserves the result comparison. There
are no runtime Function values, effects, invocation histories, world/domain
admission, or constructor denotation in this model. This is a challenge
relation; equality of arbitrary syntactic Function images is not the claim.

For nonroot rows define the candidate:

```text
P(r) = ρ(r) ∨ ∨{P(s) | direct s <= r}
N(r) = ρ(r) ∧ ∧{N(t) | direct r <= t}
```

An empty neighbor set leaves `ρ(r)`. Acyclicity makes both recurrences finite.
The candidate root observes `F(u,v; N(a),P(c))`.

The original joint relation, with no coordinate forgotten, is

`J = {(ρ,u,v) | C(ρ) ∧ F(u,v; ρ(a),ρ(c))}`.

The constrained transformed relation is

`J_keep = {(ρ,u,v) | C(ρ) ∧ F(u,v; N(a),P(c))}`.

Keeping `C` is an explicit hypothesis. A checker assuming these recurrence and
challenge rules does not prove that actual source/generalizer rules have this
interpretation.

## Derivation 1: pointwise identity and joint preservation

In a topological order, assume `P(s)=ρ(s)` for each predecessor. From `C`,
every predecessor satisfies `ρ(s)<=ρ(r)`. Joining them with `ρ(r)` yields
`P(r)=ρ(r)`. The empty case is immediate. In reverse topological order, the
dual argument gives `N(r)=ρ(r)`: each successor is above `ρ(r)`, and meeting
with `ρ(r)` yields `ρ(r)`.

Thus `J=J_keep` pointwise. Arbitrary fixed coordinate restrictions, repeated
identity incidences, and projection of any coordinates preserve this equality.
The argument works for any finite acyclic direct-row graph in a bounded lattice;
the executable scope below is only the forwarding triangle. Bounds retained
only as separate one-coordinate marginals would not satisfy this premise.

## Derivation 2: exact projection when direct bounds are forgotten

Fix a partial map `κ` from row identities to lattice values; the other rows
are existential. Keep the challenge coordinates `(u,v)` explicit. Define

```text
Rκ(u,v) = exists ρ extending κ. C(ρ) and F(u,v;ρ(a),ρ(c))
Sκ(u,v) = exists ρ extending κ. F(u,v;N(a),P(c))
```

`S` deliberately drops `C`. On this chain/triangle,
`N(a)=∧i ρ(ri)` and `P(c)=∨i ρ(ri)` even without `C`, because every identity is
reachable in the respective direction. Lattice laws therefore give

```text
Sκ(u,v) iff u<=v and every fixed κ(ri) lies in [u,v].
Rκ(u,v) iff Sκ(u,v) and every fixed pair i<j satisfies κ(ri)<=κ(rj).
```

For `S`, necessity follows from `u<=ρ(ri)<=v`; sufficiency assigns every unfixed
row `u`. For `R`, necessity is transitivity along the chain. For sufficiency,
assign each unfixed row its nearest earlier fixed value, or `u` if none exists.
Consistently ordered fixed values in `[u,v]` make that entire chain monotone.
This proof uses shared identities, existential completion of only unfixed
coordinates, and the challenge relation above.

Consequently `Rκ⊆Sκ`. For a particular challenge they differ exactly when all
fixed values are in `[u,v]` but some fixed pair is out of order. With no fixed
coordinates both are exactly `u<=v`. With one fixed coordinate they also agree.
An externally guaranteed monotone fixed-coordinate relation is sufficient for
equality. The theorem neither supplies nor assumes that the actual compiler
retains such a guarantee after generalized export.

## Smallest obstruction and mutations

The checker first finds slot aliases `(a,a,c)`, with two distinct payload rows,
fixed `a={x}`, fixed `c=∅`, and challenge `u=∅, v={x}`. `S` holds: both fixed
values lie in the interval. `R` is empty because `{x} <= ∅` is false. The generic
three-distinct-row version has the same fixed endpoints and existential `b`;
there can be no `a<=b<=c` completion.

This obstruction needs only the one-atom sublattice `∅,{x}`, two distinct
payload identities (three including the Function root), and two fixed
coordinates. One identity or a one-element lattice cannot distinguish the
relations. With fewer than two fixed coordinates Derivation 2 proves equality.
Thus those dimensions are minimized analytically, not by an additional run.

Two named mutations discriminate different shared premises:

1. **Erase own symbol on bounded rows**, while retaining `C`. For `(a,a,c)`,
   negative argument expansion becomes `ρ(c)` and positive result expansion
   becomes `ρ(a)`. With no fixed rows, challenge `{x},∅` is incorrectly admitted
   by `ρ(a)=∅,ρ(c)={x}`. The reference requires `{x}<=ρ(a)<=ρ(c)<=∅` and rejects.
   For the generic triangle this is also the projection observed after the
   distinct endpoint symbols become one-sided and are replaced by extremes;
   full compiler census/normalization is not executed here.
2. **Freshen repeated occurrences independently**, splitting negative and
   positive valuations. Even `(a,a,a)` then admits challenge `{x},∅`: choose
   negative occurrence Top and positive occurrence Bottom. The correctly
   shared identity requires `u<=ρ(a)<=v` and rejects. This mutation is tested
   by an explicit extremal construction for unfixed rows, not a second
   exhaustive split-valuation enumeration.

## Source correspondence and oracle independence

Current boxed `finish_row` at `f5c_generalization.rs:6035,6189` and flat
`finish_row` at `flat_walk_sink.rs:1621,1763` add `Variable(row)` precisely for
candidate mode, nonroot rows and nonempty child lists. Empty nonroot rows
already produce their own variable. The walker at `f5c_generalization.rs:7373`
selects direct lowers in positive polarity and direct uppers in negative
polarity, deduplicates targets, and traverses them as nonroots. Its Function
sink at `:6338` assembles already-polarized children; the walker dispatch at
`:7657` flips argument polarity when scheduling its `EnterTerm`. These justify
the **syntactic fragment encoding**, not the interpretation of exported
quantifiers as this lattice.
The exact-bound replay optimization is irrelevant here: payload rows have no
exact nonvariable bounds. The root has one exact Function lower only.

The reference predicate independently evaluates direct inequalities and the
unexpanded Function challenge. The candidate evaluates recursive join/meet
expansion. They do not share a traversal/expansion oracle. They do share `L`,
the order implementation, identity mapping, challenge rule, and graph family.
Passing comparisons verify algebra under those shared assumptions; they do
not validate source typing, production generalization, or the legacy Oracle.
No Oracle execution or adoption occurred. The historical own-symbol evidence
remains exactly the limited mechanism correspondence recorded by the primary.

## Restricted post-R/Q assignment transport

The following source-to-artifact bridge is independently reviewed against
F5 §§23/33 and the implementation at source baseline
`652820a095638ae54ea6838714b764da7b04ab3a`. It extends the conditional lattice
calculation above through Q selection and closed representation for one narrow
successful candidate path.

Assume candidate own-row mode; one fresh root distinct from all payload rows;
the root's sole lower constructor is `PureFun(a,c)`; the only payload
constraints are the acyclic forwarding edges `a≤b≤c`; and there are no payload
exact bounds, extra roots, enclosing-binder references, guarded reentries,
recovery paths or stale memo summaries. Each payload row must be quantifiable
(`level > boundary`, with the actual path using boundary zero) and outside the
non-generic closure. Assume generalization, normalization, finalization and
terminal finish succeed. Interpret union/intersection and Function challenges
in the stated lattice model, and let one shared valuation `ρ` satisfy the
original direct edges.

The root expansion excludes its own symbol. Function argument traversal is
negative and follows direct upper edges, while result traversal is positive
and follows direct lower edges. Candidate nonroot completion retains each
payload's own symbol alongside its expansion. Therefore every distinct payload
identity occurs in both polarities: the argument denotes
`ρ(a) ∩ ρ(b) ∩ ρ(c)`, and the result denotes
`ρ(a) ∪ ρ(b) ∪ ρ(c)`. The acyclic graph has no active-path reentry and therefore
no R owner; bipolar rows are not one-sided eliminations. Retained occurrences
deduplicate the shared row identities and assign each one a distinct Q ordinal.
Positive and negative substitution use the same Q map, and normalization,
finalization and export preserve those binder incidences and constructors,
modulo exact normalization.

For each such original satisfying valuation, define the artifact valuation by
`η(Q(r)) = ρ(r)` for each payload row. The direct-edge premise gives
`ρ(a)≤ρ(b)≤ρ(c)`, so lattice absorption makes the exported argument and result
evaluate to `ρ(a)` and `ρ(c)`. Thus the source-to-artifact path retains this
one-way witness through Q selection and closed representation in the restricted
model.

This does not establish adequacy of the supplied lattice interpretation for
actual closed-Q semantics. The exported Q binders carry no direct-edge table;
arbitrary Q valuations need not satisfy `a≤b≤c`. Nor does the result establish
source realization, incoming-use restoration, converse coverage, recursive
R semantics, universal scheme validity, successor correspondence, soundness,
principality or a production repair. These remain outside this theorem.

## Command, coverage and resource accounting

One Python process; no Cargo, compiler changes, tests, formatting or Git
mutation. Exact command, exit 0:

```text
timeout --signal=KILL 10s python3 -B tools/research_candidate_own_row_acyclic.py
```

The internal deadline is 9 seconds, with an external 10-second hard kill.
No seed/randomness. Exhaustive ranges: lattice bitmasks `0..3`; the four slot
patterns above; each identity either unfixed or fixed to one of four values;
all 16 `(u,v)` challenges; every complete row valuation in `L^n`.

Results: 2,880 generated graph/fixed-map/challenge models, 141,120 valuation
visits, 3,328 direct-satisfying pointwise checks, and 1,552 models with ordered
fixed coordinates. Both conditional characterizations passed throughout;
all three named witnesses were detected. No search stopped early or timed out.
Process-reported wall time 0.070321 seconds, total CPU 0.085024 seconds, Linux
peak RSS 11,200 KiB. One process consumed out of one permitted; generated-model
count is below 5,000. No output files or bytecode caches were generated.

Failure conditions: assertion failures flag either a relation disagreement,
missing mutation witness, budget overrun, or characterization failure. Domain
or graph edits require a new explicit budget and checker review.

Unsearched: payload nonvariable bounds/constructors, multiple Function nodes,
effects, arbitrary DAG branching, cycles and guarded recursion, noncontiguous
aliases, level/extrusion/non-generic closure outside the stated premise,
incoming-use substitutions, adequacy of the supplied lattice for whole-scheme
source interpretation, converse coverage and compiler execution.

## Dependency freeze, recommended action and commit packet

Direct dependencies remained unchanged across the computation:

```text
a8e91f292a0e04212de89bc044127154a91660473fd483d1a61a87190ee3d542  notes/design/2026-10-04-inference-research-playgrounds.md
08fe67474ab2b36a44fd7028ccd6f9966c0b792a2330391f9e426e81c874a173  notes/progress/2026-10-08-shadow-apply-parameter-candidate.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
6f029758c19c99e397b9653af842b39ca680ece077b65322606266987515ab88  crates/yu-solver/src/f5c_generalization.rs
8f1db3a282956b7deaf312cec6668808c5c4137adb5f964ca7cc10ef471a9c81  crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs
```

Recommended next action: check the actual exporter/fresh-use ownership point
for a canonical retained guarantee that fixed rows satisfy the original joint
direct inequalities. That source/artifact bridge discriminates the remaining
premise; another lattice recurrence checker would leave it untouched.

Commit packet:

- Exact leased paths: `notes/theory/2026-10-08-candidate-own-row-acyclic-model.md`;
  `tools/research_candidate_own_row_acyclic.py`.
- Baseline SHA: `8cadc7453404237c789c488db8c62c8b9cd747bf`.
- Changed dependency hashes: none; frozen dependencies listed above.
- Review: independent compiler-referee, second compiler-referee and
  spec-auditor reviews accepted the bounded assignment-to-closed-artifact
  argument under its stated premises. The note audit found and prompted the
  polarity-dispatch locator correction above. Reviewers left actual closed-Q
  semantic adequacy and the broader gates open; no DAG status changed. The
  producer does not certify its own output.
- Checks already run: the one bounded deterministic Python command above;
  source/code review of Q selection, substitution, normalization, finalization
  and export for the restricted bridge; lease-scoped whitespace/diff
  inspection and dependency hash recheck.
- Proposed commit message: `research: characterize own-row retention on acyclic forwarding triangle`.
- Shared deltas left to primary/curator: record the conditional direct-bound
  premise and smallest fixed-coordinate obstruction; retain
  `CandidateOwnRowGeneralizationModelUnresolved`; close no DAG or cutover gate.
