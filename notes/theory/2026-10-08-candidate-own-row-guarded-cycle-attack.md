# Candidate own rows on guarded cycles: assignment-preservation attack

Date: 2026-10-08
Status: frozen, unreviewed research characterization and conditional derivation
Gate: `CandidateOwnRowGeneralizationModelUnresolved`
Baseline: `8cadc7453404237c789c488db8c62c8b9cd747bf`
Production authority: none

## Objective and independent method

Attack loss of solutions, repeated-port sharing and recursive-owner identity
when one guarded Function bound interacts with ordinary direct inequalities.
The independent oracle enumerates concrete assignments satisfying the original
inequalities. The candidate side builds raw polarized expansion trees. No
other worker's checker is imported. No source language meaning is selected.

Authority is the isolated experimental permission in
`notes/design/2026-10-04-inference-research-playgrounds.md`, Direction and
Boundaries. Governing candidate facts are
`notes/progress/2026-10-08-shadow-apply-parameter-candidate.md`, Generalization
experiment and rejected global repair, and Frozen mechanism correspondence.
The rejected unconditional diagonal's extra Q on `my f x=f`, inadequate
outer-purpose distinction, historical Secondary references and differing
historical/current recursive quantification remain accepted constraints.

The oracle uses the powerset of three concrete tokens `{i,k,h}`. `i` has Int
head; `k` and `h` have Function head. Their total callable tables are
`k(x)=i` and `h(x)=x` for every token. Define

`F(A,B) = {f in {k,h} | forall x in A, f(x) in B}`.

This is antitone in the argument and monotone in the result. Bit masks use
`i=1`, `k=2`, `h=4`. Every row is one fixed coordinate in an assignment; all
its own leaves and active-path references use that coordinate. Function
argument traversal reverses polarity; result traversal preserves polarity.
Effects are omitted, with pure Function assumed. These total tables define a
discriminating finite oracle, not Yulang's completed Function membership.

## Exact source mapping and omitted seams

- `f5c_generalization.rs:7283`: same-polarity active reentry returns the same
  row; opposite-polarity activity records reentry and continues expansion.
- `f5c_generalization.rs:7370`: nonroot direct lower/upper targets expand in
  the corresponding polarity. `:7470` expands exact endpoints.
- `f5c_generalization.rs:7649`: Function argument polarity reverses and result
  polarity remains unchanged.
- Boxed `finish_row` at `:6035` / `:6189`, and flat sink at `:1621` / `:1763`,
  retain the own row before union/intersection of nonroot bound children.
- Root positive traversal excludes own/direct references. Recursive side
  extraction at `:11451` forces an absent lower side to Bottom and absent
  upper side to Top. The checker tests nonroot raw expansions, where even an
  absent side returns the own row; its theorem does not identify a root with
  its assignment or identify those sidecar extremes with an own reference.
- The lower replay shortcut, memo promotion, structural deduplication,
  metering, incidence census, provisional owner traces, guarded R fixed point,
  one-sided elimination, final Q/R substitution and freshening are omitted.
  In particular, `:11030` excludes selected R owners from Q. The model never
  interprets that conversion or claims that its owner coordinates survive it.

In the modeled fragment, expansion scheduling and syntactic duplicate removal
do not change union/intersection denotation. This observation does not prove
the production lower-replay shortcut or memo correspondence.

## Conditional theorem and precise missing premise

**Hypotheses.** Let a finite row graph have direct inequalities and polarized
exact bounds over an extensional constructor interpretation. Fix one
assignment `rho` satisfying every original direct and exact inequality.
Expansion retains each row's own symbol on both nonroot sides, references
`rho(row)` on same-polarity active reentry, and preserves that identity at all
repeated ports. Constructor children expand with the specified polarities.
Expansion stops at a repeated `(row,polarity)`; the graph is finite.

**Conditional conclusion.** Every raw nonroot positive and negative expansion
of row `r` denotes `rho(r)`, including a graph with guarded cycles.

**Derivation.** Induct over the finite expansion tree. An active-path leaf
denotes its exact row coordinate. For a positive expansion, the own symbol
denotes `rho(r)`; each expanded direct lower denotes a subset of `rho(r)` by
the direct inequality and induction; each exact lower denotes a subset by
constructor extensionality, child equality and its original bound. Their
union is exactly `rho(r)`. The negative case intersects `rho(r)` with direct
and exact supersets, again producing exactly `rho(r)`. Function argument
contravariance is encoded in the child polarity; its denotation agrees once
both child equalities hold. Reentry identity, rather than arbitrary unfolding
depth, closes the finite induction. No recursive greatest/least solution is
assumed or proved.

This theorem is conditional on an **already satisfying original assignment**
and **unchanged row/owner interpretation**. It establishes neither the
existence of such an assignment nor equivalence after quantification or R
conversion. The precise remaining blocker is transport of one satisfying
whole assignment through census/elimination, selected R ownership and final
Q/R interpretation. The historical own-symbol mechanism supplies no theorem
for that transport. The finite checker assumes raw transition rules and
therefore does not prove those rules are source adequate.

## Bounded experiment and mutation witnesses

The checker exhausts three rows `0,1,2`; zero to two distinct nonself directed
edges from the six possible edges (22 edge sets); one exact Function lower or
upper on row 0 (2 sides x 3 argument rows x 3 result rows); and optional Int
lower/upper on row 2 (3 choices). There are `22*2*3*3*3 = 1188` graphs.
Each graph gets all `8^3 = 512` assignments, with no random seed.

All 608,256 graph/assignment candidates were examined. The 38,700 satisfying
assignments passed all six row/side equalities: 232,200 equality checks.
720 graphs have same-polarity reentry; 648 have at least one reentry whose
cycle segment crosses a Function port. There is no candidate counterexample
within this envelope. Cross-polarity recording itself is not counted as a
same-polarity terminal reentry.

The active-owner alias mutation replaces the row coordinate on active
reentry by the next row's coordinate, while leaving own symbols unchanged.
Its smallest direct-and-Function interaction uses two meaningful rows:

```text
r <= s; F(r,r) <= r
rho(r) = {h}; rho(s) = {i,h}
```

`F({h},{h})={h}`, so the original assignment satisfies both bounds. Positive
expansion enters the negative argument of `r`, which remains `{h}` under
`r<=s`; the positive result reentry is incorrectly aliased to `s`. It computes
`{h} union F({h},{i,h}) = {k,h}`, adding `k` to `r`. Positive forwarding to
`s` computes `{i,k,h}`. If this aliased lower is required below the unchanged
owner `{h}`, it rejects a formerly satisfying assignment. Thus recursive
owner identity is a substantive condition. This is a deliberate mutation,
not evidence the current implementation aliases owners.

The executable witness is `[r,s,unused]=[4,5,0]`, with one lower Function,
one edge `(0,1)` and no scalar bound. Its row-side outputs are
`[6,4,7,5,0,0]` rather than `[4,4,5,5,0,0]`. The unused third coordinate can
be removed. One direct edge and one Function bound are minimal in number for
the stipulated interaction shape; no global minimality claim is made.
The mutation also fails without the direct edge on
`F(r,r)<=r, rho(r)={h}, rho(s)={i}`.

A separate repeated-port mutation uses `F(q,q)` with the shared coordinate
`q=Bottom`: both `{k,h}` are present. Independently replace only the argument
coordinate by Top while retaining the result Bottom; the set becomes empty.
This smallest one-Function witness demonstrates loss when a repeated port is
split. The candidate side always shares the coordinate and passes.

## Oracle independence and coverage limits

Reference satisfaction evaluates original inequalities directly in the
concrete callable tables. It does not inspect candidate expansion trees,
derive constraints from them, or assume the expansion equalities. The two
sides share the same powerset carrier, Function interpretation, supplied
original graph and row assignment. That shared interpretation is an explicit
model assumption; agreement cannot validate source generation or production
Function membership. The mutations independently challenge identity/sharing.

Unsearched cases include more than three rows, more than two direct edges,
self direct edges, multiple or nested exact Function terms, multiple scalar
bounds, other constructors, effects/handlers, arbitrary worlds, levels,
fixed outer coordinates, source realization, final generalized schemes and
fresh uses. All three row coordinates are explicitly fixed for each test;
there is no quantified versus outer-level distinction in this oracle.
Unsatisfiable original graphs receive no assignment-preservation conclusion.

## Commands, resources and frozen dependencies

Command: `python3 -B tools/research_candidate_own_row_guarded_cycle.py`.
Final run: exit 0, elapsed 0.221417 seconds, peak RSS 11,520 KiB on Linux.
One Python process at a time; in-process SIGALRM hard stop 10 seconds;
generation cap 5,000. Three focused executions used approximately 0.668
seconds combined checker wall time. The latter executions added the direct
mutation witness and corrected guarded-cycle counting to measure Function
ports *after owner entry*. They are refinements of this single method, not
additional premise-discharge attempts. CPU time was not separately measured.
No Cargo, compiler tests, builds or benchmark samples ran. Timeout,
generation-cap failure or an equality mismatch raises an error; partial
enumeration is not reported as success. Peak RSS is a measured result rather
than an enforced memory limit.

Direct dependency SHA-256:

```text
a8e91f292a0e04212de89bc044127154a91660473fd483d1a61a87190ee3d542  notes/design/2026-10-04-inference-research-playgrounds.md
08fe67474ab2b36a44fd7028ccd6f9966c0b792a2330391f9e426e81c874a173  notes/progress/2026-10-08-shadow-apply-parameter-candidate.md
6f029758c19c99e397b9653af842b39ca680ece077b65322606266987515ab88  crates/yu-solver/src/f5c_generalization.rs
8f1db3a282956b7deaf312cec6668808c5c4137adb5f964ca7cc10ef471a9c81  crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs
f69fb7938dd22ba6cc65b8a1474e9e3f05c30af106c3ca110778b4a225807173  crates/yu-solver/src/f5c_tree_analysis.rs
```

Recommended next action: inspect the owning post-R conversion using a retained
whole-row assignment/owner certificate, and identify its exact transport rule.
Another larger raw-expansion search would leave that same premise untouched.

## Commit packet

- Exact lease: `notes/theory/2026-10-08-candidate-own-row-guarded-cycle-attack.md`
  and `tools/research_candidate_own_row_guarded_cycle.py`.
- Baseline: `8cadc7453404237c789c488db8c62c8b9cd747bf`.
- Dependency hashes: above; changed dependency hashes: none at freeze.
- Review: unreviewed producer artifact; no independent certification.
- Checks: final deterministic Python run above; leased-path diff whitespace
  check reported separately in the handoff.
- Proposed commit: `research: bound own-row expansion on guarded cycles`.
- Shared deltas left to primary/curator: link the conditional raw-preservation
  result and identity mutants; retain the unresolved Q/R assignment-transport
  premise and current gate status. No task/index/authority/DAG edits requested
  as automatic closure.
