# Cycle236 remaining bridges (after exact where accessibility)

The exact source boundary is `GeneralNominalVersionedMixedSourceBoundary234`.
This is a proof plan, not a replacement target or an asserted theorem.

## Finite historical coverage before more completion fragments

For an arbitrary source-reachable state and its actually selected current plan,
prove `AggregateLedger236.ProtectedCovered (MixedFreshCompletion236.pool state plan)
state plan.packet`. The target itself is a finite, syntactic lookup:
every current aggregate entry whose ID occurs in that pool must have a stored
plan with the same seed and the same aggregate ID. `same_target` then provides
the RHS equality, and `protected_equations` obtains the actual equations from
that stored plan's full journal model. Do not assume the equations as a new
semantic hypothesis.

Split pool membership into the following *real definitions*:
1. Legacy journal supports: current raw constraints, sites/center arguments,
   historic legacy packets. Reservation ownership alone is not a semantic use.
2. Versioned stored-plan support: private merges, actual schema, output schema,
   ordered child materialization, and mode-dependent expressions.
3. Stored effect support: private head, snapshot class and current live class.
4. Current raw support and current selected class support.

For each occurrence, separate allocation families by the actual purpose tags
and recover the seed before applying slot injectivity. A current aggregate can
occur as an endpoint of a later observed argument; absence from raw reservation
lists does NOT prove disjointness from these supports. Such endpoint occurrences
need provenance back to a real recorded plan. `Dependency236` only proves that
an aggregate is numerically greater than its *own* captured endpoints. It does
not establish this historical provenance or a finite bound on future versions.

## One model, not independently chosen witnesses

`MixedSelectedWitness236.sharing` uses an explicit nonempty journal Models
assumption to rule out SharingConflict. `effects` starts from an actual chosen
head model and rules out OutputConflict. Neither result says those witnesses
can be identified with an arbitrary journal model or with one another.

`MixedLedgerCompletion236.simultaneous` constructs one explicit selective patch
from one model satisfying journal/cross/self/projection/current ClassEffects.
Its conclusion covers journal Models, candidate private HeadModels and current
ClassEffects. The remaining fullHolds obligations are actual HeadEquations,
emitted output schema and complete ordered child materialization. Actual-mode
value preservation now holds without Fresh, but does not supply new output or
child equations. Establish these obligations in that *same* constructed model.

## Full operational termination

`MixedProgressSplit236` proves all non-installation steps well-founded and that
an actual source-reachable step is administrative or appends a plan. Its
`InstallationDescent` rank is explicitly an unsolved obligation. An unbounded
numeric content-addressed slot encoding is not a finite installation bound.
Use real observation/commitment invariants to construct a decreasing rank, or
first search for an actual repeated-installation counterexample. A raw
unreachable journal or an auxiliary sufficient condition failing is not a
counterexample to the requested target.

## Stop and regression rules

No new exact-target counterexample was found in this cycle. If any target
counterexample is found later, obey I34 and ask through the supervision path;
do not weaken the selected frontier, alter language semantics, or keep proving
a known false target. Preserve 199/202/204/206/218/230 regressions. The actual
218 stable endpoint resolves as a selected parent with one pending child; its
old child is rejected, and this is not a successful root dictionary.

### Final support review

The actual-value preservation proof already separates versioned aggregate slots
from every legacy fresh slot (`not_legacy_slot`), including output purpose 2
and nonpoint actual-binder purpose 8. Thus those allocations do not require
new semantic case splits in the coverage theorem. The difficult residual case
is a raw singleton endpoint or a later observation endpoint that is itself an
old aggregate. Track its origin through the actual trace rather than assuming
that every identifier in the support is a directly allocated aggregate.
For the initial case use the real below-seed source invariant; for each install
retain the packet's entry-list witness; for refresh/reobserve/equate/merge show
that no unrelated source identity enters semantic support. These are planned
induction obligations, not yet verified invariants.
