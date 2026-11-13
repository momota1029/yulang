# Direct accessibility of the unrestricted centered relation

Status: ground point-root accessibility proved directly. Selected-plan
availability and the operational P/W trigger trace remain open. This note
replaces the open accessibility status in
[the point-source bridge note](2026-11-14-centered-point-bridges.md); it does not
change any existing definition or owner decision.

## Authority and scope

The owner decision in [spec §6.5](../../spec/06-roles.md) says:

> 実際の引数の名前（中心）は明示して持つ

> 中心は `lower ≤ 中心 ≤ upper` を満たす未知の型の名前で、具体的な型を選ぶものではない。

> 実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない

The new proofs preserve the centered state and Step already integrated. No
provenance pending case is added. Finite labels below are retrospective proof
witnesses in a model, not choices of concrete argument types by the resolver.
The latest supervisor instruction explicitly authorizes this direct
accessibility proof, superseding the earlier exclusion of that work.

`GeneralNominalCenteredAccessibility.ground_point_root_accessible` has exactly
these premises and conclusion:

```text
Checked registry →
InitialSource registry context root →
(∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
GroundRoots context root rootLabels →
Acc (fun next current => GeneralNominalCenteredSteps.Step registry root current next)
    (GeneralNominalCenteredSteps.initial context root)
```

`InitialSource` here is `GeneralNominalSourceFormation.InitialSource`.
`GroundRoots` is the existing finite closed-pattern interpretation predicate.
Internal source intervals may be nonpoint. The theorem has no compatibility,
simulation, producer, cover, depth-bound, model-inhabitation, or scheduling
premise. It uses the unrestricted centered Step, including centered refresh
and merges between differing site records. General unknown/nonpoint roots
remain outside this theorem; this is not the complete B4 statement.

`initial_source_accessible` additionally handles a centered `InitialSource`
whose root is point-valued, using the previously proved uniqueness of its
initial center representation. Its ground hypothesis explicitly supplies
finite labels for the represented initial context.

## Direct proof

1. `GeneralNominalRelationalMatching` restates recursive head matching with an
   arbitrary interpretation of captures. `actual_many_matched` instantiates it
   with the original shared-capture relation. `CenteredHeadMatching` uses
   readbacks at `plan.binder name`. `CenteredCaptureSchema` proves that actual
   capture origins occur as actual uses in the corresponding schema, including
   both nominal interval sides.
2. `CenteredCaptureLabels` chooses one normalized, minimum-mass finite label
   for each needed binder in the retrospective model. Repeated variable uses
   share this label. The proof does not assume that such labels already exist:
   head matching and scope/coverage produce them.
3. `CenteredProduction.production` derives finite meanings for every emitted
   child center, and bounds the substituted normalized head by the parent's
   label mass. It retains the ordinary preparation check for materialization.
   `GeneralPatternCoveredResult` proves stability when the *normalized result*
   is covered; unconditional normalization idempotence would be false.
4. `CenteredAncestry.sites_bounded` restricts the same centered model backwards
   along the trace and proves
   `depth + mass(site labels) ≤ mass(root labels)`. At an installation, the
   local producer and `checked_normalized_descent` supply the strict child
   decrease. The future installation bound uses the common **centered** model
   required by its guard, not an ordinary branch witness.
5. `CenteredEnumeration` reuses the existing invocation frontier, allocation
   pool, report enumeration, occurrence templates, and packet codes. Raw and
   centered site ledgers correspond by occurrence in both directions. For a
   centered merge, occurrence outputs suffice to bound source support; equal
   site records are unnecessary.
6. `GeneralNominalFiniteProgress` provides a relation-parametric missing-fact
   measure. Its centered basis contains semantic packet signatures, Known
   identities, alias pairs, ordinary equality pairs, and point observations.
   Every full Step adds a listed fact. Reachable enqueue is impossible because
   generated demands are registered. Centered refresh preserves raw models
   backwards through `Refines`; equality of raw model sets is unnecessary.
   Installation novelty is measured by the unchanged raw commitment/signature
   predicates, exactly as required by the actual centered constructor.

The proof is independent of the failed literal-erasure proposal. That earlier
counterexample remains valid and unchanged.

## Boundary and terminal execution

`GeneralNominalCenteredGroundBoundary.groundBoundary` changes only Initial to
require a point root with finite ground labels. Its Step, local predicates,
models, generated demands, and stability are the full centered definitions.
It proves the six structural V5 laws: `closure`, `stepModels`, `frontierLocal`,
`localIdentity`, `dictionaryRefl`, and `initialReorders`.

`progress` extends accessibility to every reachable state of this boundary.
`terminal` applies `terminal_of_accessible` and gives a finite actual centered
trace, halted endpoint, stability of the root and every generated demand,
and backwards model inclusion. `finalState`, `execution`, and `halted` choose
and certify that endpoint. This chooser takes checkedness and reachability
proofs; it is not yet a B4 `Executor.run` returning a diagnostic tree.
`treeExecution`, exact classification, and the complete V5 package are not
claimed.

## Selected guards and where trees

`CenteredTrace.generated_centered` now proves that every reachable generated
demand has a registered centered site. `CenteredSelection.selected_base_plan`
uses that registration and local selection to construct an ordinary installable
packet, with exact selected key and children, **assuming Joint applicability
and recovered merge closure**. Joint supplies the current journal-compatible
branch witness and agreement with prior choices.

Together with `CenteredInspection.selected_installable_iff`, the remaining
installation obligations are therefore explicit: Joint/merge closure, legacy
value support, and a model satisfying both the current center ledger and the
new plan. Their derivation from selection and reachability remains open.
The spec's §6.3 merge decision says:

> impl を選ぶ前、保留のままでも行う。

Selection alone cannot be used to erase the operational merge-closure guard.
Also, centered `Trusted` explanations may contain equations absent from legacy
`Support.Slice`; the centered decision guard has not been converted into the
retained value-support guard.

`guarded_selected_children` proves actual generated children for a stable,
installable selected plan. `CenteredWhere` shows that, at a stable reachable
snapshot, availability of such plans for every generated selected demand
implies generated-child closure and accessibility of the actual local where
relation. Literal emitted identities strictly increase, and the snapshot's
finite registered identities supply a reverse numerical bound. These results
retain the explicit `Available` premise; they are not unconditional
`generatedChildren` or `whereAccessible` fields.

## Allocation and nested centers

`CenteredAllocation` proves that ordinary allocation keys have purpose at most
6, while fresh center namespaces use purposes 7–9. The injective source encoding
separates these namespaces and distinguishes compound centers by clause and
position. For every trace with the derived installation bound, a fresh name
of purpose at least 7 is outside all listed raw source IDs. This does not say
that point centers or output binder centers are fresh: they intentionally
reuse their designated identities.

Every registered plan has its packet in the raw journal. Hence every centered
model of a reachable state satisfies the historical plan's complete equations.
`registered_nested_name` preserves actual schema-leaf equality to the binder
center; `registered_nested_argument` additionally gives its capture interval
bounds. `registered_child_names` preserves every emitted child's center bounds
and actual materialization schema. These are semantic invariants of the
existing ledger, not a new stored descriptor at every uninspected nested slot.
General allocation/model-extension and total nested-descriptor production
remain open.

## Trigger status

The spec's P/W trigger shares the same `b` center through the two children and
intends the equations `A = V b`, `A = V next`, `next = V b`, hence `b = V b`
and K2. The existing centered algebra and conditional rejection theorems still
apply. This change does not supply the full actual trace.

An audit found an important fixture distinction: `triggerLeafPlan` uses the
standalone W request with output targets 2/7/8. It is not the W emitted by P,
whose anchor and wrapped output share the same allocated target, as proved by
`SettledIntervalDeclarations.shared_anchor`. Its certificate cannot establish
the real P→W trace. Conversely, the old missing-provenance theorem cannot be
used to claim that the centered trace is blocked. Once the actual W packet is
installed, its empty requirements make it discharged; the existing discharged
support lemmas can justify that producer. The outstanding work is to construct
the emitted packets, their recorded facts, head-support witnesses and refreshes,
then an inhabited centered trace producing the cycle. No new owner decision
is needed.

## Review and checks

No registered `prover` launch surface was available; the primary constructed
these additive proofs. Separate read-only reviews checked the local producer,
the unrestricted accessibility quantifiers, all centered transition cases,
and the conditional boundary/selection/allocation statements. Only the primary
modified files. Existing source and design files retain their original byte
prefixes; the only tracked changes are appended imports and this note's index
entry. No git reference was changed.

Final commands from the repository root:

```text
cd lean && lake build Yulang.GeneralNominalCenteredGroundBoundary Yulang.GeneralNominalCenteredWhere
cd lean && lake build Yulang
cd lean && lake env lean Audit/CenteredDirectAccessibility.lean > /tmp/centered-direct-audit.log 2>&1
python3 /tmp/check-centered-direct.py
git diff --check
```

All five commands exited **0**. The focused build completed 815 jobs and the
aggregate build completed 2350 jobs. The new audit covers 100 exported theorem
declarations and reports only `propext`, `Classical.choice`, and `Quot.sound`.
The filesystem check confirms 15 new imported modules, exactly the two permitted
append-only tracked changes, the new audit/note, and branch `astra2/centered`.
Intermediate elaboration errors were repaired before these final checks. No
full trigger execution or unconditional selected-plan availability was verified.
