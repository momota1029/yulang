# Centered head choice and post-choice output errors: V6

Status: Draft — additive definitions and local laws; no V6 composition.
Date: 2026-11-14.
Baseline: `87487e1a7`, `astra2/centered`.
Scope: centered-15. The operational Step and Initial predicate are unchanged.

## Authority and separation

The centered-15 owner clarification is authoritative: unnamed arguments are
inputs, named arguments are outputs, and a merged demand retains all output
requests, including a request present at only one occurrence. Outputs never
filter head candidates or resolve ambiguity. The supervisor chose a genuine
post-choice `OutputConflict` rejection in an additive successor target.

The checked-out [§6.3](../../spec/06-roles.md) states
「すべての名前なしの引数が同じものを指す」 as the merge condition and
「二つの関連型の出力を等しいとし、需要を一つにまとめる」.
It also states 「それまでに積まれた制約と合わなければ、その時点で型エラーになる」
after the implementation's associated equation is added. §6.2 says overlapping
implementations are ambiguous. At this baseline the additional literal
named/unnamed clarification is not yet present in the checked-out spec; this
note records the current owner message as its source, without editing the spec.

Thus the first alias fixture has one head candidate `R int`, followed by a
conflict between the retained `out = int` and chosen `out = list int`. With two
visible `impl R int` declarations, different outputs cannot choose between
them: the head result is ambiguous. The frozen G″ classifier is not reused.
This continues the correction in
[the output-conflict audit](2026-11-14-centered-output-conflict.md).

## New definitions

### Head applicability

[GeneralNominalCenteredHeadCandidates](../../lean/Yulang/GeneralNominalCenteredHeadCandidates.lean)
defines `inputs root` by preserving identity, role and unnamed intervals and
erasing the output-request list. `Prepared` is the existing `HeadReady` applied
to that input projection: metadata, linked inputs, fresh allocation, a finished
head report and a model of the head's private constraints/projections. It has
no `RequestReady`, named-output `Consistent`, or `Joint` premise. `Survivor`
adds visible checked declaration membership and the existing child allocation.
Solving the child demands remains separate from matching the head.

`Failed` and `InspectionPending` use this same head-only preparation. The
concrete boundary applies input projection to the raw root/candidate K2 tests
and uses head-only preparation for the centered candidate-cycle test. It keeps
the justified-head decision guard and registration/merge-closure guard. Those
inspect inputs and administrative state, not whether named outputs fit a
candidate. In particular, missing output-schema coverage is not a pending rule.

Proved: `prepared_ignores_outputs`, `survivor_ignores_outputs`,
`old_prepared_head`, `old_survivor_head`, `survivor_children_functional`, and
`unique_excludes_two`. Output-erasure invariance fixes the explicit demand
requests at a fixed context; it does not erase existing journal constraints or
claim arbitrary changes to the whole state leave matching unchanged.

### Retaining the entire class's requests

[GeneralNominalCenteredHeadOutputs.requests](../../lean/Yulang/GeneralNominalCenteredHeadOutputs.lean)
collects the output lists of **all registered raw sites** whose occurrence
identities are in the focus's alias class. A membership test, not a positional
zip/intersection of two lists, determines retention. Duplicates are harmless
conjuncts. This is an additive class view; the raw merge operation is unchanged.

`mem_requests_iff` characterizes membership exactly. `request_retained` and
`same_class_requests` show retention and representative-independent membership.
`one_sided_request` proves that merging an empty-request occurrence with a
registered requested occurrence retains the latter's request. It is a property
of the merge function, not a new theorem that a particular merge Step is enabled.

### Chosen effects and a new conflict

`Frame` describes a prospective plan at the current registry/context, with
registered raw and centered input sites, the chosen key and head preparation.
It does not require the plan to be installed or to satisfy the old installation
guards. All class requests use this one plan's associated equations and shared
center binders.

`HeadEquations` contains the input center intervals, fits for head variables,
and the actual head schema. It excludes named equations and child obligations.
`OutputEquations` contains the schema for every retained named request and
`EqualOutputs`, which requires every same-name pair of targets in the class to
be equivalent in the model.

`ChosenHead registry state root key model` requires a unique head key and a
prospective frame whose head equations hold. `ChosenClassEffects` additionally
requires its output equations. Both require `EffectsReady`, the explicit
coverage condition described below. This condition belongs to effect
interpretation; it is absent from `Prepared` and `Survivor`.

The new conflict is exactly:

```lean
(∃ model, Models state model ∧ ChosenHead registry state root key model) ∧
  ¬ ∃ model, Models state model ∧ ChosenClassEffects registry state root key model
```

The positive half provides an inhabited current centered model and a feasible
head before testing outputs. It distinguishes an output extension failure
from an already inconsistent journal or an unrealizable head. The negative
half ranges over **all eligible frames**, so choosing one bad representative
cannot manufacture an error.

Proved: `conflict_inhabited`, `conflict_not_preexisting`, `conflict_unique`,
`conflict_excludes_ambiguity`, `effects_equal_outputs`, and
`empty_outputs_no_conflict`. `no_conflict_iff_effects` gives the exact common-model
equivalence **under the positive chosen-head baseline**. The concrete boundary's
`selected_has_effects` retains that hypothesis; it does not establish it from
reachability or head matching.

### Explicit coverage limit of this intermediate implementation

`EffectsReady` requires an explicit associated equation for every retained
request and `outputSchema.unknown = false`. Both checks matter: the old
`rootRequests` translation can omit a missing explicit equation even when the
schema's unknown flag is false. Checked declarations may instead use a role
default, and defaults use the separate `Roles.Term` representation. No generic
default-to-centered-schema interpretation bridge is added in this turn.

Consequently this is a coverage-gated concrete conflict interface, not yet a
complete classifier for all source programs. Role defaults and unsupported
translations cannot yield a certified conflict through this API. Their absence
does not eliminate a head or create pending; it leaves the positive
chosen-head baseline unavailable. In that case `¬ OutputConflict` alone is
insufficient to establish output consistency, even though the total local
classifier can select. Discharging or extending this coverage interface is an
implementation obligation, not a further language choice.

## Every V6 difference from V5

[B4TargetV6](../../lean/Yulang/B4TargetV6.lean) keeps V5's vocabulary, executor,
Initial quantifiers, reachability, tree/result types and five-clause statement.
The boundary extends V5 through a named `toV5` projection and adds the keyed
`OutputConflict` predicate. The abstract inherited Survivor slot is interpreted
as head applicability by the concrete boundary above.

| Clause | Change |
| --- | --- |
| `RejectReason` | After the existing unknown-root exclusion and K2 alternatives, add a unique-head conflict beside the zero-survivor case, under the existing inspection-pending exclusion. |
| `Local.rejected`, `Classify.rejected` | Use V6 RejectReason. |
| `Local.selected`, `Classify.selected` | Require `¬ OutputConflict` for the unique head; the recursive dictionary premises are unchanged. |
| pending, inspection pending, ambiguous constructors | Same clauses and priorities as V3/V5, now using head-only observations at this concrete boundary. |
| `SaturationTotal` | Exactly V5's predicate on `toV5`, including actual Steps, stability and model restriction. |
| `Exact` | Same quantifiers and resolution relation, with V6 Local. |
| `OrderIndependent` | Exactly V5's predicate on `toV5`; the dictionary equivalence contract is unchanged. |
| `DictionarySound` | Same quantifiers and Evidence, with V6 Classify. |
| `NoFalseRejection` | Same quantifiers, with V6 RejectReason. |
| `Statement` | Same five-clause conjunction in the same order, using the replacements above. |

V6 uses the existing `.rejected` diagnostic; the new reason is carried in the
judgment, not a fifth tree constructor. A conflict alternative itself requires
`Unique`, even for an abstract boundary that supplies an arbitrary conflict
predicate. Thus two distinct surviving head keys cannot be overridden by this
new reason. Root unknown heads still defer first; root/candidate K2 still
precede ambiguity; an inspection deferral still precedes ordinary head choice.

Generic proofs are `prior_rejection`, `output_conflict_rejected`,
`ambiguous_not_rejected`, `selected_not_rejected`, `local_functional`,
`local_total`, `ambiguous_only`, and `selected_clear`.
Generic totality requires `SurvivorChildrenFunctional`; the concrete checked
registry discharges it. `PreexistingInconsistency` is explicitly separate and
does not add a fifth rejection reason. V6 does not assert that arbitrary empty
model states must produce a diagnostic independently of Local.
In particular, a merge that has already made Models empty is outside this new
prospective-conflict reason. No universal diagnosis of earlier inconsistency
is claimed.

## Status of the twelve G′ bridges

The new concrete boundary is
`GeneralNominalCenteredHeadBoundary.boundary roles`. Its Step, Initial, Stable,
Generated, Models, Evidence and registry predicates are the existing ones.
There is no V6 skeleton or composition theorem in this change. The following
table concerns the corresponding bridge statements, rather than a value of
the V5 bridge structure (whose Local is necessarily the old judgment).

| G′ bridge | Transfer status for the head-only boundary |
| --- | --- |
| progress | Proved unchanged: `GeneralNominalCenteredHeadTransfers.progress`; reuses the existing accessibility theorem. |
| execution | Operational trace projection can be reused for the existing final-state function. Not packaged as a V6 executor here. |
| halted | Same operational reuse; no new V6 executor here. |
| closure | Proved unchanged: `GeneralNominalCenteredHeadTransfers.closure`. |
| stepModels | Proved unchanged: `GeneralNominalCenteredHeadTransfers.stepModels`. |
| frontierLocal | Reproved for the new classifier: `GeneralNominalCenteredHeadBoundary.frontierLocal`. |
| localIdentity | New frontier protocol definition: `GeneralNominalCenteredHeadBoundary.localIdentity`. |
| whereAccessible | Needs a head-Survivor version of the existing registered-site/child-identity bound; old selected-to-old-Local is not available. Not proved here. |
| treeExecution | Rebuild the diagnostic using V6 frontiers after the new child-accessibility proof. The old tree component is not reused as an exact V6 diagnostic. |
| canonicalLocalOrder | Needs the new observations, class requests and effects transported through packet/plan correspondence. See below. |
| dictionaryRefl | Proved unchanged: `GeneralNominalCenteredHeadTransfers.dictionaryRefl`. |
| initialReorders | Proved unchanged: `GeneralNominalCenteredHeadTransfers.initialReorders`. |

Seven bridge analogues are proved here. The five structural transfers have only
their original checked/reachable/transition premises. The two local protocol
laws require no reachable-state hypothesis; frontier exactness uses checkedness.

Canonical registry normalization and the operational permutation simulation
remain usable because Step is unchanged. Their old Local clause is insufficient:
the new proof must transport `HeadCandidates.Survivor` and `InspectionPending`,
alias-class request membership, eligible `Frame`s, `EffectsReady`, and the
existence/nonexistence of common centered models with the chosen effects.
This must hold both at fixed registry across corresponding states and under
registry reordering. A new canonical executor's `LiftedExit` must refer to V6
Local. The current executor chooses an exit by agreement on **old** Local;
that agreement alone does not imply agreement on these new observations.

## Remaining production and semantic obligations

1. **Head realization and complete output interpretation.** At a reachable,
   merge-closed, safe unique head, construct the positive chosen-head baseline
   used by `selected_has_effects`. This includes a registered frame, center
   model extension and complete effect coverage. Defaults and unsupported
   schemas must be interpreted, not turned into another deferral or filter.
2. **Effect soundness/completeness and class coherence.** Connect the schemas
   to all source associated equations, including defaults, and prove that
   alias representatives and permissible center readbacks yield equivalent
   chosen effects. `same_class_requests` alone proves only request membership.
   This interface covers the focus class's requested associated outputs;
   newly emitted where-clause output equations belong to the subsequent
   production/child-class proof, not this output schema.
3. **Output-effect coverage at installation.** The named new obligation is
   `GeneralNominalCenteredHeadOutputs.OutputEffectCoverage`:

   ```lean
   ∀ model, Models after model → ChosenClassEffects registry before root key model
   ```

   The successor production proof must establish it for successful installation
   (and preserve it through later merges that add requests). Together with model
   restriction it ensures every resulting model satisfies all class requests.
   An existential compatible model is weaker and is not enough.
4. **Successful production.** Replace the old output-sensitive installation
   gates additively with the head/effect split; prove value support, emission
   and child-edge coverage for stable selected classes. A diagnostic conflict
   need not install a contradictory packet, but a successful selection must
   carry the whole class's effects. `GeneratedChildren` remains open.
5. **V6 execution/composition.** Rebuild the Local-dependent bridges listed
   above and the successor skeleton. EvidenceNode remains the other worker's
   responsibility; this note does not treat its old statement as a V6 proof.

No Step is modified this turn. It still uses the historical output-sensitive
Prepared/Joint/common-model gates, so agreement of the new Local with successful
installation is not claimed. No source trace to the new conflict diagnostic,
V6 Statement, or complete source-language output coverage is proved here.
Conversely, the unchanged Step can still install using its output-filtered
candidate guard where the new head-only Local would report ambiguity. The
successor diagnostic is not an operational repair by itself.

The prover role is unavailable in this checkout; the primary constructed these
bounded local proofs, with separate source and final review. Validation is by
the targeted warning-failing build, the aggregate builds and a new dedicated
audit, as reported with the handoff.

The fresh independent review found no logical defect within this partial API.
It confirmed the absence of prospective named-output filtering in the new
candidate, decision and K2 predicates, and the scope of the seven field
analogues. It also checked that a missing frame cannot manufacture a conflict.

## Proof premises and validation

There is no unproved global premise hidden behind the seven field analogues.
The five structural theorems retain the ordinary checked/reachable, halted,
Step or initial-state hypotheses of their respective fields. Generic V6
`local_total` assumes survivor-child functionality; concrete `local_total`
derives it from `Checked registry`. Conflict rejection assumes `SafeKnown`,
which excludes the higher-priority pending/K2 cases. `selected_has_effects`
and `no_conflict_iff_effects` retain exactly this additional, undischarged
realization hypothesis:

```lean
∃ model, Models state model ∧ ChosenHead registry state root key model
```

Its coverage and model-extension components are not established by the new
head-survivor laws. No theorem claims selected implies installable. The named
production obligation `OutputEffectCoverage`, source interpretation/coherence,
and the remaining V6 bridges above are definitions or future proof work, not
assumptions of a claimed complete composition.

The exact declaration inventory is the dedicated
[audit file](../../lean/Audit/GeneralNominalCenteredHead.lean): 44 theorem checks,
with dependencies contained in `propext`, `Classical.choice`, and `Quot.sound`.
Final commands and exit codes from the repository root:

```text
cd lean && lake build --wfail Yulang.B4TargetV6 Yulang.GeneralNominalCenteredHeadCandidates Yulang.GeneralNominalCenteredHeadOutputs Yulang.GeneralNominalCenteredHeadBoundary Yulang.GeneralNominalCenteredHeadTransfers
exit 0
cd lean && lake build --wfail
exit 0
cd lean && lake build Yulang
exit 0
cd lean && lake env lean Audit/GeneralNominalCenteredHead.lean
exit 0
git diff --check
exit 0
```

During construction, the first targeted build of `no_conflict_iff_effects`
exited 1 because this Lean environment does not provide the shorthand lemma
used for double-negation elimination. Its final proof uses an explicit
classical case split; the commands above are the successful final checks.
The scope check confirms that the only old-file changes are appended imports
and the appended design-index entry; all five new Lean modules are imported.
