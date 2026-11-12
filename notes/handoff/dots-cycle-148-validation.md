# Cycle148 exact validation

## Public theorem axioms
```text
'Yulang.GeneralDictionarySupportConstraintTrace.recorded_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.at_recorded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.recorded_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.satisfies_append' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.trace_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.steps_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.trace_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.assignment_lost_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.trace_rejection_edge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportConstraintTrace.permuted_trace_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_known' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.source_unknown' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.remaining_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.not_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.models_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_raw_K2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_never_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_support_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.child_generated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportPointRefresh.reached_rejected_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.second_raw_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.second_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.second_improves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.remaining_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.not_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_models_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.no_further_point_revision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_generated_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_new_child_not_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRevisionStability.point_emission_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_self_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_ready' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_K2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.root_not_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.original_root_self_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.original_root_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.original_root_K2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.original_root_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.original_root_not_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.point_root_K2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.point_root_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportRootRejection.point_root_not_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalMergeCongruence.occurrences_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalMergeCongruence.lower_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMergeCongruence.upper_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMergeCongruence.mergeAtoms_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalMergeCongruence.merges_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalMergeCongruence.ofFn_aligned' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMergeCongruence.ofFn_merges_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalRepeatedHistoricalBranch.branch_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalRepeatedJournalFacts.same_after_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalRepeatedJournalFacts.projection_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalRepeatedMaterializationFacts.schema_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalRepeatedMaterializationFacts.branch_models_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalRepeatedMergeTransport.union_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalRepeatedMergeTransport.inter_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalRepeatedMergeTransport.equations_congr' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalRepeatedMergeTransport.merges_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalRepeatedMergeTransport.point_bounds_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalRepeatedMergeTransport.merges_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.coherent_of_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.coherent_of_point_aliases' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.projection_of_coherent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.coherent_of_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.compatible_of_coherent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.private_models_of_merges' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedCaptureFacts.branch_models_iff_residual' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedHistoricalBranch.merges_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedHistoricalBranch.branch_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedHistoricalBranch.merges_after_steps_of_source_ids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedHistoricalBranch.branch_after_steps_of_source_ids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedJournalFacts.coherent_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedJournalFacts.projection_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedMaterializationFacts.occurrence_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedMaterializationFacts.schema_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedMaterializationFacts.branch_models_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Full scoped gate
```text
FOCUSED-AXIOM-PASS: 206 declarations in cycle148 modules
```

## Exact theorem signatures
```lean
@Yulang.GeneralDictionarySupportConstraintTrace.recorded_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {events : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Recorded registry before focus after events →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after.current model ↔
        Yulang.GeneralNominalSaturationState.Models before.current model ∧
          Yulang.GeneralDictionarySupportConstraintTrace.Satisfies events model
@Yulang.GeneralDictionarySupportConstraintTrace.at_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSupportSteps.At registry before focus after →
    ∃ events, Yulang.GeneralDictionarySupportConstraintTrace.Recorded registry before focus after events
@Yulang.GeneralDictionarySupportConstraintTrace.recorded_at : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {events : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Recorded registry before focus after events →
    Yulang.GeneralNominalSupportSteps.At registry before focus after
@Yulang.GeneralDictionarySupportConstraintTrace.satisfies_append : ∀ {roles : Yulang.Roles.RoleDecls}
  (first last : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralDictionarySupportConstraintTrace.Satisfies (first ++ last) model ↔
    Yulang.GeneralDictionarySupportConstraintTrace.Satisfies first model ∧
      Yulang.GeneralDictionarySupportConstraintTrace.Satisfies last model
@Yulang.GeneralDictionarySupportConstraintTrace.trace_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start finish : Yulang.GeneralNominalSupport.Tracked roles}
  {events : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start finish events →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models finish.current model ↔
        Yulang.GeneralNominalSaturationState.Models start.current model ∧
          Yulang.GeneralDictionarySupportConstraintTrace.Satisfies events model
@Yulang.GeneralDictionarySupportConstraintTrace.steps_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start finish : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) start finish →
    ∃ events, Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start finish events
@Yulang.GeneralDictionarySupportConstraintTrace.trace_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start finish : Yulang.GeneralNominalSupport.Tracked roles}
  {events : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start finish events →
    Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) start finish
@Yulang.GeneralDictionarySupportConstraintTrace.assignment_lost_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start finish : Yulang.GeneralNominalSupport.Tracked roles}
  {events : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start finish events →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models start.current model →
        (¬Yulang.GeneralNominalSaturationState.Models finish.current model ↔
          ∃ event, event ∈ events ∧ ¬event.Holds model)
@Yulang.GeneralDictionarySupportConstraintTrace.trace_rejection_edge : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start finish : Yulang.GeneralNominalSupport.Tracked roles}
  {events : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start finish events →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models start.current model →
        ¬Yulang.GeneralNominalSaturationState.Models finish.current model →
          ∃ before after focus current event,
            Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) start before ∧
              Yulang.GeneralNominalSaturationState.Generated before.current root focus ∧
                Yulang.GeneralDictionarySupportConstraintTrace.Recorded registry before focus after current ∧
                  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) after finish ∧
                    Yulang.GeneralNominalSaturationState.Models before.current model ∧
                      ¬Yulang.GeneralNominalSaturationState.Models after.current model ∧
                        event ∈ current ∧ ¬event.Holds model
@Yulang.GeneralDictionarySupportConstraintTrace.permuted_trace_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start left right : Yulang.GeneralNominalSupport.Tracked roles}
  {first last : List (Yulang.GeneralDictionarySupportConstraintTrace.Event roles)},
  Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start left first →
    Yulang.GeneralDictionarySupportConstraintTrace.Trace registry root start right last →
      first.Perm last →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models left.current model ↔
            Yulang.GeneralNominalSaturationState.Models right.current model
Yulang.GeneralDictionarySupportPointRefresh.child_known : Yulang.GeneralNominalState.Known
  Yulang.GeneralDictionarySupportPointRefresh.refreshedState 2
Yulang.GeneralDictionarySupportPointRefresh.source_unknown : ¬Yulang.GeneralNominalState.Known
    Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context.state 2
Yulang.GeneralDictionarySupportPointRefresh.remaining_update : Yulang.GeneralNominalSupportSteps.At
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportRevisionStability.pointFinish
  Yulang.GeneralNominalFeedbackObstruction.root Yulang.GeneralDictionarySupportPointRefresh.after
Yulang.GeneralDictionarySupportPointRefresh.not_stable : ¬Yulang.GeneralNominalSupportSteps.Stable
    Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportRevisionStability.pointFinish
    Yulang.GeneralNominalFeedbackObstruction.root
Yulang.GeneralDictionarySupportPointRefresh.models_iff : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportPointRefresh.after.current m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current m
Yulang.GeneralDictionarySupportPointRefresh.reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralDictionarySupportPointRefresh.after
Yulang.GeneralDictionarySupportPointRefresh.child_linked : Yulang.GeneralNominalState.Linked
  Yulang.GeneralDictionarySupportPointRefresh.refreshedState Yulang.GeneralNominalFeedbackObstruction.child.demand
Yulang.GeneralDictionarySupportPointRefresh.child_raw_K2 : Yulang.GeneralNominalCycleK2.RootK2
  Yulang.GeneralDictionarySupportPointRefresh.refreshedState Yulang.GeneralNominalFeedbackObstruction.child.demand
Yulang.GeneralDictionarySupportPointRefresh.child_rejected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportPointRefresh.refreshed
  Yulang.GeneralNominalFeedbackObstruction.child Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionarySupportPointRefresh.child_never_expanded : ∀
  (next : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  next.site.occurrence = Yulang.GeneralNominalFeedbackObstruction.child →
    ¬Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalFeedbackObstruction.registry
        Yulang.GeneralDictionarySupportPointRefresh.refreshed next
Yulang.GeneralDictionarySupportPointRefresh.child_support_rejected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportPointRefresh.after
  Yulang.GeneralNominalFeedbackObstruction.child Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionarySupportPointRefresh.child_generated : Yulang.GeneralNominalSaturationState.Generated
  Yulang.GeneralDictionarySupportPointRefresh.after.current Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralNominalFeedbackObstruction.child
Yulang.GeneralDictionarySupportPointRefresh.reached_rejected_child : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
    Yulang.GeneralDictionarySupportPointRefresh.after ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportPointRefresh.after.current
      Yulang.GeneralNominalFeedbackObstruction.model ∧
    Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionarySupportPointRefresh.after.current
        Yulang.GeneralNominalFeedbackObstruction.root Yulang.GeneralNominalFeedbackObstruction.child ∧
      Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralNominalFeedbackObstruction.registry
        Yulang.GeneralDictionarySupportPointRefresh.after Yulang.GeneralNominalFeedbackObstruction.child
        Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionarySupportRevisionStability.second_raw_models : ∀
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionarySupportRevisionStability.secondRevision.snapshot m ↔
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryCurrentRevisionObstruction.revised.context.state m
Yulang.GeneralDictionarySupportRevisionStability.second_certified : Yulang.GeneralNominalReobservationSteps.Certified
  Yulang.GeneralDictionarySupportRevisionStability.secondRevision
Yulang.GeneralDictionarySupportRevisionStability.second_improves : Yulang.GeneralNominalReobservationSteps.Improves
  Yulang.GeneralDictionarySupportRevisionStability.secondRevision
Yulang.GeneralDictionarySupportRevisionStability.remaining_update : Yulang.GeneralNominalSupportSteps.At
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportRevisionObstruction.finish
  Yulang.GeneralNominalFeedbackObstruction.root
  (have __src := Yulang.GeneralDictionarySupportRevisionObstruction.finish;
  { source := __src.source, current := Yulang.GeneralDictionarySupportRevisionStability.twiceRevised,
    facts := __src.facts })
Yulang.GeneralDictionarySupportRevisionStability.not_stable : ¬Yulang.GeneralNominalSupportSteps.Stable
    Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportRevisionObstruction.finish
    Yulang.GeneralNominalFeedbackObstruction.root
Yulang.GeneralDictionarySupportRevisionStability.point_models_iff : ∀
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRevisionObstruction.finish.current m
Yulang.GeneralDictionarySupportRevisionStability.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context.state
Yulang.GeneralDictionarySupportRevisionStability.no_further_point_revision : ∀
  (next :
    Yulang.GeneralNominalReobservationSteps.Revision Yulang.GeneralDictionarySupportRevisionStability.twiceRevised),
  ¬Yulang.GeneralNominalReobservationSteps.Improves next
Yulang.GeneralDictionarySupportRevisionStability.point_models : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current Yulang.GeneralNominalFeedbackObstruction.model
Yulang.GeneralDictionarySupportRevisionStability.point_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralDictionarySupportRevisionStability.pointFinish
Yulang.GeneralDictionarySupportRevisionStability.point_report : Yulang.GeneralNominalRecursiveCandidates.report
    Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context
    Yulang.GeneralNominalFeedbackObstruction.declaration [(0, 0)] =
  Yulang.GeneralNominalUnaryCaptureFacts.captured
    Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context.state 0 0 0 (2, 2)
Yulang.GeneralDictionarySupportRevisionStability.point_children : ∀
  (check :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalFeedbackObstruction.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalFeedbackObstruction.declaration),
  Yulang.GeneralNominalAllocation.children Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context.state
      Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
      Yulang.GeneralNominalFeedbackObstruction.declaration check
      (Yulang.GeneralNominalRecursiveInspection.bindings
        Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context.state
        (Yulang.GeneralNominalRecursiveCandidates.report
          Yulang.GeneralDictionarySupportRevisionStability.twiceRevised.context
          Yulang.GeneralNominalFeedbackObstruction.declaration [(0, 0)])) =
    [Yulang.GeneralDictionaryCurrentRevisionObstruction.newChild]
Yulang.GeneralDictionarySupportRevisionStability.point_generated_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current
      Yulang.GeneralNominalFeedbackObstruction.root focus →
    focus = Yulang.GeneralNominalFeedbackObstruction.root ∨ focus = Yulang.GeneralNominalFeedbackObstruction.child
Yulang.GeneralDictionarySupportRevisionStability.point_new_child_not_generated : ¬Yulang.GeneralNominalSaturationState.Generated
    Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current Yulang.GeneralNominalFeedbackObstruction.root
    Yulang.GeneralDictionaryCurrentRevisionObstruction.newChild
Yulang.GeneralDictionarySupportRevisionStability.point_emission_gap : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
    Yulang.GeneralDictionarySupportRevisionStability.pointFinish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current
      Yulang.GeneralNominalFeedbackObstruction.model ∧
    Yulang.GeneralNominalReobservationSteps.PointClosed
        Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current.context.state ∧
      Yulang.GeneralDictionaryCurrentRevisionObstruction.newChild ∈
          Yulang.GeneralNominalAllocation.children
            Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current.context.state
            Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
            Yulang.GeneralNominalFeedbackObstruction.declaration
            Yulang.GeneralNominalFeedbackObstruction.declaration_checked
            (Yulang.GeneralNominalRecursiveInspection.bindings
              Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current.context.state
              (Yulang.GeneralNominalRecursiveCandidates.report
                Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current.context
                Yulang.GeneralNominalFeedbackObstruction.declaration [(0, 0)])) ∧
        ¬Yulang.GeneralNominalSaturationState.Generated
            Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current
            Yulang.GeneralNominalFeedbackObstruction.root Yulang.GeneralDictionaryCurrentRevisionObstruction.newChild
Yulang.GeneralDictionarySupportRootRejection.root_equal : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportPointRefresh.after.current m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 0).fst (m 2).fst
Yulang.GeneralDictionarySupportRootRejection.root_self_argument : Yulang.GeneralNominalFeedbackK2.Argument
  Yulang.GeneralDictionarySupportPointRefresh.after.current 0 0
Yulang.GeneralDictionarySupportRootRejection.root_linked : Yulang.GeneralNominalState.Linked
  Yulang.GeneralDictionarySupportPointRefresh.after.current.context.state
  Yulang.GeneralNominalFeedbackObstruction.root.demand
Yulang.GeneralDictionarySupportRootRejection.root_ready : ¬Yulang.GeneralNominalState.RootPending
    Yulang.GeneralDictionarySupportPointRefresh.after.current.context.state
    Yulang.GeneralNominalFeedbackObstruction.root.demand
Yulang.GeneralDictionarySupportRootRejection.root_K2 : Yulang.GeneralNominalFeedbackK2.RootK2
  Yulang.GeneralDictionarySupportPointRefresh.after.current Yulang.GeneralNominalFeedbackObstruction.root
Yulang.GeneralDictionarySupportRootRejection.root_rejected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportPointRefresh.after
  Yulang.GeneralNominalFeedbackObstruction.root Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionarySupportRootRejection.root_not_selected : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralNominalFeedbackObstruction.registry
      Yulang.GeneralDictionarySupportPointRefresh.after Yulang.GeneralNominalFeedbackObstruction.root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
Yulang.GeneralDictionarySupportRootRejection.original_root_self_argument : Yulang.GeneralNominalFeedbackK2.Argument
  Yulang.GeneralDictionarySupportRevisionObstruction.finish.current 0 0
Yulang.GeneralDictionarySupportRootRejection.original_root_ready : ¬Yulang.GeneralNominalState.RootPending
    Yulang.GeneralDictionarySupportRevisionObstruction.finish.current.context.state
    Yulang.GeneralNominalFeedbackObstruction.root.demand
Yulang.GeneralDictionarySupportRootRejection.original_root_K2 : Yulang.GeneralNominalFeedbackK2.RootK2
  Yulang.GeneralDictionarySupportRevisionObstruction.finish.current Yulang.GeneralNominalFeedbackObstruction.root
Yulang.GeneralDictionarySupportRootRejection.original_root_rejected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportRevisionObstruction.finish
  Yulang.GeneralNominalFeedbackObstruction.root Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionarySupportRootRejection.original_root_not_selected : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralNominalFeedbackObstruction.registry
      Yulang.GeneralDictionarySupportRevisionObstruction.finish Yulang.GeneralNominalFeedbackObstruction.root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
Yulang.GeneralDictionarySupportRootRejection.point_root_K2 : Yulang.GeneralNominalFeedbackK2.RootK2
  Yulang.GeneralDictionarySupportRevisionStability.pointFinish.current Yulang.GeneralNominalFeedbackObstruction.root
Yulang.GeneralDictionarySupportRootRejection.point_root_rejected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralDictionarySupportRevisionStability.pointFinish
  Yulang.GeneralNominalFeedbackObstruction.root Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionarySupportRootRejection.point_root_not_selected : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralNominalFeedbackObstruction.registry
      Yulang.GeneralDictionarySupportRevisionStability.pointFinish Yulang.GeneralNominalFeedbackObstruction.root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
Yulang.GeneralNominalMergeCongruence.occurrences_equivalent : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  {first last : Yulang.GeneralNominalAllocation.Bindings},
  Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.BindingEquivalent model) first last →
    ∀ (name : Nat),
      Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.IntervalEquivalent model)
        (Yulang.GeneralNominalAllocation.occurrences first name) (Yulang.GeneralNominalAllocation.occurrences last name)
Yulang.GeneralNominalMergeCongruence.lower_equivalent : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  {first last : List Yulang.GeneralSourceState.Interval},
  Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.IntervalEquivalent model) first last →
    Yulang.CommonNominalFullCarrier.Equivalent
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.lower first))
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.lower last))
Yulang.GeneralNominalMergeCongruence.upper_equivalent : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  {first last : List Yulang.GeneralSourceState.Interval},
  Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.IntervalEquivalent model) first last →
    Yulang.CommonNominalFullCarrier.Equivalent
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.upper first))
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.upper last))
Yulang.GeneralNominalMergeCongruence.mergeAtoms_iff : ∀ (before after : Yulang.GeneralNominalState.State)
  (oldRegistry newRegistry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  before.seed = after.seed →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment) {first last : Yulang.GeneralNominalAllocation.Bindings},
      Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.BindingEquivalent model) first
          last →
        ∀ (name : Nat),
          Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
              (Yulang.GeneralNominalMergeCongruence.mergeAtoms before oldRegistry invocation declaration first name) ↔
            Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
              (Yulang.GeneralNominalMergeCongruence.mergeAtoms after newRegistry invocation declaration last name)
Yulang.GeneralNominalMergeCongruence.merges_iff : ∀ (before after : Yulang.GeneralNominalState.State)
  (oldRegistry newRegistry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  before.seed = after.seed →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment) {first last : Yulang.GeneralNominalAllocation.Bindings},
      Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.BindingEquivalent model) first
          last →
        (Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.merges before oldRegistry invocation declaration first) ↔
          Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.merges after newRegistry invocation declaration last))
@Yulang.GeneralNominalMergeCongruence.ofFn_aligned : ∀ {n : Nat} (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (names : Fin n → Nat) (first last : Fin n → Yulang.GeneralSourceState.Interval),
  (∀ (i : Fin n), Yulang.GeneralNominalMergeCongruence.IntervalEquivalent model (first i) (last i)) →
    Yulang.GeneralNominalDemandMerging.All₂ (Yulang.GeneralNominalMergeCongruence.BindingEquivalent model)
      (List.ofFn fun i => (names i, first i)) (List.ofFn fun i => (names i, last i))
Yulang.GeneralNominalMergeCongruence.ofFn_merges_iff : ∀ (before after : Yulang.GeneralNominalState.State)
  (oldRegistry newRegistry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  before.seed = after.seed →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment) {n : Nat} (names : Fin n → Nat)
      (first last : Fin n → Yulang.GeneralSourceState.Interval),
      (∀ (i : Fin n), Yulang.GeneralNominalMergeCongruence.IntervalEquivalent model (first i) (last i)) →
        (Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.merges before oldRegistry invocation declaration
              (List.ofFn fun i => (names i, first i))) ↔
          Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.merges after newRegistry invocation declaration
              (List.ofFn fun i => (names i, last i))))
@Yulang.GeneralNominalRepeatedHistoricalBranch.branch_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ (binder : Nat),
                packet.declaration.inputNames = [binder] →
                  ∀ (oldLeft oldRight : Yulang.GeneralNominalInspection.Bounds packet.context.state),
                    oldDescriptor.arguments =
                        [Yulang.GeneralNominalState.Parameter.type oldLeft,
                          Yulang.GeneralNominalState.Parameter.type oldRight] →
                      Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                            packet.declaration =
                          [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                              [Yulang.GeneralNominalInspection.Query.variables [binder],
                                Yulang.GeneralNominalInspection.Query.variables [binder]]] →
                        ∀ (slot : Fin after.current.context.state.base.slots)
                          (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                          after.current.context.state.nominals slot = some descriptor →
                            ∀ (left right : Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                              descriptor.arguments =
                                  [Yulang.GeneralNominalState.Parameter.type left,
                                    Yulang.GeneralNominalState.Parameter.type right] →
                                Yulang.GeneralNominalInspection.queries after.current.context.state
                                      after.current.context.interpretation packet.declaration =
                                    [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                                        [Yulang.GeneralNominalInspection.Query.variables [binder],
                                          Yulang.GeneralNominalInspection.Query.variables [binder]]] →
                                  oldLeft.fst = oldLeft.snd →
                                    oldRight.fst = oldRight.snd →
                                      left.fst = left.snd →
                                        right.fst = right.snd →
                                          packet.context.state.base.source oldSlot =
                                              after.current.context.state.base.source slot →
                                            oldDescriptor.declaration.name = descriptor.declaration.name →
                                              packet.context.state.seed = after.current.context.state.seed →
                                                ∀
                                                  (checked :
                                                    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors
                                                      roles packet.declaration),
                                                  packet.declaration.requirements = [] →
                                                    ∀ (equation : Yulang.GeneralDeclarations.Equation),
                                                      packet.declaration.associated = [equation] →
                                                        packet.site.occurrence.demand.outputs =
                                                            [{ name := equation.name,
                                                                target :=
                                                                  after.current.context.state.base.source slot }] →
                                                          Yulang.GeneralNominalInspection.translate
                                                                after.current.context.state.constructors
                                                                after.current.context.interpretation
                                                                (Yulang.GeneralDeclarationPatterns.normalize
                                                                  equation.rhs) =
                                                              Yulang.GeneralNominalInspection.Query.nominal
                                                                descriptor.declaration.name
                                                                [Yulang.GeneralNominalInspection.Query.variables
                                                                    [binder],
                                                                  Yulang.GeneralNominalInspection.Query.variables
                                                                    [binder]] →
                                                            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                                              Yulang.GeneralNominalSaturationState.Models after.current
                                                                  model →
                                                                Yulang.GeneralNominalRecursiveCandidates.BranchModels
                                                                  registry after.current.context packet.site.occurrence
                                                                  packet.declaration checked [(slot, slot)] model
@Yulang.GeneralNominalRepeatedJournalFacts.same_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (slot : Fin packet.context.state.base.slots)
          (descriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals slot = some descriptor →
            packet.bounds = [(slot, slot)] →
              ∀ (binder : Nat) (left right : Yulang.GeneralNominalInspection.Bounds packet.context.state),
                descriptor.arguments =
                    [Yulang.GeneralNominalState.Parameter.type left, Yulang.GeneralNominalState.Parameter.type right] →
                  Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                        packet.declaration =
                      [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                          [Yulang.GeneralNominalInspection.Query.variables [binder],
                            Yulang.GeneralNominalInspection.Query.variables [binder]]] →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models after.current model →
                        Yulang.GeneralNominalRepeatedCaptureFacts.SameParameters model
                          (packet.context.state.base.source slot) descriptor.declaration.name
@Yulang.GeneralNominalRepeatedJournalFacts.projection_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ (oldBinder : Nat) (oldLeft oldRight : Yulang.GeneralNominalInspection.Bounds packet.context.state),
                oldDescriptor.arguments =
                    [Yulang.GeneralNominalState.Parameter.type oldLeft,
                      Yulang.GeneralNominalState.Parameter.type oldRight] →
                  Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                        packet.declaration =
                      [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                          [Yulang.GeneralNominalInspection.Query.variables [oldBinder],
                            Yulang.GeneralNominalInspection.Query.variables [oldBinder]]] →
                    ∀ (slot : Fin after.current.context.state.base.slots)
                      (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                      after.current.context.state.nominals slot = some descriptor →
                        ∀ (binder : Nat)
                          (left right : Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                          descriptor.arguments =
                              [Yulang.GeneralNominalState.Parameter.type left,
                                Yulang.GeneralNominalState.Parameter.type right] →
                            after.current.context.state.base.source slot = packet.context.state.base.source oldSlot →
                              descriptor.declaration.name = oldDescriptor.declaration.name →
                                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                  Yulang.GeneralNominalSaturationState.Models after.current model →
                                    Yulang.GeneralNominalRecursiveInspection.ProjectionModels
                                      after.current.context.state
                                      (Yulang.GeneralNominalBinaryCaptureFacts.captured after.current.context.state slot
                                        descriptor.declaration.name binder binder left right)
                                      model
Yulang.GeneralNominalRepeatedMaterializationFacts.schema_models : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration.outputNames = [] →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ (binder : Nat),
          binder ∈ declaration.inputNames →
            ∀ (left right : Yulang.GeneralNominalInspection.Bounds state),
              descriptor.arguments =
                  [Yulang.GeneralNominalState.Parameter.type left, Yulang.GeneralNominalState.Parameter.type right] →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalState.Models state model →
                    Yulang.GeneralNominalRepeatedCaptureFacts.SameParameters model (state.base.source slot)
                        descriptor.declaration.name →
                      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                          (Yulang.GeneralNominalAllocation.merges state registry invocation declaration
                            (Yulang.GeneralNominalRecursiveInspection.bindings state
                              (Yulang.GeneralNominalBinaryCaptureFacts.captured state slot descriptor.declaration.name
                                binder binder left right))) →
                        Yulang.GeneralNominalMaterialization.Models state declaration
                          (Yulang.GeneralNominalAllocation.capture state registry invocation declaration.id
                            (Yulang.GeneralNominalRecursiveInspection.bindings state
                              (Yulang.GeneralNominalBinaryCaptureFacts.captured state slot descriptor.declaration.name
                                binder binder left right)))
                          (Yulang.GeneralNominalBinaryCaptureFacts.captured state slot descriptor.declaration.name
                            binder binder left right)
                          (Yulang.GeneralNominalRepeatedMaterializationFacts.headSchema state slot
                            descriptor.declaration.name binder)
                          model
@Yulang.GeneralNominalRepeatedMaterializationFacts.branch_models_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
  declaration.requirements = [] →
    ∀ (equation : Yulang.GeneralDeclarations.Equation),
      declaration.associated = [equation] →
        ∀ (slot : Fin context.state.base.slots)
          (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
          context.state.nominals slot = some descriptor →
            ∀ (binder : Nat),
              binder ∈ declaration.inputNames →
                ∀ (left right : Yulang.GeneralNominalInspection.Bounds context.state),
                  descriptor.arguments =
                      [Yulang.GeneralNominalState.Parameter.type left,
                        Yulang.GeneralNominalState.Parameter.type right] →
                    Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration =
                        [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                            [Yulang.GeneralNominalInspection.Query.variables [binder],
                              Yulang.GeneralNominalInspection.Query.variables [binder]]] →
                      root.demand.outputs = [{ name := equation.name, target := context.state.base.source slot }] →
                        Yulang.GeneralNominalInspection.translate context.state.constructors context.interpretation
                              (Yulang.GeneralDeclarationPatterns.normalize equation.rhs) =
                            Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                              [Yulang.GeneralNominalInspection.Query.variables [binder],
                                Yulang.GeneralNominalInspection.Query.variables [binder]] →
                          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration
                                checked [(slot, slot)] model ↔
                              Yulang.GeneralNominalState.Models context.state model ∧
                                Yulang.GeneralNominalRepeatedCaptureFacts.SameParameters model
                                    (context.state.base.source slot) descriptor.declaration.name ∧
                                  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                                    (Yulang.GeneralNominalAllocation.merges context.state registry root.identity
                                      declaration
                                      (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                                        (Yulang.GeneralNominalRecursiveCandidates.report context declaration
                                          [(slot, slot)])))
@Yulang.GeneralNominalRepeatedMergeTransport.union_equivalent : ∀ {a b c d : Yulang.CommonNominalFullCarrier.Ty},
  Yulang.CommonNominalFullCarrier.Equivalent a c →
    Yulang.CommonNominalFullCarrier.Equivalent b d →
      Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalSyntax.Layer.union a b)
        (Yulang.CommonNominalSyntax.Layer.union c d)
@Yulang.GeneralNominalRepeatedMergeTransport.inter_equivalent : ∀ {a b c d : Yulang.CommonNominalFullCarrier.Ty},
  Yulang.CommonNominalFullCarrier.Equivalent a c →
    Yulang.CommonNominalFullCarrier.Equivalent b d →
      Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalSyntax.Layer.inter a b)
        (Yulang.CommonNominalSyntax.Layer.inter c d)
Yulang.GeneralNominalRepeatedMergeTransport.equations_congr : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (source : Nat) (first last : Yulang.Core.PresenceGeneration.TyTerm Nat),
  Yulang.CommonNominalFullCarrier.Equivalent
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model first)
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model last) →
    (Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.equations source first) ↔
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.equations source last))
Yulang.GeneralNominalRepeatedMergeTransport.merges_iff : ∀ (before after : Yulang.GeneralNominalState.State)
  (oldRegistry newRegistry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (binder : Nat),
  declaration.inputNames = [binder] →
    before.seed = after.seed →
      ∀ (oldLeft oldRight newLeft newRight : Yulang.GeneralSourceState.Interval)
        (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.CommonNominalFullCarrier.Equivalent (model oldLeft.fst).fst (model newLeft.fst).fst →
          Yulang.CommonNominalFullCarrier.Equivalent (model oldLeft.snd).fst (model newLeft.snd).fst →
            Yulang.CommonNominalFullCarrier.Equivalent (model oldRight.fst).fst (model newRight.fst).fst →
              Yulang.CommonNominalFullCarrier.Equivalent (model oldRight.snd).fst (model newRight.snd).fst →
                (Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                    (Yulang.GeneralNominalAllocation.merges before oldRegistry invocation declaration
                      [(binder, oldLeft), (binder, oldRight)]) ↔
                  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                    (Yulang.GeneralNominalAllocation.merges after newRegistry invocation declaration
                      [(binder, newLeft), (binder, newRight)]))
Yulang.GeneralNominalRepeatedMergeTransport.point_bounds_equivalent : ∀
  (before after : Yulang.GeneralNominalState.State) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models before model →
    Yulang.GeneralNominalState.Models after model →
      ∀ (oldSlot : Fin before.base.slots) (newSlot : Fin after.base.slots)
        (oldDescriptor : Yulang.GeneralNominalState.Descriptor before.base.slots)
        (newDescriptor : Yulang.GeneralNominalState.Descriptor after.base.slots),
        before.nominals oldSlot = some oldDescriptor →
          after.nominals newSlot = some newDescriptor →
            ∀ (index : Nat) (oldBounds : Yulang.GeneralNominalInspection.Bounds before)
              (newBounds : Yulang.GeneralNominalInspection.Bounds after),
              oldDescriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type oldBounds) →
                newDescriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type newBounds) →
                  oldBounds.fst = oldBounds.snd →
                    newBounds.fst = newBounds.snd →
                      before.base.source oldSlot = after.base.source newSlot →
                        oldDescriptor.declaration.name = newDescriptor.declaration.name →
                          Yulang.CommonNominalFullCarrier.Equivalent (model (before.base.source oldBounds.fst)).fst
                            (model (after.base.source newBounds.fst)).fst
@Yulang.GeneralNominalRepeatedMergeTransport.merges_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ (binder : Nat),
                packet.declaration.inputNames = [binder] →
                  ∀ (oldLeft oldRight : Yulang.GeneralNominalInspection.Bounds packet.context.state),
                    oldDescriptor.arguments =
                        [Yulang.GeneralNominalState.Parameter.type oldLeft,
                          Yulang.GeneralNominalState.Parameter.type oldRight] →
                      Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                            packet.declaration =
                          [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                              [Yulang.GeneralNominalInspection.Query.variables [binder],
                                Yulang.GeneralNominalInspection.Query.variables [binder]]] →
                        ∀ (slot : Fin after.current.context.state.base.slots)
                          (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                          after.current.context.state.nominals slot = some descriptor →
                            ∀ (left right : Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                              descriptor.arguments =
                                  [Yulang.GeneralNominalState.Parameter.type left,
                                    Yulang.GeneralNominalState.Parameter.type right] →
                                Yulang.GeneralNominalInspection.queries after.current.context.state
                                      after.current.context.interpretation packet.declaration =
                                    [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                                        [Yulang.GeneralNominalInspection.Query.variables [binder],
                                          Yulang.GeneralNominalInspection.Query.variables [binder]]] →
                                  oldLeft.fst = oldLeft.snd →
                                    oldRight.fst = oldRight.snd →
                                      left.fst = left.snd →
                                        right.fst = right.snd →
                                          packet.context.state.base.source oldSlot =
                                              after.current.context.state.base.source slot →
                                            oldDescriptor.declaration.name = descriptor.declaration.name →
                                              packet.context.state.seed = after.current.context.state.seed →
                                                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                                  Yulang.GeneralNominalSaturationState.Models after.current model →
                                                    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model
                                                      model
                                                      (Yulang.GeneralNominalAllocation.merges
                                                        after.current.context.state registry
                                                        packet.site.occurrence.identity packet.declaration
                                                        (Yulang.GeneralNominalRecursiveInspection.bindings
                                                          after.current.context.state
                                                          (Yulang.GeneralNominalRecursiveCandidates.report
                                                            after.current.context packet.declaration [(slot, slot)])))
Yulang.GeneralNominalSharedCaptureFacts.coherent_of_injective : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (source name : Nat) {n : Nat} (names : Fin n → Nat),
  Function.Injective names → Yulang.GeneralNominalSharedCaptureFacts.Coherent model source name names
Yulang.GeneralNominalSharedCaptureFacts.coherent_of_point_aliases : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ {n : Nat} (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state),
          (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
            (∀ (i : Fin n), (bounds i).fst = (bounds i).snd) →
              (∀ (i j : Fin n),
                  names i = names j → state.base.source (bounds i).fst = state.base.source (bounds j).fst) →
                Yulang.GeneralNominalSharedCaptureFacts.Coherent model (state.base.source slot)
                  descriptor.declaration.name names
Yulang.GeneralNominalSharedCaptureFacts.projection_of_coherent : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ {n : Nat} (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state),
          (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
            Yulang.GeneralNominalSharedCaptureFacts.Coherent model (state.base.source slot) descriptor.declaration.name
                names →
              Yulang.GeneralNominalRecursiveInspection.ProjectionModels state
                (Yulang.GeneralNominalLinearCaptureFacts.captured state slot descriptor.declaration.name names bounds)
                model
Yulang.GeneralNominalSharedCaptureFacts.coherent_of_projection : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (slot : Fin state.base.slots) (name : Nat) {n : Nat}
  (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state),
  Yulang.GeneralNominalRecursiveInspection.ProjectionModels state
      (Yulang.GeneralNominalLinearCaptureFacts.captured state slot name names bounds) model →
    Yulang.GeneralNominalSharedCaptureFacts.Coherent model (state.base.source slot) name names
Yulang.GeneralNominalSharedCaptureFacts.compatible_of_coherent : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ {n : Nat} (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state),
          (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
            Yulang.GeneralNominalSharedCaptureFacts.Coherent model (state.base.source slot) descriptor.declaration.name
                names →
              Yulang.GeneralNominalAllocation.Compatible
                (Yulang.GeneralNominalRecursiveInspection.bindings state
                  (Yulang.GeneralNominalLinearCaptureFacts.captured state slot descriptor.declaration.name names
                    bounds))
                model
@Yulang.GeneralNominalSharedCaptureFacts.private_models_of_merges : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (slot : Fin context.state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
  context.state.nominals slot = some descriptor →
    ∀ {n : Nat} (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds context.state),
      (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
        Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration =
            [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralNominalSharedCaptureFacts.Coherent model (context.state.base.source slot)
                  descriptor.declaration.name names →
                Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                    (Yulang.GeneralNominalAllocation.merges context.state registry root.identity declaration
                      (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                        (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)]))) →
                  Yulang.GeneralNominalState.Models
                    (Yulang.GeneralNominalRecursiveCandidates.privateState registry context root declaration
                      [(slot, slot)])
                    model
@Yulang.GeneralNominalSharedCaptureFacts.branch_models_iff_residual : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (slot : Fin context.state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
  context.state.nominals slot = some descriptor →
    ∀ {n : Nat} (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds context.state),
      (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
        Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration =
            [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked
                [(slot, slot)] model ↔
              Yulang.GeneralNominalState.Models context.state model ∧
                Yulang.GeneralNominalSharedCaptureFacts.Coherent model (context.state.base.source slot)
                    descriptor.declaration.name names ∧
                  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                      (Yulang.GeneralNominalAllocation.merges context.state registry root.identity declaration
                        (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                          (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)]))) ∧
                    Yulang.GeneralNominalMaterialization.Models context.state declaration
                      (Yulang.GeneralNominalAllocation.capture context.state registry root.identity declaration.id
                        (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                          (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)])))
                      (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)])
                      (Yulang.GeneralNominalRecursiveCandidates.generated registry context root declaration checked
                        [(slot, slot)])
                      model
@Yulang.GeneralNominalSharedHistoricalBranch.merges_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ {n : Nat} (names : Fin n → Nat)
                (oldBounds : Fin n → Yulang.GeneralNominalInspection.Bounds packet.context.state),
                (oldDescriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (oldBounds i)) →
                  Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                        packet.declaration =
                      [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                          (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                    ∀ (slot : Fin after.current.context.state.base.slots)
                      (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                      after.current.context.state.nominals slot = some descriptor →
                        ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                          (descriptor.arguments =
                              List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                            Yulang.GeneralNominalInspection.queries after.current.context.state
                                  after.current.context.interpretation packet.declaration =
                                [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                                    (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                              (∀ (i : Fin n), (oldBounds i).fst = (oldBounds i).snd) →
                                (∀ (i : Fin n), (bounds i).fst = (bounds i).snd) →
                                  packet.context.state.base.source oldSlot =
                                      after.current.context.state.base.source slot →
                                    oldDescriptor.declaration.name = descriptor.declaration.name →
                                      packet.context.state.seed = after.current.context.state.seed →
                                        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                          Yulang.GeneralNominalSaturationState.Models after.current model →
                                            Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                                              (Yulang.GeneralNominalAllocation.merges after.current.context.state
                                                registry packet.site.occurrence.identity packet.declaration
                                                (Yulang.GeneralNominalRecursiveInspection.bindings
                                                  after.current.context.state
                                                  (Yulang.GeneralNominalRecursiveCandidates.report after.current.context
                                                    packet.declaration [(slot, slot)])))
@Yulang.GeneralNominalSharedHistoricalBranch.branch_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ {n : Nat} (names : Fin n → Nat),
                (∀ (i : Fin n), names i ∈ packet.declaration.inputNames) →
                  ∀ (oldBounds : Fin n → Yulang.GeneralNominalInspection.Bounds packet.context.state),
                    (oldDescriptor.arguments =
                        List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (oldBounds i)) →
                      Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                            packet.declaration =
                          [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                              (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                        ∀ (slot : Fin after.current.context.state.base.slots)
                          (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                          after.current.context.state.nominals slot = some descriptor →
                            ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                              (descriptor.arguments =
                                  List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                                Yulang.GeneralNominalInspection.queries after.current.context.state
                                      after.current.context.interpretation packet.declaration =
                                    [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                                        (List.ofFn fun i =>
                                          Yulang.GeneralNominalInspection.Query.variables [names i])] →
                                  (∀ (i : Fin n), (oldBounds i).fst = (oldBounds i).snd) →
                                    (∀ (i : Fin n), (bounds i).fst = (bounds i).snd) →
                                      packet.context.state.base.source oldSlot =
                                          after.current.context.state.base.source slot →
                                        oldDescriptor.declaration.name = descriptor.declaration.name →
                                          packet.context.state.seed = after.current.context.state.seed →
                                            ∀
                                              (checked :
                                                Yulang.GeneralDeclarations.DeclarationChecked registry.constructors
                                                  roles packet.declaration),
                                              packet.declaration.requirements = [] →
                                                ∀ (equation : Yulang.GeneralDeclarations.Equation),
                                                  packet.declaration.associated = [equation] →
                                                    packet.site.occurrence.demand.outputs =
                                                        [{ name := equation.name,
                                                            target := after.current.context.state.base.source slot }] →
                                                      Yulang.GeneralNominalInspection.translate
                                                            after.current.context.state.constructors
                                                            after.current.context.interpretation
                                                            (Yulang.GeneralDeclarationPatterns.normalize equation.rhs) =
                                                          Yulang.GeneralNominalInspection.Query.nominal
                                                            descriptor.declaration.name
                                                            (List.ofFn fun i =>
                                                              Yulang.GeneralNominalInspection.Query.variables
                                                                [names i]) →
                                                        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                                          Yulang.GeneralNominalSaturationState.Models after.current
                                                              model →
                                                            Yulang.GeneralNominalRecursiveCandidates.BranchModels
                                                              registry after.current.context packet.site.occurrence
                                                              packet.declaration checked [(slot, slot)] model
@Yulang.GeneralNominalSharedHistoricalBranch.merges_after_steps_of_source_ids : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ {n : Nat} (names : Fin n → Nat)
                (oldBounds : Fin n → Yulang.GeneralNominalInspection.Bounds packet.context.state),
                (oldDescriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (oldBounds i)) →
                  Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                        packet.declaration =
                      [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                          (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                    ∀ (slot : Fin after.current.context.state.base.slots)
                      (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                      after.current.context.state.nominals slot = some descriptor →
                        ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                          (descriptor.arguments =
                              List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                            Yulang.GeneralNominalInspection.queries after.current.context.state
                                  after.current.context.interpretation packet.declaration =
                                [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                                    (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                              (∀ (i : Fin n),
                                  packet.context.state.base.source (oldBounds i).fst =
                                    after.current.context.state.base.source (bounds i).fst) →
                                (∀ (i : Fin n),
                                    packet.context.state.base.source (oldBounds i).snd =
                                      after.current.context.state.base.source (bounds i).snd) →
                                  packet.context.state.seed = after.current.context.state.seed →
                                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                      Yulang.GeneralNominalSaturationState.Models after.current model →
                                        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                                          (Yulang.GeneralNominalAllocation.merges after.current.context.state registry
                                            packet.site.occurrence.identity packet.declaration
                                            (Yulang.GeneralNominalRecursiveInspection.bindings
                                              after.current.context.state
                                              (Yulang.GeneralNominalRecursiveCandidates.report after.current.context
                                                packet.declaration [(slot, slot)])))
@Yulang.GeneralNominalSharedHistoricalBranch.branch_after_steps_of_source_ids : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ {n : Nat} (names : Fin n → Nat),
                (∀ (i : Fin n), names i ∈ packet.declaration.inputNames) →
                  ∀ (oldBounds : Fin n → Yulang.GeneralNominalInspection.Bounds packet.context.state),
                    (oldDescriptor.arguments =
                        List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (oldBounds i)) →
                      Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                            packet.declaration =
                          [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                              (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                        ∀ (slot : Fin after.current.context.state.base.slots)
                          (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                          after.current.context.state.nominals slot = some descriptor →
                            ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                              (descriptor.arguments =
                                  List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                                Yulang.GeneralNominalInspection.queries after.current.context.state
                                      after.current.context.interpretation packet.declaration =
                                    [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                                        (List.ofFn fun i =>
                                          Yulang.GeneralNominalInspection.Query.variables [names i])] →
                                  (∀ (i : Fin n),
                                      packet.context.state.base.source (oldBounds i).fst =
                                        after.current.context.state.base.source (bounds i).fst) →
                                    (∀ (i : Fin n),
                                        packet.context.state.base.source (oldBounds i).snd =
                                          after.current.context.state.base.source (bounds i).snd) →
                                      packet.context.state.base.source oldSlot =
                                          after.current.context.state.base.source slot →
                                        oldDescriptor.declaration.name = descriptor.declaration.name →
                                          packet.context.state.seed = after.current.context.state.seed →
                                            ∀
                                              (checked :
                                                Yulang.GeneralDeclarations.DeclarationChecked registry.constructors
                                                  roles packet.declaration),
                                              packet.declaration.requirements = [] →
                                                ∀ (equation : Yulang.GeneralDeclarations.Equation),
                                                  packet.declaration.associated = [equation] →
                                                    packet.site.occurrence.demand.outputs =
                                                        [{ name := equation.name,
                                                            target := after.current.context.state.base.source slot }] →
                                                      Yulang.GeneralNominalInspection.translate
                                                            after.current.context.state.constructors
                                                            after.current.context.interpretation
                                                            (Yulang.GeneralDeclarationPatterns.normalize equation.rhs) =
                                                          Yulang.GeneralNominalInspection.Query.nominal
                                                            descriptor.declaration.name
                                                            (List.ofFn fun i =>
                                                              Yulang.GeneralNominalInspection.Query.variables
                                                                [names i]) →
                                                        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                                          Yulang.GeneralNominalSaturationState.Models after.current
                                                              model →
                                                            Yulang.GeneralNominalRecursiveCandidates.BranchModels
                                                              registry after.current.context packet.site.occurrence
                                                              packet.declaration checked [(slot, slot)] model
@Yulang.GeneralNominalSharedJournalFacts.coherent_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (slot : Fin packet.context.state.base.slots)
          (descriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals slot = some descriptor →
            packet.bounds = [(slot, slot)] →
              ∀ {n : Nat} (names : Fin n → Nat)
                (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds packet.context.state),
                (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                  Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                        packet.declaration =
                      [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                          (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models after.current model →
                        Yulang.GeneralNominalSharedCaptureFacts.Coherent model (packet.context.state.base.source slot)
                          descriptor.declaration.name names
@Yulang.GeneralNominalSharedJournalFacts.projection_after_steps : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralNominalSupportSteps.Step registry root) before after →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet ∈ before.current.packets →
        ∀ (oldSlot : Fin packet.context.state.base.slots)
          (oldDescriptor : Yulang.GeneralNominalState.Descriptor packet.context.state.base.slots),
          packet.context.state.nominals oldSlot = some oldDescriptor →
            packet.bounds = [(oldSlot, oldSlot)] →
              ∀ {n : Nat} (oldNames names : Fin n → Nat)
                (oldBounds : Fin n → Yulang.GeneralNominalInspection.Bounds packet.context.state),
                (oldDescriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (oldBounds i)) →
                  Yulang.GeneralNominalInspection.queries packet.context.state packet.context.interpretation
                        packet.declaration =
                      [Yulang.GeneralNominalInspection.Query.nominal oldDescriptor.declaration.name
                          (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [oldNames i])] →
                    ∀ (slot : Fin after.current.context.state.base.slots)
                      (descriptor : Yulang.GeneralNominalState.Descriptor after.current.context.state.base.slots),
                      after.current.context.state.nominals slot = some descriptor →
                        ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds after.current.context.state),
                          (descriptor.arguments =
                              List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                            (∀ (i j : Fin n), names i = names j → oldNames i = oldNames j) →
                              after.current.context.state.base.source slot = packet.context.state.base.source oldSlot →
                                descriptor.declaration.name = oldDescriptor.declaration.name →
                                  ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                                    Yulang.GeneralNominalSaturationState.Models after.current model →
                                      Yulang.GeneralNominalRecursiveInspection.ProjectionModels
                                        after.current.context.state
                                        (Yulang.GeneralNominalLinearCaptureFacts.captured after.current.context.state
                                          slot descriptor.declaration.name names bounds)
                                        model
Yulang.GeneralNominalSharedMaterializationFacts.occurrence_iff : ∀ (state : Yulang.GeneralNominalState.State)
  (slot : Fin state.base.slots) (head : Nat) {n : Nat} (names : Fin n → Nat)
  (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state) (name : Nat) (pair : Nat × Nat),
  pair ∈
      Yulang.GeneralNominalAllocation.occurrences
        (Yulang.GeneralNominalRecursiveInspection.bindings state
          (Yulang.GeneralNominalLinearCaptureFacts.captured state slot head names bounds))
        name ↔
    ∃ j, names j = name ∧ (state.base.source (bounds j).fst, state.base.source (bounds j).snd) = pair
Yulang.GeneralNominalSharedMaterializationFacts.schema_models : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration.outputNames = [] →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ {n : Nat} (names : Fin n → Nat),
          (∀ (i : Fin n), names i ∈ declaration.inputNames) →
            ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state),
              (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  Yulang.GeneralNominalState.Models state model →
                    Yulang.GeneralNominalSharedCaptureFacts.Coherent model (state.base.source slot)
                        descriptor.declaration.name names →
                      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                          (Yulang.GeneralNominalAllocation.merges state registry invocation declaration
                            (Yulang.GeneralNominalRecursiveInspection.bindings state
                              (Yulang.GeneralNominalLinearCaptureFacts.captured state slot descriptor.declaration.name
                                names bounds))) →
                        Yulang.GeneralNominalMaterialization.Models state declaration
                          (Yulang.GeneralNominalAllocation.capture state registry invocation declaration.id
                            (Yulang.GeneralNominalRecursiveInspection.bindings state
                              (Yulang.GeneralNominalLinearCaptureFacts.captured state slot descriptor.declaration.name
                                names bounds)))
                          (Yulang.GeneralNominalLinearCaptureFacts.captured state slot descriptor.declaration.name names
                            bounds)
                          (Yulang.GeneralNominalLinearMaterializationFacts.headSchema state slot
                            descriptor.declaration.name names)
                          model
@Yulang.GeneralNominalSharedMaterializationFacts.branch_models_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
  declaration.requirements = [] →
    ∀ (equation : Yulang.GeneralDeclarations.Equation),
      declaration.associated = [equation] →
        ∀ (slot : Fin context.state.base.slots)
          (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
          context.state.nominals slot = some descriptor →
            ∀ {n : Nat} (names : Fin n → Nat),
              (∀ (i : Fin n), names i ∈ declaration.inputNames) →
                ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds context.state),
                  (descriptor.arguments = List.ofFn fun i => Yulang.GeneralNominalState.Parameter.type (bounds i)) →
                    Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration =
                        [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                            (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i])] →
                      root.demand.outputs = [{ name := equation.name, target := context.state.base.source slot }] →
                        Yulang.GeneralNominalInspection.translate context.state.constructors context.interpretation
                              (Yulang.GeneralDeclarationPatterns.normalize equation.rhs) =
                            Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                              (List.ofFn fun i => Yulang.GeneralNominalInspection.Query.variables [names i]) →
                          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration
                                checked [(slot, slot)] model ↔
                              Yulang.GeneralNominalState.Models context.state model ∧
                                Yulang.GeneralNominalSharedCaptureFacts.Coherent model (context.state.base.source slot)
                                    descriptor.declaration.name names ∧
                                  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
                                    (Yulang.GeneralNominalAllocation.merges context.state registry root.identity
                                      declaration
                                      (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                                        (Yulang.GeneralNominalRecursiveCandidates.report context declaration
                                          [(slot, slot)])))
```
