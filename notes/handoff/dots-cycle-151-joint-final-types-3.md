# Cycle151 final Joint theorem types, part3/3

```text
          Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
              Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
              (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11) 3 ∧
            (¬∃ p,
                  p ∈ Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets ∧
                    p.site.occurrence = Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10) ∧
              ¬∃ p,
                  p ∈ Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets ∧
                    p.site.occurrence = Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.parent_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      Yulang.GeneralNominalExamples.displayRoot 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.child_instance : ∀ (n : Nat)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) 3 []
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.child_evidence : ∀ (n : Nat)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
      (Yulang.CommonRoleOutermostResolver.Dictionary.node 3 [])
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.full_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.edges_exact : Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.edges =
  [(Yulang.GeneralNominalExamples.displayRoot, Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10),
    (Yulang.GeneralNominalExamples.displayRoot, Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11)]
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.generated_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot focus →
    focus = Yulang.GeneralNominalExamples.displayRoot ∨
      focus = Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10 ∨
        focus = Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.reachable_full_evidence : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current Yulang.GeneralNominalExamples.model
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
Yulang.GeneralDictionaryEarlyMergeScalarReadback.parent_selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children)
Yulang.GeneralDictionaryEarlyMergeScalarReadback.supported_parent : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children)
Yulang.GeneralDictionaryEarlyMergeScalarReadback.classified : Yulang.B4TargetV3.Classify
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Result.selected Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload)
Yulang.GeneralDictionaryEarlyMergeScalarReadback.actual_classified_evidence : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.B4TargetV3.Classify
        (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
        Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
        Yulang.GeneralNominalExamples.displayRoot
        (Yulang.CommonRoleOutermostResolver.Result.selected Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload) ∧
      ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
            assignment →
          Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
            Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
            Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
Yulang.GeneralDictionaryEarlyMergeScalarStable.models_of_source : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current m
Yulang.GeneralDictionaryEarlyMergeScalarStable.varying_model : ∀ (name : Nat),
  2 ≤ name →
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      (Yulang.GeneralDictionaryEarlyMergeScalarStable.varying name)
Yulang.GeneralDictionaryEarlyMergeScalarStable.refresh_large_unknown : ∀
  (next : Yulang.GeneralNominalCandidates.Context)
  (certificate :
    Yulang.GeneralNominalCycleSteps.Refresh Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current next)
  (source : Nat), 2 ≤ source → ¬Yulang.GeneralNominalState.Known next.state source
Yulang.GeneralDictionaryEarlyMergeScalarStable.context_complete : Yulang.GeneralNominalSaturationState.ContextComplete
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
Yulang.GeneralDictionaryEarlyMergeScalarStable.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  Yulang.GeneralDictionaryEarlyMergeScalarClassification.current.state
Yulang.GeneralDictionaryEarlyMergeScalarStable.sameInputs_no_cross : ∀ (n : Nat),
  ¬Yulang.GeneralNominalFeedbackSites.SameInputs Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralDictionaryEarlyMergeScalarJoint.rootSite (Yulang.GeneralDictionaryEarlyMergeScalarExample.site n)
Yulang.GeneralDictionaryEarlyMergeScalarStable.merges_closed : ∀
  (first last : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  first ∈ Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.sites →
    last ∈ Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.sites →
      Yulang.GeneralNominalFeedbackSites.SameInputs Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current first
          last →
        Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          first.occurrence.identity last.occurrence.identity
Yulang.GeneralDictionaryEarlyMergeScalarStable.installs_committed : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot p.site.occurrence →
    Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current p →
      Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current p
Yulang.GeneralDictionaryEarlyMergeScalarStable.feedback_stable : Yulang.GeneralNominalFeedbackSteps.Stable
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeScalarStable.stable : Yulang.GeneralNominalSupportSteps.Stable
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeScalarStable.stable_classified_dictionary : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
      Yulang.B4TargetV3.Classify
          (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
          Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
          Yulang.GeneralDictionaryEarlyMergeScalarExample.finish Yulang.GeneralNominalExamples.displayRoot
          (Yulang.CommonRoleOutermostResolver.Result.selected
            Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload) ∧
        ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
              assignment →
            Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
              Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
              Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
Yulang.GeneralDictionaryEarlyMergeVariableCoverage.ordinary_trace : Yulang.B4Target.Steps
  (Yulang.GeneralDictionarySupportOrdinaryExecution.Step Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    Yulang.GeneralNominalExamples.displayRoot)
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
Yulang.GeneralDictionaryEarlyMergeVariableCoverage.covered : Yulang.GeneralDictionaryVariableStableCoverage.Covered
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeVariableCoverage.every_model_from_coverage : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      assignment →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
Yulang.GeneralDictionaryEarlyMergeVariableCoverage.actual_stable_alias_coverage : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralDictionaryVariableStableCoverage.Covered Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
          Yulang.GeneralDictionaryEarlyMergeScalarExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
        (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity ≠
            (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity ∧
          Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
              (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
              (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity ∧
            Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
              Yulang.GeneralDictionaryEarlyMergeScalarClassification.current Yulang.GeneralNominalExamples.model
              Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
```
