# Cycle151 final Joint theorem types, part2/3

```text
                                  Yulang.GeneralNominalSaturationState.Generated state.current focus child
Yulang.GeneralDictionaryEarlyMergeScalarExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
Yulang.GeneralDictionaryEarlyMergeScalarExample.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
Yulang.GeneralDictionaryEarlyMergeScalarExample.all_source_decisions : ∀
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  (∀ (index : Fin (Yulang.GeneralDeclarationExamples.roles root.demand.role).arity),
      root.demand.arguments index = (0, 0)) →
    Yulang.GeneralNominalSupport.DecisionGuard (Yulang.GeneralDictionaryEarlyMergeScalarExample.start root)
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry root []
Yulang.GeneralDictionaryEarlyMergeScalarExample.query : Yulang.GeneralNominalInspection.queries
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.interpretation
    Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration =
  [Yulang.GeneralNominalInspection.Query.nominal 0 [Yulang.GeneralNominalInspection.Query.variables [0]]]
Yulang.GeneralDictionaryEarlyMergeScalarExample.schema : Yulang.GeneralNominalRecursiveCandidates.generated
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
    Yulang.GeneralDictionaryEarlyMergeScalarExample.checked [(0, 0)] =
  { }
Yulang.GeneralDictionaryEarlyMergeScalarExample.branch : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
      Yulang.GeneralDictionaryEarlyMergeScalarExample.checked [(0, 0)] m
Yulang.GeneralDictionaryEarlyMergeScalarExample.prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
  Yulang.GeneralDictionaryEarlyMergeScalarExample.checked
Yulang.GeneralDictionaryEarlyMergeScalarExample.survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children
Yulang.GeneralDictionaryEarlyMergeScalarExample.selected : Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children)
Yulang.GeneralDictionaryEarlyMergeScalarExample.children_exact : Yulang.GeneralDictionaryEarlyMergeScalarExample.children =
  [Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10, Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11]
Yulang.GeneralDictionaryEarlyMergeScalarExample.enabled : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot).current
  Yulang.GeneralDictionaryEarlyMergeScalarExample.packet
Yulang.GeneralDictionaryEarlyMergeScalarExample.packet_guard : Yulang.GeneralNominalSupportSteps.PacketGuard
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.packet []
Yulang.GeneralDictionaryEarlyMergeScalarExample.novel : ¬Yulang.GeneralNominalFeedbackSteps.Committed
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot).current
    Yulang.GeneralDictionaryEarlyMergeScalarExample.packet
Yulang.GeneralDictionaryEarlyMergeScalarExample.source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryEarlyMergeScalarExample.before_scheduled : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryEarlyMergeScalarExample.before
Yulang.GeneralDictionaryEarlyMergeScalarExample.before_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryEarlyMergeScalarExample.before.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryEarlyMergeScalarExample.site_present : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    Yulang.GeneralDictionaryEarlyMergeScalarExample.site n ∈
      Yulang.GeneralDictionaryEarlyMergeScalarExample.before.current.sites
Yulang.GeneralDictionaryEarlyMergeScalarExample.inputs_same : Yulang.GeneralNominalFeedbackSites.SameInputs
  Yulang.GeneralDictionaryEarlyMergeScalarExample.before.current
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.site 10) (Yulang.GeneralDictionaryEarlyMergeScalarExample.site 11)
Yulang.GeneralDictionaryEarlyMergeScalarExample.actual_early_merge : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarExample.before
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.aliases ≠ []
Yulang.GeneralDictionaryEarlyMergeScalarExample.finish_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryEarlyMergeScalarExample.actual_path : Yulang.B4Target.Steps
  (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    Yulang.GeneralNominalExamples.displayRoot)
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
Yulang.GeneralDictionaryEarlyMergeScalarExample.reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
Yulang.GeneralDictionaryEarlyMergeScalarExample.inhabited_early_merge : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets ≠ [] ∧
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.aliases ≠ [] ∧
        Yulang.GeneralDictionarySupportChoices.Coherent Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
Yulang.GeneralDictionaryEarlyMergeScalarClassification.parent_instance : Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  Yulang.GeneralDictionaryEarlyMergeScalarClassification.current Yulang.GeneralNominalExamples.model
  Yulang.GeneralNominalExamples.displayRoot 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children
Yulang.GeneralDictionaryEarlyMergeScalarClassification.acyclic : ∀ (source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current source
Yulang.GeneralDictionaryEarlyMergeScalarClassification.child_selected : ∀ (n : Nat),
  Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
    (Yulang.CommonRoleOutermostResolver.Frontier.selected 3 [])
Yulang.GeneralDictionaryEarlyMergeScalarClassification.supported_child : ∀ (n : Nat),
  Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
    (Yulang.CommonRoleOutermostResolver.Frontier.selected 3 [])
Yulang.GeneralDictionaryEarlyMergeScalarJoint.sites_exact : Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.sites =
  [Yulang.GeneralDictionaryEarlyMergeScalarJoint.rootSite, Yulang.GeneralDictionaryEarlyMergeScalarExample.site 10,
    Yulang.GeneralDictionaryEarlyMergeScalarExample.site 11]
@Yulang.GeneralDictionaryEarlyMergeScalarJoint.alias_class : ∀ {first last : Nat},
  Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current first last →
    (Yulang.GeneralDictionaryEarlyMergeScalarJoint.ChildIdentity first ↔
      Yulang.GeneralDictionaryEarlyMergeScalarJoint.ChildIdentity last)
Yulang.GeneralDictionaryEarlyMergeScalarJoint.root_outside : ¬Yulang.GeneralDictionaryEarlyMergeScalarJoint.ChildIdentity
    Yulang.GeneralNominalExamples.displayRoot.identity
Yulang.GeneralDictionaryEarlyMergeScalarJoint.related_children : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    ∀ (s : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
      Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) s →
        s.occurrence = Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10 ∨
          s.occurrence = Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11
Yulang.GeneralDictionaryEarlyMergeScalarJoint.covered : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
      Yulang.GeneralNominalExamples.intDisplay
Yulang.GeneralDictionaryEarlyMergeScalarJoint.packets_grow : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  p ∈ Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets →
    Yulang.GeneralDictionaryOrdinaryTrace.Extension p.context
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.context
Yulang.GeneralDictionaryEarlyMergeScalarJoint.joint : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          assignment →
        Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
          Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) 3
Yulang.GeneralDictionaryEarlyMergeScalarJoint.same_assignment : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          assignment →
        ∀ (s : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
          Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
              (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) s →
            Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
              Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current s.occurrence 3 assignment
Yulang.GeneralDictionaryEarlyMergeScalarJoint.distinct_children : (Yulang.GeneralDictionaryEarlyMergeScalarExample.child
      10).identity ≠
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity
Yulang.GeneralDictionaryEarlyMergeScalarJoint.children_aliased : Yulang.GeneralNominalSaturationState.Alias
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity
Yulang.GeneralDictionaryEarlyMergeScalarJoint.unrecorded : ∀ (n : Nat),
  n = 10 ∨ n = 11 →
    ¬∃ p,
        p ∈ Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets ∧
          p.site.occurrence = Yulang.GeneralDictionaryEarlyMergeScalarExample.child n
Yulang.GeneralDictionaryEarlyMergeScalarJoint.actual_two_unrecorded_joints : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity ≠
        (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity ∧
      Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity ∧
        Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
            Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
            (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10) 3 ∧
```
