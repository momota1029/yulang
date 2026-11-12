# Cycle151 Joint theorem types, part 2/2

```text
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  (∀ (index : Fin (Yulang.GeneralDeclarationExamples.roles root.demand.role).arity),
      Eq.{1} (root.demand.arguments index) (Prod.mk.{0, 0} 0 0)) →
    Yulang.GeneralNominalSupport.DecisionGuard (Yulang.GeneralDictionaryEarlyMergeScalarExample.start root)
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry root List.nil.{0}
Yulang.GeneralDictionaryEarlyMergeScalarExample.query : Eq.{1}
  (Yulang.GeneralNominalInspection.queries (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralNominalExamples.interpretation Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration)
  (List.cons.{0}
    (Yulang.GeneralNominalInspection.Query.nominal 0
      (List.cons.{0} (Yulang.GeneralNominalInspection.Query.variables (List.cons.{0} 0 List.nil.{0})) List.nil.{0}))
    List.nil.{0})
Yulang.GeneralDictionaryEarlyMergeScalarExample.schema : Eq.{1}
  (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration Yulang.GeneralDictionaryEarlyMergeScalarExample.checked
    (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}))
  { }
Yulang.GeneralDictionaryEarlyMergeScalarExample.branch : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
      Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
      Yulang.GeneralDictionaryEarlyMergeScalarExample.checked (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}) m
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
  (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 1 Yulang.GeneralDictionaryEarlyMergeScalarExample.children)
Yulang.GeneralDictionaryEarlyMergeScalarExample.children_exact : Eq.{1}
  Yulang.GeneralDictionaryEarlyMergeScalarExample.children
  (List.cons.{0} (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10)
    (List.cons.{0} (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11) List.nil.{0}))
Yulang.GeneralDictionaryEarlyMergeScalarExample.enabled : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot).current
  Yulang.GeneralDictionaryEarlyMergeScalarExample.packet
Yulang.GeneralDictionaryEarlyMergeScalarExample.packet_guard : Yulang.GeneralNominalSupportSteps.PacketGuard
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.packet List.nil.{0}
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
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Membership.mem.{0, 0} Yulang.GeneralDictionaryEarlyMergeScalarExample.before.current.sites
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.site n)
Yulang.GeneralDictionaryEarlyMergeScalarExample.inputs_same : Yulang.GeneralNominalFeedbackSites.SameInputs
  Yulang.GeneralDictionaryEarlyMergeScalarExample.before.current
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.site 10) (Yulang.GeneralDictionaryEarlyMergeScalarExample.site 11)
Yulang.GeneralDictionaryEarlyMergeScalarExample.actual_early_merge : Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarExample.before
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
    Ne.{1} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets List.nil.{0} ∧
      Ne.{1} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.aliases List.nil.{0}
Yulang.GeneralDictionaryEarlyMergeScalarExample.finish_model : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryEarlyMergeScalarExample.actual_path : Yulang.B4Target.Steps.{1}
  (Yulang.GeneralNominalSupportSteps.Step Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    Yulang.GeneralNominalExamples.displayRoot)
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
Yulang.GeneralDictionaryEarlyMergeScalarExample.reachable : Yulang.B4TargetV5.Reachable.{0}
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
Yulang.GeneralDictionaryEarlyMergeScalarExample.inhabited_early_merge : Yulang.B4TargetV5.Reachable.{0}
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Ne.{1} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets List.nil.{0} ∧
      Ne.{1} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.aliases List.nil.{0} ∧
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
    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 3 List.nil.{0})
Yulang.GeneralDictionaryEarlyMergeScalarClassification.supported_child : ∀ (n : Nat),
  Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 3 List.nil.{0})
Yulang.GeneralDictionaryEarlyMergeScalarJoint.sites_exact : Eq.{1}
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.sites
  (List.cons.{0} Yulang.GeneralDictionaryEarlyMergeScalarJoint.rootSite
    (List.cons.{0} (Yulang.GeneralDictionaryEarlyMergeScalarExample.site 10)
      (List.cons.{0} (Yulang.GeneralDictionaryEarlyMergeScalarExample.site 11) List.nil.{0})))
@Yulang.GeneralDictionaryEarlyMergeScalarJoint.alias_class : ∀ {first last : Nat},
  Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current first last →
    (Yulang.GeneralDictionaryEarlyMergeScalarJoint.ChildIdentity first ↔
      Yulang.GeneralDictionaryEarlyMergeScalarJoint.ChildIdentity last)
Yulang.GeneralDictionaryEarlyMergeScalarJoint.root_outside : ¬Yulang.GeneralDictionaryEarlyMergeScalarJoint.ChildIdentity
    Yulang.GeneralNominalExamples.displayRoot.identity
Yulang.GeneralDictionaryEarlyMergeScalarJoint.related_children : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    ∀ (s : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
      Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) s →
        Eq.{1} s.occurrence (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10) ∨
          Eq.{1} s.occurrence (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11)
Yulang.GeneralDictionaryEarlyMergeScalarJoint.covered : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
      Yulang.GeneralNominalExamples.intDisplay
Yulang.GeneralDictionaryEarlyMergeScalarJoint.packets_grow : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  Membership.mem.{0, 0} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets p →
    Yulang.GeneralDictionaryOrdinaryTrace.Extension p.context
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.context
Yulang.GeneralDictionaryEarlyMergeScalarJoint.joint : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          assignment →
        Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
          Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) 3
Yulang.GeneralDictionaryEarlyMergeScalarJoint.distinct_children : Ne.{1}
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity
Yulang.GeneralDictionaryEarlyMergeScalarJoint.children_aliased : Yulang.GeneralNominalSaturationState.Alias
  Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity
Yulang.GeneralDictionaryEarlyMergeScalarJoint.unrecorded : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    ¬Exists.{1} fun p =>
        Membership.mem.{0, 0} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets p ∧
          Eq.{1} p.site.occurrence (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
Yulang.GeneralDictionaryEarlyMergeScalarJoint.actual_two_unrecorded_joints : Yulang.B4TargetV5.Reachable.{0}
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
      Yulang.GeneralNominalExamples.model ∧
    Ne.{1} (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
        (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity ∧
      Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10).identity
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11).identity ∧
        Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
            Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
            (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10) 3 ∧
          Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
              Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
              (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11) 3 ∧
            (¬Exists.{1} fun p =>
                  Membership.mem.{0, 0} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets p ∧
                    Eq.{1} p.site.occurrence (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 10)) ∧
              ¬Exists.{1} fun p =>
                  Membership.mem.{0, 0} Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current.packets p ∧
                    Eq.{1} p.site.occurrence (Yulang.GeneralDictionaryEarlyMergeScalarExample.child 11)
Yulang.GeneralDictionaryEarlyMergeScalarJoint.same_assignment : ∀ (n : Nat),
  Eq.{1} n 10 ∨ Eq.{1} n 11 →
    ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
          assignment →
        ∀ (s : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
          Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current
              (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n) s →
            Yulang.GeneralNominalJointCandidates.BranchAt Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
              Yulang.GeneralDictionaryEarlyMergeScalarExample.finish.current s.occurrence 3 assignment
```
