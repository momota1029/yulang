# Cycle151 Joint theorem types, part 1/2

```text
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  Membership.mem.{0, 0} registry.declarations chosen →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
        ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus chosen.id
                  List.nil.{0}
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_selected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  Membership.mem.{0, 0} registry.declarations chosen →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
        ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Eq.{1} chosen.id key ∧ Eq.{1} List.nil.{0} children
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        Membership.mem.{0, 0} state.current.packets packet →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
        Membership.mem.{0, 0} registry.declarations chosen →
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
            Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
              ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                  Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered registry state focus chosen →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          Membership.mem.{0, 0} registry.declarations chosen →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
                ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                    Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_locality : ∀
  (site : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayChild site →
    Eq.{1} site.occurrence Yulang.GeneralNominalExamples.displayChild
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.covered : Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
  Yulang.GeneralNominalExamples.displayChild Yulang.GeneralNominalExamples.intDisplay
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      assignment →
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayChild 3
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.actual_unrecorded_stable_joint : Yulang.B4TargetV5.Reachable.{0}
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayChild ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
          Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayChild 3 ∧
        ¬Exists.{1} fun packet =>
            Membership.mem.{0, 0} Yulang.GeneralDictionarySupportRecursiveExample.finish.current.packets packet ∧
              Eq.{1} packet.site.occurrence Yulang.GeneralNominalExamples.displayChild
@Yulang.GeneralDictionaryUnrecordedVariableJoint.selected_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  Membership.mem.{0, 0} registry.declarations chosen →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
        ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Eq.{1} chosen.id key ∧
                  Yulang.GeneralNominalJointCandidates.BranchAt registry state.current focus chosen.id model
@Yulang.GeneralDictionaryUnrecordedVariableJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        Membership.mem.{0, 0} state.current.packets packet →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
        Membership.mem.{0, 0} registry.declarations chosen →
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
            Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
              ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                  Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          Membership.mem.{0, 0} registry.declarations chosen →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
                ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                    Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_nonterminal_packet : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          Membership.mem.{0, 0} registry.declarations chosen →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
                ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                    Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalSupportSteps.Stable registry state focus →
                            Ne.{1} children List.nil.{0} →
                              Exists.{1} fun packet =>
                                Membership.mem.{0, 0} state.current.packets packet ∧ Eq.{1} packet.site.occurrence focus
@Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_instances_generated : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          Membership.mem.{0, 0} registry.declarations chosen →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
                ∀ (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children) →
                    Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalSupportSteps.Stable registry state focus →
                            (∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
                                Yulang.GeneralNominalSaturationState.Models state.current assignment →
                                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context
                                    assignment focus key children) ∧
                              ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                                Membership.mem.{0, 0} children child →
                                  Yulang.GeneralNominalSaturationState.Generated state.current focus child
Yulang.GeneralDictionaryEarlyMergeScalarExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
Yulang.GeneralDictionaryEarlyMergeScalarExample.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
Yulang.GeneralDictionaryEarlyMergeScalarExample.all_source_decisions : ∀
```
