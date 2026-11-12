# Cycle151 final Joint theorem types, part1/3

```text
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  chosen ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus chosen.id
                  []
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_selected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  chosen ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model → chosen.id = key ∧ [] = children
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        packet ∈ state.current.packets →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
        chosen ∈ registry.declarations →
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
            Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered registry state focus chosen →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          chosen ∈ registry.declarations →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_locality : ∀
  (site : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayChild site →
    site.occurrence = Yulang.GeneralNominalExamples.displayChild
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.covered : Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
  Yulang.GeneralNominalExamples.displayChild Yulang.GeneralNominalExamples.intDisplay
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      assignment →
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayChild 3
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.actual_unrecorded_stable_joint : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayChild ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
          Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayChild 3 ∧
        ¬∃ packet,
            packet ∈ Yulang.GeneralDictionarySupportRecursiveExample.finish.current.packets ∧
              packet.site.occurrence = Yulang.GeneralNominalExamples.displayChild
@Yulang.GeneralDictionaryUnrecordedVariableJoint.selected_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  chosen ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                chosen.id = key ∧
                  Yulang.GeneralNominalJointCandidates.BranchAt registry state.current focus chosen.id model
@Yulang.GeneralDictionaryUnrecordedVariableJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        packet ∈ state.current.packets →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
        chosen ∈ registry.declarations →
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
            Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          chosen ∈ registry.declarations →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_nonterminal_packet : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          chosen ∈ registry.declarations →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalSupportSteps.Stable registry state focus →
                            children ≠ [] → ∃ packet, packet ∈ state.current.packets ∧ packet.site.occurrence = focus
@Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_instances_generated : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          chosen ∈ registry.declarations →
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalSupportSteps.Stable registry state focus →
                            (∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
                                Yulang.GeneralNominalSaturationState.Models state.current assignment →
                                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context
                                    assignment focus key children) ∧
                              ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                                child ∈ children →
```
