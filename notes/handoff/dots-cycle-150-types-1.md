# Cycle150 exact theorem types, part1/3

Lean4.35.0 `#check @name`, exit0.

```text
@Yulang.GeneralDictionaryAliasMixedLocality.leaf_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      Yulang.GeneralDictionaryAliasMixedLocality.Leaf state.current.context focus declaration →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralNominalJointCandidates.BranchAt registry state.current focus declaration.id model
@Yulang.GeneralDictionaryAliasMixedLocality.covered_of_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDictionaryAliasRecordedLocality.Covered registry state focus →
    Yulang.GeneralDictionaryAliasMixedLocality.Covered registry state focus chosen
@Yulang.GeneralDictionaryAliasMixedLocality.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        packet ∈ state.current.packets →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      Yulang.GeneralDictionarySupportChoices.Coherent state.current →
        ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
          packet ∈ state.current.packets →
            packet.site.occurrence = focus →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralDictionaryAliasMixedLocality.Covered registry state focus packet.declaration →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryAliasMixedLocality.early_ordinary_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root state →
          ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            packet ∈ state.current.packets →
              packet.site.occurrence = focus →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryAliasMixedLocality.Covered registry state focus packet.declaration →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryAliasRecordedLocality.covered_of_locality : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  packet ∈ state.current.packets →
    packet.site.occurrence = focus →
      ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalSupportBoundary.Local registry state focus
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
          (∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
              Yulang.GeneralNominalJointCandidates.Related state.current focus site → site.occurrence = focus) →
            Yulang.GeneralDictionaryAliasRecordedLocality.Covered registry state focus
@Yulang.GeneralDictionaryAliasRecordedLocality.related_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        packet ∈ state.current.packets →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      Yulang.GeneralDictionarySupportChoices.Coherent state.current →
        ∀ (chosen : Yulang.GeneralNominalSaturationState.Packet roles),
          chosen ∈ state.current.packets →
            chosen.site.occurrence = focus →
              ∀ (key : Nat),
                chosen.declaration.id = key →
                  Yulang.GeneralDictionaryAliasRecordedLocality.Covered registry state focus →
                    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
                      Yulang.GeneralNominalJointCandidates.Related state.current focus site →
                        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                          Yulang.GeneralNominalSaturationState.Models state.current model →
                            Yulang.GeneralNominalJointCandidates.BranchAt registry state.current site.occurrence key
                              model
@Yulang.GeneralDictionaryAliasRecordedLocality.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        packet ∈ state.current.packets →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      Yulang.GeneralDictionarySupportChoices.Coherent state.current →
        ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
          packet ∈ state.current.packets →
            packet.site.occurrence = focus →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralDictionaryAliasRecordedLocality.Covered registry state focus →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryAliasRecordedLocality.early_ordinary_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root state →
          ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            packet ∈ state.current.packets →
              packet.site.occurrence = focus →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryAliasRecordedLocality.Covered registry state focus →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryAliasTreeLocality.leaf_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      Yulang.GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus declaration →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralNominalJointCandidates.BranchAt registry state.current focus declaration.id model
@Yulang.GeneralDictionaryAliasTreeLocality.covered_of_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDictionaryAliasRecordedLocality.Covered registry state focus →
    Yulang.GeneralDictionaryAliasTreeLocality.Covered registry state focus chosen
@Yulang.GeneralDictionaryAliasTreeLocality.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        packet ∈ state.current.packets →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) →
      Yulang.GeneralDictionarySupportChoices.Coherent state.current →
        ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
          packet ∈ state.current.packets →
            packet.site.occurrence = focus →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                Yulang.GeneralNominalSupportBoundary.Local registry state focus
                    (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                  Yulang.GeneralDictionaryAliasTreeLocality.Covered registry state focus packet.declaration →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryAliasTreeLocality.early_ordinary_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryEarlyMergeChoices.Scheduled registry root state →
          ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            packet ∈ state.current.packets →
              packet.site.occurrence = focus →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    Yulang.GeneralDictionaryAliasTreeLocality.Covered registry state focus packet.declaration →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models state.current model →
                          Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
@Yulang.GeneralDictionaryAliasTreeLocality.covered_of_mixed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDictionaryAliasMixedLocality.Covered registry state focus chosen →
    Yulang.GeneralDictionaryAliasTreeLocality.Covered registry state focus chosen
@Yulang.GeneralDictionaryBranchCoverage.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryBranchCoverage.Covered registry state root →
      Yulang.GeneralNominalSaturationState.Generated state.current root focus →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          Yulang.GeneralNominalSupportBoundary.Local registry state focus
              (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state.current model →
                Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus key
                    children ∧
                  ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                    child ∈ children → Yulang.GeneralNominalSaturationState.Generated state.current root child
@Yulang.GeneralDictionaryBranchCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryBranchCoverage.Covered registry state root →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
            (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
            Yulang.GeneralNominalSaturationState.Generated state.current root focus →
              Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry
                  state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus dictionary
@Yulang.GeneralDictionaryBranchCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralNominalSupportSteps.SourceFormed registry root state →
    Yulang.GeneralDictionaryBranchCoverage.Covered registry state root →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state.current model →
          ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
            (demands : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
            (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                focus ∈ demands → Yulang.GeneralNominalSaturationState.Generated state.current root focus) →
              Yulang.CommonRoleOutermostResolver.All₂
                  (fun focus dictionary =>
                    Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
                      registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                  demands dictionaries →
                Yulang.CommonRoleOutermostResolver.All₂
                  (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) demands
                  dictionaries
@Yulang.GeneralDictionaryBranchCoverage.of_spine : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionarySpineCoverage.Covered registry state root →
    Yulang.GeneralDictionaryBranchCoverage.Covered registry state root
Yulang.GeneralDictionaryBranchCoverage.recursive_fixture : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current model →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current.context model
      Yulang.GeneralNominalExamples.displayRoot
      (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
@Yulang.GeneralDictionaryBranchCoverage.of_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    Yulang.GeneralDictionaryBranchCoverage.TraceCovered registry state root →
      Yulang.GeneralDictionaryBranchCoverage.Covered registry state root
@Yulang.GeneralDictionaryBranchCoverage.initial_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryBranchCoverage.TraceCovered registry state root →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state.current model →
              ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
                    registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                    dictionary
@Yulang.GeneralDictionaryBranchLeaf.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : Yulang.GeneralDictionaryBranchLeaf.BranchLeafShape context root declaration)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models context.state model →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked
      [(shape.slot, shape.slot)] model
@Yulang.GeneralDictionaryBranchLeaf.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : Yulang.GeneralDictionaryBranchLeaf.BranchLeafShape context root declaration),
  Yulang.GeneralNominalRecursiveCandidates.RequestReady registry context root declaration checked
    [(shape.slot, shape.slot)]
@Yulang.GeneralDictionaryBranchLeaf.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀ (shape : Yulang.GeneralDictionaryBranchLeaf.BranchLeafShape context root declaration),
        Yulang.GeneralNominalRecursiveCandidates.Metadata registry context →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralDictionaryRecursiveEvidence.Instance registry context model root declaration.id []
@Yulang.GeneralDictionaryBranchLeaf.selected_leaf : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀ (shape : Yulang.GeneralDictionaryBranchLeaf.BranchLeafShape state.context root declaration) (key : Nat)
        (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalFeedbackK2.Local registry state root
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models state.context.state model →
              declaration.id = key ∧
                children = [] ∧
                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.context model root key [] ∧
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root
                      (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
@Yulang.GeneralDictionaryBranchLeaf.selected_of_coverage : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionaryBranchLeaf.HasBranchLeaf registry state.context root →
    ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalFeedbackK2.Local registry state root
          (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models state.context.state model →
            children = [] ∧
              Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.context model root key [] ∧
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root
                  (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.coverage_from_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root →
      Yulang.GeneralDictionarySpineCoverage.Covered registry state root
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state.current model →
              ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
                    registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                    dictionary
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.forget_growth : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralDictionarySpineCoverage.Covered registry state root →
    Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.covered_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    (Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root ↔
      Yulang.GeneralDictionarySpineCoverage.Covered registry state root)
Yulang.GeneralDictionaryBranchOrdinaryCoverage.recursive_fixture : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current model →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current.context model
      Yulang.GeneralNominalExamples.displayRoot
      (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
@Yulang.GeneralDictionaryFiniteJournalJointExample.alias_eq : ∀ {first last : Nat},
  Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionarySupportRecursiveExample.finish.current first last →
    first = last
Yulang.GeneralDictionaryFiniteJournalJointExample.root_locality : ∀
  (site : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot site →
    site.occurrence = Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryFiniteJournalJointExample.root_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      assignment →
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1
Yulang.GeneralDictionaryFiniteJournalJointExample.actual_stable_joint : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
        Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1
@Yulang.GeneralDictionaryNamedLocality.at_ordinary : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryNamedLocality.At names registry before focus after →
    Yulang.GeneralDictionarySupportOrdinaryExecution.At registry before focus after
```
