# Cycle151 exact quantified theorem types

```text
          @Yulang.GeneralDictionaryVariableStableCoverage.Covered roles registry state root →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
                  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                  @Yulang.GeneralNominalSaturationState.Generated roles
                      (@Yulang.GeneralNominalSupport.Tracked.current roles state) root focus →
                    @Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                        (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
                          (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                          (Yulang.GeneralNominalSupportBoundary.boundary roles))
                        registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                      @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                        (@Yulang.GeneralNominalSaturationState.State.context roles
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                        model focus dictionary
@Yulang.GeneralDictionaryVariableStableCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryVariableStableCoverage.Covered roles registry state root →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
                  (demands : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                      @Membership.mem (Yulang.GeneralSourceDictionaries.Occurrence roles)
                          (List (Yulang.GeneralSourceDictionaries.Occurrence roles))
                          (@List.instMembership (Yulang.GeneralSourceDictionaries.Occurrence roles)) demands focus →
                        @Yulang.GeneralNominalSaturationState.Generated roles
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) root focus) →
                    @Yulang.CommonRoleOutermostResolver.All₂
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand
                        Yulang.CommonRoleOutermostResolver.Dictionary
                        (fun focus dictionary =>
                          @Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                            (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
                              (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                              (Yulang.GeneralNominalSupportBoundary.boundary roles))
                            registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                        demands dictionaries →
                      @Yulang.CommonRoleOutermostResolver.All₂ (Yulang.GeneralSourceDictionaries.Occurrence roles)
                        Yulang.GeneralDictionaryReadback.Payload
                        (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                          (@Yulang.GeneralNominalSaturationState.State.context roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                          model)
                        demands dictionaries
Yulang.GeneralDictionaryVariableStableExample.covered : @Yulang.GeneralDictionaryVariableStableCoverage.Covered
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalExamples.registry
  Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryVariableStableExample.every_model : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionarySupportRecursiveExample.finish)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalExamples.registry
      (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionarySupportRecursiveExample.finish))
      assignment Yulang.GeneralNominalExamples.displayRoot
      (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
          (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
          (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary)))
Yulang.GeneralDictionaryVariableStableExample.reachable_stable_unrecorded_success : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish)
  (And
    (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
      Yulang.GeneralNominalExamples.displayRoot)
    (And
      (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionarySupportRecursiveExample.finish)
        Yulang.GeneralNominalExamples.model)
      (And
        (Not
          (@Exists (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles) fun packet =>
            And
              (@Membership.mem (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)
                (List (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
                (@List.instMembership
                  (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
                (@Yulang.GeneralNominalSaturationState.State.packets Yulang.GeneralDeclarationExamples.roles
                  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
                    Yulang.GeneralDictionarySupportRecursiveExample.finish))
                packet)
              (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
                (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles
                  (@Yulang.GeneralNominalSaturationState.Packet.site Yulang.GeneralDeclarationExamples.roles packet))
                Yulang.GeneralNominalExamples.displayChild)))
        (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralNominalExamples.registry
          (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionarySupportRecursiveExample.finish))
          Yulang.GeneralNominalExamples.model Yulang.GeneralNominalExamples.displayRoot
          (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
              (Yulang.CommonRoleOutermostResolver.Dictionary.node
                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
              (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary)))))))
@Yulang.GeneralDictionaryVariableTree.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : @Yulang.GeneralDictionaryVariableTree.TreeBranchShape roles context root declaration)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models context.state model →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
        (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
          (@Yulang.GeneralDictionaryVariableTree.TreeBranchShape.slot roles context root declaration shape)
          (@Yulang.GeneralDictionaryVariableTree.TreeBranchShape.slot roles context root declaration shape))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state)))
      model
@Yulang.GeneralDictionaryVariableTree.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : @Yulang.GeneralDictionaryVariableTree.TreeBranchShape roles context root declaration),
  @Yulang.GeneralNominalRecursiveCandidates.RequestReady roles registry context root declaration checked
    (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
      (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
        (@Yulang.GeneralDictionaryVariableTree.TreeBranchShape.slot roles context root declaration shape)
        (@Yulang.GeneralDictionaryVariableTree.TreeBranchShape.slot roles context root declaration shape))
      (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state)))
@Yulang.GeneralDictionaryVariableTree.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape : @Yulang.GeneralDictionaryVariableTree.TreeBranchShape roles context root declaration),
      Yulang.GeneralNominalRecursiveCandidates.Metadata registry context →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models context.state model →
            @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root declaration.id
              (@Yulang.GeneralNominalAllocation.children roles registry.constructors context.state registry root
                declaration checked
                (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration
                    (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
                      (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
                        (@Yulang.GeneralDictionaryVariableTree.TreeBranchShape.slot roles context root declaration
                          shape)
                        (@Yulang.GeneralDictionaryVariableTree.TreeBranchShape.slot roles context root declaration
                          shape))
                      (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state))))))
@Yulang.GeneralDictionaryVariableTree.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀
        (shape :
          @Yulang.GeneralDictionaryVariableTree.TreeBranchShape roles
            (@Yulang.GeneralNominalSaturationState.State.context roles state) root declaration)
        (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        @Yulang.GeneralNominalFeedbackK2.Local roles registry state root
            (@Yulang.CommonRoleOutermostResolver.Frontier.selected
              (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand key children) →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models (@Yulang.GeneralNominalSaturationState.State.context roles state).state
                model →
              And (@Eq Nat declaration.id key)
                (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
                  (@Yulang.GeneralNominalSaturationState.State.context roles state) model root key children)
@Yulang.GeneralDictionaryVariableTree.selected_of_coverage : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryVariableTree.HasVariableTree roles registry
      (@Yulang.GeneralNominalSaturationState.State.context roles state) root →
    ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralNominalFeedbackK2.Local roles registry state root
          (@Yulang.CommonRoleOutermostResolver.Frontier.selected
            (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand key children) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models (@Yulang.GeneralNominalSaturationState.State.context roles state).state
              model →
            @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
              (@Yulang.GeneralNominalSaturationState.State.context roles state) model root key children
@Yulang.GeneralDictionaryVariableTree.selected_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryVariableTree.HasVariableTree roles registry
      (@Yulang.GeneralNominalSaturationState.State.context roles state) root →
    ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralNominalFeedbackK2.Local roles registry state root
          (@Yulang.CommonRoleOutermostResolver.Frontier.selected
            (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand key children) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models (@Yulang.GeneralNominalSaturationState.State.context roles state).state
              model →
            ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
              @Yulang.CommonRoleOutermostResolver.All₂ (Yulang.GeneralSourceDictionaries.Occurrence roles)
                  Yulang.GeneralDictionaryReadback.Payload
                  (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                    (@Yulang.GeneralNominalSaturationState.State.context roles state) model)
                  children dictionaries →
                @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                  (@Yulang.GeneralNominalSaturationState.State.context roles state) model root
                  (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryVariableTreeChildSelected.child_input : ∀
  (index :
    Fin
      (Yulang.GeneralDeclarationExamples.roles

```
