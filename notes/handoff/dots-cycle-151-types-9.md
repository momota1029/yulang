# Cycle151 exact quantified theorem types

```text
          (@Yulang.GeneralSourceState.Demand.role Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryVariableTreeEvidence.child))).arity),
  @Eq Yulang.GeneralSourceState.Interval
    (@Yulang.GeneralSourceState.Demand.arguments Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeEvidence.child)
      index)
    (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
Yulang.GeneralDictionaryVariableTreeChildSelected.child_ready : Not
  (@Yulang.GeneralNominalState.RootPending Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralNominalBranchExample.state
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeEvidence.child))
Yulang.GeneralDictionaryVariableTreeChildSelected.child_linked : @Yulang.GeneralNominalState.Linked
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalBranchExample.state
  (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeEvidence.child)
Yulang.GeneralDictionaryVariableTreeChildSelected.prepared_child : @Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralDictionaryVariableTreeEvidence.child
  Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration Yulang.GeneralDictionaryVariableTreeEvidence.leaf_checked
Yulang.GeneralDictionaryVariableTreeChildSelected.child_survivor : @Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralDictionaryVariableTreeEvidence.child
  Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeChildSelected.parent_conflict : @Ne
  (List (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state))
  (@Yulang.GeneralNominalRecursiveInspection.Report.conflicts Yulang.GeneralNominalBranchExample.context.state
    (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralNominalBranchExample.context
      Yulang.GeneralDictionaryVariableTreeExample.declaration
      (@List.cons (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state)
        (@Prod.mk (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
          (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
          (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 1)
            (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 1)))
          (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 1)
            (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 1))))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state)))))
  (@List.nil (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state))
Yulang.GeneralDictionaryVariableTreeChildSelected.parent_failed : ∀
  (check :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDictionaryVariableTreeExample.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.declaration),
  @Yulang.GeneralNominalRecursiveCandidates.Failed Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
    Yulang.GeneralDictionaryVariableTreeEvidence.child Yulang.GeneralDictionaryVariableTreeExample.declaration check
Yulang.GeneralDictionaryVariableTreeChildSelected.parent_not_prepared : ∀
  (check :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDictionaryVariableTreeExample.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.declaration),
  Not
    (@Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
      Yulang.GeneralDictionaryVariableTreeEvidence.child Yulang.GeneralDictionaryVariableTreeExample.declaration check)
Yulang.GeneralDictionaryVariableTreeChildSelected.unique_child : @Yulang.GeneralNominalLocalBoundary.Unique
  (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalFeedbackK2.fields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryVariableTreeExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralDictionaryVariableTreeEvidence.child Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
  (@List.nil (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
Yulang.GeneralDictionaryVariableTreeChildSelected.child_selected : @Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralDictionaryVariableTreeEvidence.child
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
    (@List.nil (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
Yulang.GeneralDictionaryVariableTreeChildSelected.child_decisions : @Yulang.GeneralNominalSupport.DecisionGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.start
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralDictionaryVariableTreeEvidence.child
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeChildSelected.child_support_selected : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralDictionaryVariableTreeExample.start Yulang.GeneralDictionaryVariableTreeEvidence.child
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
    (@List.nil (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
Yulang.GeneralDictionaryVariableTreeChildSelected.classified : @Yulang.B4TargetV3.Classify
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralDictionaryVariableTreeExample.start
  Yulang.GeneralNominalBranchExample.root
  (Yulang.CommonRoleOutermostResolver.Result.selected
    (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.declaration.id
      (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
        (Yulang.CommonRoleOutermostResolver.Dictionary.node
          Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
          (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
        (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))))
Yulang.GeneralDictionaryVariableTreeChildSelected.reachable_classified_unstable : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
    Yulang.GeneralDictionaryVariableTreeExample.start)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.start)
      Yulang.GeneralNominalBranchExample.model)
    (And
      (@Yulang.B4TargetV3.Classify
        (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
        (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
          (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
          (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles))
        Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralDictionaryVariableTreeExample.start
        Yulang.GeneralNominalBranchExample.root
        (Yulang.CommonRoleOutermostResolver.Result.selected
          (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.declaration.id
            (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
              (Yulang.CommonRoleOutermostResolver.Dictionary.node
                Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
                (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
              (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary)))))
      (Not
        (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralDictionaryVariableTreeExample.start
          Yulang.GeneralNominalBranchExample.root))))
@Yulang.GeneralDictionaryVariableTreeCoverage.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.GeneralNominalSupportSteps.SourceFormed roles registry root state →
    ∀ (domain : Yulang.GeneralSourceDictionaries.Occurrence roles → Prop),
      @Yulang.GeneralDictionaryVariableTreeCoverage.CoveredOn roles registry state domain →
        domain focus →
          ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
            @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                  (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                @Yulang.GeneralNominalSaturationState.Models roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                  @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
                    (@Yulang.GeneralNominalSaturationState.State.context roles
                      (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                    model focus key children
@Yulang.GeneralDictionaryVariableTreeCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.GeneralNominalSupportSteps.SourceFormed roles registry root state →
    ∀ (domain : Yulang.GeneralSourceDictionaries.Occurrence roles → Prop),
      @Yulang.GeneralDictionaryVariableTreeCoverage.CoveredOn roles registry state domain →
        @Yulang.GeneralDictionaryVariableTreeCoverage.ClosedOn roles registry state domain →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            @Yulang.GeneralNominalSaturationState.Models roles
                (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
              ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload)
                (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                domain focus →
                  @Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                      (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                        (Yulang.GeneralNominalSupportBoundary.boundary roles))
                      registry state focus (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                      (@Yulang.GeneralNominalSaturationState.State.context roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                      model focus dictionary
@Yulang.GeneralDictionaryVariableTreeCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.GeneralNominalSupportSteps.SourceFormed roles registry root state →
    ∀ (domain : Yulang.GeneralSourceDictionaries.Occurrence roles → Prop),
      @Yulang.GeneralDictionaryVariableTreeCoverage.CoveredOn roles registry state domain →
        @Yulang.GeneralDictionaryVariableTreeCoverage.ClosedOn roles registry state domain →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            @Yulang.GeneralNominalSaturationState.Models roles
                (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
              ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
                (demands : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                    @Membership.mem (Yulang.GeneralSourceDictionaries.Occurrence roles)
                        (List (Yulang.GeneralSourceDictionaries.Occurrence roles))
                        (@List.instMembership (Yulang.GeneralSourceDictionaries.Occurrence roles)) demands focus →
                      domain focus) →
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
@Yulang.GeneralDictionaryVariableTreeCoverage.reachable_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
      (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    ∀ (domain : Yulang.GeneralSourceDictionaries.Occurrence roles → Prop),
      domain root →
        @Yulang.GeneralDictionaryVariableTreeCoverage.CoveredOn roles registry state domain →
          @Yulang.GeneralDictionaryVariableTreeCoverage.ClosedOn roles registry state domain →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                  @Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                      (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                        (Yulang.GeneralNominalSupportBoundary.boundary roles))
                      registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry

```
