# Cycle152 exact theorem types (6)

```lean
Yulang.GeneralDictionaryObservedCompleteSelected.no_root : Not
  (@Yulang.GeneralNominalFeedbackK2.RootK2 Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.start)
    Yulang.GeneralDictionaryObservedCompleteExample.root)
Yulang.GeneralDictionaryObservedCompleteSelected.no_candidate : Not
  (@Yulang.GeneralNominalFeedbackK2.CandidateK2 Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.registry
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.start)
    Yulang.GeneralDictionaryObservedCompleteExample.root)
Yulang.GeneralDictionaryObservedCompleteSelected.unique : @Yulang.GeneralNominalLocalBoundary.Unique
  (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalFeedbackK2.fields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.start)
  Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
  Yulang.GeneralDictionaryObservedCompleteExample.children
Yulang.GeneralDictionaryObservedCompleteSelected.selected : @Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.start)
  Yulang.GeneralDictionaryObservedCompleteExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
    Yulang.GeneralDictionaryObservedCompleteExample.children)
Yulang.GeneralDictionaryObservedCompleteSelected.decisions : @Yulang.GeneralNominalSupport.DecisionGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.start
  Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedCompleteSelected.support_selected : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.start Yulang.GeneralDictionaryObservedCompleteExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
    Yulang.GeneralDictionaryObservedCompleteExample.children)
Yulang.GeneralDictionaryObservedCompleteStable.installs_committed : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  @Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      Yulang.GeneralDictionaryObservedCompleteExample.root
      (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSaturationState.Packet.site Yulang.GeneralDeclarationExamples.roles p)) →
    @Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteExample.registry
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
        p →
      @Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
        p
Yulang.GeneralDictionaryObservedCompleteStable.feedback_stable : @Yulang.GeneralNominalFeedbackSteps.Stable
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
  Yulang.GeneralDictionaryObservedCompleteExample.root
Yulang.GeneralDictionaryObservedCompleteStable.stable : @Yulang.GeneralNominalSupportSteps.Stable
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed Yulang.GeneralDictionaryObservedCompleteExample.root
Yulang.GeneralDictionaryObservedCompleteStable.stable_reachable_named_dictionary : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
    Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      Yulang.GeneralNominalExamples.model)
    (And
      (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteExample.registry
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed
        Yulang.GeneralDictionaryObservedCompleteExample.root)
      (And
        (@Ne (List Yulang.GeneralSourceState.Output)
          (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryObservedCompleteExample.root))
          (@List.nil Yulang.GeneralSourceState.Output))
        (And
          (@Eq Nat
            (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
              Yulang.GeneralDictionaryObservedCompleteExample.children)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
            @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
                (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
                  Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
                assignment →
              @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
                Yulang.GeneralDictionaryObservedCompleteExample.registry
                Yulang.GeneralDictionaryObservedCompleteClosure.current assignment
                Yulang.GeneralDictionaryObservedCompleteExample.root
                Yulang.GeneralDictionaryObservedCompleteEvidence.payload)))))
Yulang.GeneralDictionaryObservedInitialExample.source_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryObservedInitialExample.source Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryObservedInitialExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryObservedInitialExample.declaration
Yulang.GeneralDictionaryObservedInitialExample.requests_exact : @Eq (List Yulang.GeneralNominalMaterialization.Request)
  (@Yulang.GeneralNominalMaterialization.requests Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.source Yulang.GeneralDictionaryObservedInitialExample.registry
    Yulang.GeneralDictionaryObservedInitialExample.root Yulang.GeneralDictionaryObservedInitialExample.declaration
    Yulang.GeneralDictionaryObservedInitialExample.checked
    (Yulang.GeneralNominalRecursiveInspection.bindings Yulang.GeneralDictionaryObservedInitialExample.source
      (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryObservedInitialExample.context
        Yulang.GeneralDictionaryObservedInitialExample.declaration
        (@List.cons
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedInitialExample.context.state)
          (@Prod.mk (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots)
            (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots)
            (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots) (nat_lit 0)
              (@Fin.instOfNat Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots ⋯ (nat_lit 0)))
            (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots) (nat_lit 0)
              (@Fin.instOfNat Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots ⋯ (nat_lit 0))))
          (@List.nil
            (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedInitialExample.context.state))))))
  (@List.cons Yulang.GeneralNominalMaterialization.Request
    {
      pattern :=
        Yulang.GeneralDeclarationPatterns.Pattern.app (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@List.nil Yulang.GeneralDeclarationPatterns.Pattern),
      target := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
      mode := Yulang.GeneralNominalMaterialization.Mode.actual }
    (@List.nil Yulang.GeneralNominalMaterialization.Request))
Yulang.GeneralDictionaryObservedInitialExample.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.context
Yulang.GeneralDictionaryObservedInitialExample.named_request_present : @Ne (List Yulang.GeneralSourceState.Output)
  (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.root))
  (@List.nil Yulang.GeneralSourceState.Output)
Yulang.GeneralDictionaryObservedInitialExample.nonterminal : @Ne (List Yulang.GeneralDeclarations.Clause)
  Yulang.GeneralDictionaryObservedInitialExample.declaration.requirements (@List.nil Yulang.GeneralDeclarations.Clause)
Yulang.GeneralDictionaryObservedInitialExample.every_source_model : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedInitialExample.source assignment →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.context
      Yulang.GeneralDictionaryObservedInitialExample.root Yulang.GeneralDictionaryObservedInitialExample.declaration
      Yulang.GeneralDictionaryObservedInitialExample.checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedInitialExample.context.state)
        (@Prod.mk (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots)
          (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots)
          (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots ⋯ (nat_lit 0))))
        (@List.nil
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedInitialExample.context.state)))
      assignment
Yulang.GeneralDictionaryObservedInitialExample.actual_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.context Yulang.GeneralNominalExamples.model
  Yulang.GeneralDictionaryObservedInitialExample.root Yulang.GeneralDictionaryObservedInitialExample.declaration.id
  (@Yulang.GeneralNominalAllocation.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryObservedInitialExample.source
    Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.root
    Yulang.GeneralDictionaryObservedInitialExample.declaration Yulang.GeneralDictionaryObservedInitialExample.checked
    (Yulang.GeneralNominalRecursiveInspection.bindings Yulang.GeneralDictionaryObservedInitialExample.source
      (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryObservedInitialExample.context
        Yulang.GeneralDictionaryObservedInitialExample.declaration
        (@List.cons
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedInitialExample.context.state)
          (@Prod.mk (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots)
            (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots)
            (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots) (nat_lit 0)
              (@Fin.instOfNat Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots ⋯ (nat_lit 0)))
            (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots) (nat_lit 0)
              (@Fin.instOfNat Yulang.GeneralDictionaryObservedInitialExample.context.state.base.slots ⋯ (nat_lit 0))))
          (@List.nil
            (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedInitialExample.context.state))))))

```
