# Cycle152 exact theorem types (4)

```lean
Yulang.GeneralDictionaryObservedCompleteCoverage.covered : @Yulang.GeneralDictionaryObservedStableCoverage.Covered
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed Yulang.GeneralDictionaryObservedCompleteExample.root
Yulang.GeneralDictionaryObservedCompleteCoverage.every_model_from_coverage : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteClosure.current
      assignment Yulang.GeneralDictionaryObservedCompleteExample.root
      Yulang.GeneralDictionaryObservedCompleteEvidence.payload
Yulang.GeneralDictionaryObservedCompleteCoverage.actual_stable_named_coverage : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
    Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
  (And
    (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry
      Yulang.GeneralDictionaryObservedCompleteInstallation.installed
      Yulang.GeneralDictionaryObservedCompleteExample.root)
    (And
      (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
        Yulang.GeneralNominalExamples.model)
      (And
        (@Yulang.GeneralDictionaryObservedStableCoverage.Covered Yulang.GeneralDeclarationExamples.roles
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
            (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryObservedCompleteExample.registry
              Yulang.GeneralDictionaryObservedCompleteClosure.current Yulang.GeneralNominalExamples.model
              Yulang.GeneralDictionaryObservedCompleteExample.root
              Yulang.GeneralDictionaryObservedCompleteEvidence.payload))))))
Yulang.GeneralDictionaryObservedCompleteEvidence.children_exact : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryObservedCompleteExample.children
  (@List.cons (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedCompleteEvidence.child
    (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
Yulang.GeneralDictionaryObservedCompleteEvidence.child_arguments : @Eq
  (Option (List (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedCompleteExample.context.state)))
  (@Yulang.GeneralNominalRecursiveCandidates.arguments Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.context Yulang.GeneralDictionaryObservedCompleteEvidence.child)
  (@some
    (List
      (Prod (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
        (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)))
    (@List.cons
      (Prod (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
        (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots))
      (@Prod.mk (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
        (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
        (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots) (nat_lit 1)
          (@Fin.instOfNat Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots ⋯ (nat_lit 1)))
        (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots) (nat_lit 1)
          (@Fin.instOfNat Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots ⋯ (nat_lit 1))))
      (@List.nil
        (Prod (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
          (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)))))
Yulang.GeneralDictionaryObservedCompleteEvidence.child_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.context
      assignment Yulang.GeneralDictionaryObservedCompleteEvidence.child Yulang.GeneralNominalExamples.intDisplay.id
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedCompleteEvidence.child_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.context
      assignment Yulang.GeneralDictionaryObservedCompleteEvidence.child
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralNominalExamples.intDisplay.id
        (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
Yulang.GeneralDictionaryObservedCompleteEvidence.full_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.context
      assignment Yulang.GeneralDictionaryObservedCompleteExample.root
      Yulang.GeneralDictionaryObservedCompleteEvidence.payload
Yulang.GeneralDictionaryObservedCompleteEvidence.reachable_inhabited_full_evidence : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
    Yulang.GeneralDictionaryObservedCompleteExample.start)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteExample.start)
      Yulang.GeneralNominalExamples.model)
    (And
      (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.context
        Yulang.GeneralNominalExamples.model Yulang.GeneralDictionaryObservedCompleteExample.root
        Yulang.GeneralDictionaryObservedCompleteEvidence.payload)
      (And
        (@Ne (List Yulang.GeneralSourceState.Output)
          (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryObservedCompleteExample.root))
          (@List.nil Yulang.GeneralSourceState.Output))
        (@Eq Nat
          (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
            Yulang.GeneralDictionaryObservedCompleteExample.children)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
Yulang.GeneralDictionaryObservedCompleteExample.source_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralDictionaryObservedCompleteExample.source Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryObservedCompleteExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryObservedCompleteExample.declaration
Yulang.GeneralDictionaryObservedCompleteExample.requests_exact : @Eq (List Yulang.GeneralNominalMaterialization.Request)
  (@Yulang.GeneralNominalMaterialization.requests Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.source Yulang.GeneralDictionaryObservedCompleteExample.registry
    Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteExample.declaration
    Yulang.GeneralDictionaryObservedCompleteExample.checked
    (Yulang.GeneralNominalRecursiveInspection.bindings Yulang.GeneralDictionaryObservedCompleteExample.source
      (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryObservedCompleteExample.context
        Yulang.GeneralDictionaryObservedCompleteExample.declaration
        (@List.cons
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedCompleteExample.context.state)
          (@Prod.mk (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
            (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
            (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots) (nat_lit 0)
              (@Fin.instOfNat Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots ⋯ (nat_lit 0)))
            (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots) (nat_lit 0)
              (@Fin.instOfNat Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots ⋯ (nat_lit 0))))
          (@List.nil
            (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedCompleteExample.context.state))))))
  (@List.cons Yulang.GeneralNominalMaterialization.Request
    {
      pattern :=
        Yulang.GeneralDeclarationPatterns.Pattern.app (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@List.nil Yulang.GeneralDeclarationPatterns.Pattern),
      target := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
      mode := Yulang.GeneralNominalMaterialization.Mode.actual }
    (@List.nil Yulang.GeneralNominalMaterialization.Request))
Yulang.GeneralDictionaryObservedCompleteExample.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.context
Yulang.GeneralDictionaryObservedCompleteExample.named_request_present : @Ne (List Yulang.GeneralSourceState.Output)
  (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.root))
  (@List.nil Yulang.GeneralSourceState.Output)
Yulang.GeneralDictionaryObservedCompleteExample.nonterminal : @Ne (List Yulang.GeneralDeclarations.Clause)
  Yulang.GeneralDictionaryObservedCompleteExample.declaration.requirements (@List.nil Yulang.GeneralDeclarations.Clause)
Yulang.GeneralDictionaryObservedCompleteExample.every_source_model : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.context
      Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteExample.declaration
      Yulang.GeneralDictionaryObservedCompleteExample.checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedCompleteExample.context.state)
        (@Prod.mk (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
          (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots)
          (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat (Fin Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryObservedCompleteExample.context.state.base.slots ⋯ (nat_lit 0))))
        (@List.nil
          (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralDictionaryObservedCompleteExample.context.state)))
      assignment

```
