# Cycle152 exact theorem types (7)

```lean
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
Yulang.GeneralDictionaryObservedInitialExample.initial_source : @Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.context Yulang.GeneralDictionaryObservedInitialExample.root
Yulang.GeneralDictionaryObservedInitialExample.initial_models : @Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.start)
  Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryObservedInitialExample.actual_reachable : @Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.root
  Yulang.GeneralDictionaryObservedInitialExample.start
Yulang.GeneralDictionaryObservedInitialExample.root_ready : Not
  (@Yulang.GeneralNominalState.RootPending Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.source
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.root))
Yulang.GeneralDictionaryObservedInitialExample.prepared : @Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.context Yulang.GeneralDictionaryObservedInitialExample.root
  Yulang.GeneralDictionaryObservedInitialExample.declaration Yulang.GeneralDictionaryObservedInitialExample.checked
Yulang.GeneralDictionaryObservedInitialExample.survivor : @Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.context Yulang.GeneralDictionaryObservedInitialExample.root
  Yulang.GeneralDictionaryObservedInitialExample.declaration.id Yulang.GeneralDictionaryObservedInitialExample.children
Yulang.GeneralDictionaryObservedInitialExample.initial_joint : @Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.start)
  Yulang.GeneralDictionaryObservedInitialExample.root Yulang.GeneralDictionaryObservedInitialExample.declaration.id
Yulang.GeneralDictionaryObservedInitialExample.actual_children_count : @Eq Nat
  (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedInitialExample.children)
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
Yulang.GeneralDictionaryObservedInitialInstallation.packet_children : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralNominalSaturationState.Packet.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialInstallation.packet)
  Yulang.GeneralDictionaryObservedInitialExample.children
Yulang.GeneralDictionaryObservedInitialInstallation.enabled : @Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.start)
  Yulang.GeneralDictionaryObservedInitialInstallation.packet
Yulang.GeneralDictionaryObservedInitialInstallation.children_nonempty : @Ne
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryObservedInitialExample.children
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedInitialInstallation.novel : Not
  (@Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.start)
    Yulang.GeneralDictionaryObservedInitialInstallation.packet)
Yulang.GeneralDictionaryObservedInitialInstallation.guard : @Yulang.GeneralNominalSupportSteps.PacketGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.start
  Yulang.GeneralDictionaryObservedInitialInstallation.packet
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedInitialInstallation.install_at : @Yulang.GeneralNominalSupportSteps.At
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.start Yulang.GeneralDictionaryObservedInitialExample.root
  Yulang.GeneralDictionaryObservedInitialInstallation.installed
Yulang.GeneralDictionaryObservedInitialInstallation.install_step : @Yulang.GeneralNominalSupportSteps.Step
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.root Yulang.GeneralDictionaryObservedInitialExample.start
  Yulang.GeneralDictionaryObservedInitialInstallation.installed
Yulang.GeneralDictionaryObservedInitialInstallation.not_stable : Not
  (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.start
    Yulang.GeneralDictionaryObservedInitialExample.root)
Yulang.GeneralDictionaryObservedInitialInstallation.installed_reachable : @Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.root
  Yulang.GeneralDictionaryObservedInitialInstallation.installed
Yulang.GeneralDictionaryObservedInitialReadback.children_exact : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryObservedInitialExample.children
  (@List.cons (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedInitialReadback.child
    (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))

```
