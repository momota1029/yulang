# Cycle152 exact theorem types (5)

```lean
Yulang.GeneralDictionaryObservedCompleteExample.actual_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.context Yulang.GeneralNominalExamples.model
  Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
  (@Yulang.GeneralNominalAllocation.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryObservedCompleteExample.source
    Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
    Yulang.GeneralDictionaryObservedCompleteExample.declaration Yulang.GeneralDictionaryObservedCompleteExample.checked
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
Yulang.GeneralDictionaryObservedCompleteExample.initial_source : @Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.context Yulang.GeneralDictionaryObservedCompleteExample.root
Yulang.GeneralDictionaryObservedCompleteExample.initial_models : @Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.start)
  Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryObservedCompleteExample.actual_reachable : @Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
  Yulang.GeneralDictionaryObservedCompleteExample.start
Yulang.GeneralDictionaryObservedCompleteExample.root_ready : Not
  (@Yulang.GeneralNominalState.RootPending Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.source
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.root))
Yulang.GeneralDictionaryObservedCompleteExample.prepared : @Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.context Yulang.GeneralDictionaryObservedCompleteExample.root
  Yulang.GeneralDictionaryObservedCompleteExample.declaration Yulang.GeneralDictionaryObservedCompleteExample.checked
Yulang.GeneralDictionaryObservedCompleteExample.survivor : @Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.context Yulang.GeneralDictionaryObservedCompleteExample.root
  Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
  Yulang.GeneralDictionaryObservedCompleteExample.children
Yulang.GeneralDictionaryObservedCompleteExample.initial_joint : @Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.start)
  Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
Yulang.GeneralDictionaryObservedCompleteExample.actual_children_count : @Eq Nat
  (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedCompleteExample.children)
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
Yulang.GeneralDictionaryObservedCompleteFinalEvidence.models_of_source : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment →
    @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment
Yulang.GeneralDictionaryObservedCompleteFinalEvidence.source_of_models : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment →
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment
Yulang.GeneralDictionaryObservedCompleteFinalEvidence.installed_models_iff : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Iff
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment)
    (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryObservedCompleteExample.source assignment)
Yulang.GeneralDictionaryObservedCompleteFinalEvidence.final_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry
      (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
      assignment Yulang.GeneralDictionaryObservedCompleteExample.root
      Yulang.GeneralDictionaryObservedCompleteEvidence.payload
Yulang.GeneralDictionaryObservedCompleteFinalEvidence.nonempty_journal : @Ne
  (List (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralNominalSaturationState.State.packets Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
  (@List.nil (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedCompleteFinalEvidence.reachable_full_named_dictionary : And
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
      (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteExample.registry
        (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
        Yulang.GeneralNominalExamples.model Yulang.GeneralDictionaryObservedCompleteExample.root
        Yulang.GeneralDictionaryObservedCompleteEvidence.payload)
      (And
        (@Ne (List (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
          (@Yulang.GeneralNominalSaturationState.State.packets Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
          (@List.nil (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)))
        (And
          (@Ne (List Yulang.GeneralSourceState.Output)
            (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
              (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
                Yulang.GeneralDictionaryObservedCompleteExample.root))
            (@List.nil Yulang.GeneralSourceState.Output))
          (@Eq Nat
            (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
              Yulang.GeneralDictionaryObservedCompleteExample.children)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
Yulang.GeneralDictionaryObservedCompleteInstallation.packet_children : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralNominalSaturationState.Packet.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteInstallation.packet)
  Yulang.GeneralDictionaryObservedCompleteExample.children
Yulang.GeneralDictionaryObservedCompleteInstallation.enabled : @Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.start)
  Yulang.GeneralDictionaryObservedCompleteInstallation.packet
Yulang.GeneralDictionaryObservedCompleteInstallation.children_nonempty : @Ne
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryObservedCompleteExample.children
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedCompleteInstallation.novel : Not
  (@Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.start)
    Yulang.GeneralDictionaryObservedCompleteInstallation.packet)
Yulang.GeneralDictionaryObservedCompleteInstallation.guard : @Yulang.GeneralNominalSupportSteps.PacketGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.start
  Yulang.GeneralDictionaryObservedCompleteInstallation.packet
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedCompleteInstallation.install_at : @Yulang.GeneralNominalSupportSteps.At
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.start Yulang.GeneralDictionaryObservedCompleteExample.root
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed
Yulang.GeneralDictionaryObservedCompleteInstallation.install_step : @Yulang.GeneralNominalSupportSteps.Step
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteExample.start
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed
Yulang.GeneralDictionaryObservedCompleteInstallation.not_stable : Not
  (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.start
    Yulang.GeneralDictionaryObservedCompleteExample.root)
Yulang.GeneralDictionaryObservedCompleteInstallation.installed_reachable : @Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed

```
