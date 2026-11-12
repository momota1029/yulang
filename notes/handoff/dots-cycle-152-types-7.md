# Cycle152 exact theorem types (7)

```lean
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
Yulang.GeneralDictionaryObservedInitialReadback.child_role : @Eq Nat
  (@Yulang.GeneralSourceState.Demand.role Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialReadback.child))
  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
Yulang.GeneralDictionaryObservedInitialReadback.no_child_instance : ∀
  (snapshot : Yulang.GeneralNominalCandidates.Context) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (key : Nat)
  (descendants : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  Not
    (@Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.registry snapshot assignment
      Yulang.GeneralDictionaryObservedInitialReadback.child key descendants)
Yulang.GeneralDictionaryObservedInitialReadback.no_child_evidence : ∀
  (snapshot : Yulang.GeneralNominalCandidates.Context) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  Not
    (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.registry snapshot assignment
      Yulang.GeneralDictionaryObservedInitialReadback.child payload)
Yulang.GeneralDictionaryObservedInitialReadback.installed_models : @Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialInstallation.installed)
  Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryObservedInitialReadback.reachable_inhabited_missing_child : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.root
    Yulang.GeneralDictionaryObservedInitialInstallation.installed)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedInitialInstallation.installed)
      Yulang.GeneralNominalExamples.model)
    (∀ (payload : Yulang.GeneralDictionaryReadback.Payload),
      Not
        (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryObservedInitialExample.registry
          (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryObservedInitialInstallation.installed))
          Yulang.GeneralNominalExamples.model Yulang.GeneralDictionaryObservedInitialReadback.child payload)))
Yulang.GeneralDictionaryObservedInitialSelected.no_root : Not
  (@Yulang.GeneralNominalFeedbackK2.RootK2 Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.start)
    Yulang.GeneralDictionaryObservedInitialExample.root)
Yulang.GeneralDictionaryObservedInitialSelected.no_candidate : Not
  (@Yulang.GeneralNominalFeedbackK2.CandidateK2 Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.registry
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedInitialExample.start)
    Yulang.GeneralDictionaryObservedInitialExample.root)
Yulang.GeneralDictionaryObservedInitialSelected.unique : @Yulang.GeneralNominalLocalBoundary.Unique
  (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalFeedbackK2.fields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryObservedInitialExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.start)
  Yulang.GeneralDictionaryObservedInitialExample.root Yulang.GeneralDictionaryObservedInitialExample.declaration.id
  Yulang.GeneralDictionaryObservedInitialExample.children
Yulang.GeneralDictionaryObservedInitialSelected.selected : @Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedInitialExample.start)
  Yulang.GeneralDictionaryObservedInitialExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryObservedInitialExample.declaration.id
    Yulang.GeneralDictionaryObservedInitialExample.children)
Yulang.GeneralDictionaryObservedInitialSelected.decisions : @Yulang.GeneralNominalSupport.DecisionGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.start
  Yulang.GeneralDictionaryObservedInitialExample.registry Yulang.GeneralDictionaryObservedInitialExample.root
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedInitialSelected.support_selected : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedInitialExample.registry
  Yulang.GeneralDictionaryObservedInitialExample.start Yulang.GeneralDictionaryObservedInitialExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryObservedInitialExample.declaration.id
    Yulang.GeneralDictionaryObservedInitialExample.children)
Yulang.GeneralDictionaryObservedRequestTransport.observed_append : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (first last : List Yulang.GeneralNominalMaterialization.Request),
  Iff
    (Yulang.GeneralDictionaryObservedScalarRequests.Observed state interpretation
      (@HAppend.hAppend (List Yulang.GeneralNominalMaterialization.Request)
        (List Yulang.GeneralNominalMaterialization.Request) (List Yulang.GeneralNominalMaterialization.Request)
        (@instHAppendOfAppend (List Yulang.GeneralNominalMaterialization.Request)
          (@List.instAppend Yulang.GeneralNominalMaterialization.Request))
        first last))
    (And (Yulang.GeneralDictionaryObservedScalarRequests.Observed state interpretation first)
      (Yulang.GeneralDictionaryObservedScalarRequests.Observed state interpretation last))

```
