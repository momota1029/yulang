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
Yulang.GeneralDictionaryObservedFiniteRequests.schemas_valid : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (queries : List Yulang.GeneralNominalInspection.Query)
  (origins : Nat → Yulang.GeneralNominalRecursiveInspection.Origin) (mode : Yulang.GeneralNominalMaterialization.Mode)
  (start : Nat),
  (∀ (index : Nat) (query : Yulang.GeneralNominalInspection.Query),
      @Eq (Option Yulang.GeneralNominalInspection.Query)
          (@getElem? (List Yulang.GeneralNominalInspection.Query) Nat Yulang.GeneralNominalInspection.Query
            (fun as i => @LT.lt Nat instLTNat i (@List.length Yulang.GeneralNominalInspection.Query as))
            (@List.instGetElem?NatLtLength Yulang.GeneralNominalInspection.Query) queries index)
          (@some Yulang.GeneralNominalInspection.Query query) →
        Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
          (Yulang.GeneralNominalMaterialization.schema query
            (origins (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) start index)) mode)) →
    Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
      (Yulang.GeneralNominalMaterialization.schemas queries origins mode start)
Yulang.GeneralDictionaryObservedFiniteRequests.tree_schema : ∀ (state : Yulang.GeneralNominalState.State)
  {slot : Fin state.base.slots} {query : Yulang.GeneralNominalInspection.Query}
  (tree : Yulang.GeneralDictionaryObservedFiniteRequests.Tree state slot query)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin) (mode : Yulang.GeneralNominalMaterialization.Mode),
      Yulang.GeneralNominalSpineFacts.Matches state model slot origin →
        Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
          (Yulang.GeneralNominalMaterialization.schema query origin mode)
Yulang.GeneralDictionaryObservedFiniteRequests.schemas_shape : ∀ (queries : List Yulang.GeneralNominalInspection.Query)
  (origins : Nat → Yulang.GeneralNominalRecursiveInspection.Origin) (mode : Yulang.GeneralNominalMaterialization.Mode)
  (start : Nat),
  (∀ (index : Nat) (query : Yulang.GeneralNominalInspection.Query),
      @Eq (Option Yulang.GeneralNominalInspection.Query)
          (@getElem? (List Yulang.GeneralNominalInspection.Query) Nat Yulang.GeneralNominalInspection.Query
            (fun as i => @LT.lt Nat instLTNat i (@List.length Yulang.GeneralNominalInspection.Query as))
            (@List.instGetElem?NatLtLength Yulang.GeneralNominalInspection.Query) queries index)
          (@some Yulang.GeneralNominalInspection.Query query) →
        And
          (@Eq (List Yulang.GeneralNominalMaterialization.Use)
            (Yulang.GeneralNominalMaterialization.schema query
                (origins (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) start index)) mode).variables
            (@List.nil Yulang.GeneralNominalMaterialization.Use))
          (@Eq Bool
            (Yulang.GeneralNominalMaterialization.schema query
                (origins (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) start index)) mode).unknown
            false)) →
    And
      (@Eq (List Yulang.GeneralNominalMaterialization.Use)
        (Yulang.GeneralNominalMaterialization.schemas queries origins mode start).variables
        (@List.nil Yulang.GeneralNominalMaterialization.Use))
      (@Eq Bool (Yulang.GeneralNominalMaterialization.schemas queries origins mode start).unknown false)
Yulang.GeneralDictionaryObservedFiniteRequests.tree_shape : ∀ (state : Yulang.GeneralNominalState.State)
  {slot : Fin state.base.slots} {query : Yulang.GeneralNominalInspection.Query}
  (tree : Yulang.GeneralDictionaryObservedFiniteRequests.Tree state slot query)
  (origin : Yulang.GeneralNominalRecursiveInspection.Origin) (mode : Yulang.GeneralNominalMaterialization.Mode),
  And
    (@Eq (List Yulang.GeneralNominalMaterialization.Use)
      (Yulang.GeneralNominalMaterialization.schema query origin mode).variables
      (@List.nil Yulang.GeneralNominalMaterialization.Use))
    (@Eq Bool (Yulang.GeneralNominalMaterialization.schema query origin mode).unknown false)
Yulang.GeneralDictionaryObservedFiniteRequests.observed_of_closed : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedClosedRequests.Observed state interpretation requests →
    Yulang.GeneralDictionaryObservedFiniteRequests.Observed state interpretation requests
Yulang.GeneralDictionaryObservedFiniteRequests.generated_shape : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedFiniteRequests.Observed state interpretation requests →
    And
      (@Eq (List Yulang.GeneralNominalMaterialization.Use)
        (Yulang.GeneralNominalMaterialization.generated state interpretation requests).variables
        (@List.nil Yulang.GeneralNominalMaterialization.Use))
      (@Eq Bool (Yulang.GeneralNominalMaterialization.generated state interpretation requests).unknown false)
Yulang.GeneralDictionaryObservedFiniteRequests.generated_valid : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedFiniteRequests.Observed state interpretation requests →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
          (Yulang.GeneralNominalMaterialization.generated state interpretation requests)
Yulang.GeneralDictionaryObservedFiniteRequests.generated_models : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedFiniteRequests.Observed state interpretation requests →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
      (report : Yulang.GeneralNominalRecursiveInspection.Report state)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        Yulang.GeneralNominalMaterialization.Models state declaration capture report
          (Yulang.GeneralNominalMaterialization.generated state interpretation requests) model

```
