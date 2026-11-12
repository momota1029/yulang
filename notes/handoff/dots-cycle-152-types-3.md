# Cycle152 exact theorem types (3)

```lean
Yulang.GeneralDictionaryObservedCompleteClassification.classified : @Yulang.B4TargetV3.Classify
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed Yulang.GeneralDictionaryObservedCompleteExample.root
  (Yulang.CommonRoleOutermostResolver.Result.selected Yulang.GeneralDictionaryObservedCompleteEvidence.payload)
Yulang.GeneralDictionaryObservedCompleteClassification.stable_classified_named_dictionary : And
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
        (@Yulang.B4TargetV3.Classify
          (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
          (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
            (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
            (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles))
          Yulang.GeneralDictionaryObservedCompleteExample.registry
          Yulang.GeneralDictionaryObservedCompleteInstallation.installed
          Yulang.GeneralDictionaryObservedCompleteExample.root
          (Yulang.CommonRoleOutermostResolver.Result.selected Yulang.GeneralDictionaryObservedCompleteEvidence.payload))
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
                  Yulang.GeneralDictionaryObservedCompleteEvidence.payload))))))
Yulang.GeneralDictionaryObservedCompleteClosure.final_parent_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteClosure.current
      assignment Yulang.GeneralDictionaryObservedCompleteExample.root
      Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
      Yulang.GeneralDictionaryObservedCompleteExample.children
Yulang.GeneralDictionaryObservedCompleteClosure.final_child_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteClosure.current
      assignment Yulang.GeneralDictionaryObservedCompleteEvidence.child Yulang.GeneralNominalExamples.intDisplay.id
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryObservedCompleteClosure.edges_exact : @Eq
  (List
    (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
  (@Yulang.GeneralNominalSaturationState.State.edges Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
  (@List.cons
    (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
    (@Prod.mk (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralDictionaryObservedCompleteExample.root Yulang.GeneralDictionaryObservedCompleteEvidence.child)
    (@List.nil
      (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))))
Yulang.GeneralDictionaryObservedCompleteClosure.sites_exact : @Eq
  (List (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralNominalSaturationState.State.sites Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
  (@List.cons (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles)
    (@Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedCompleteExample.root)
    (@List.cons (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles)
      (@Yulang.GeneralNominalFeedbackSites.childSite Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.packet
        Yulang.GeneralDictionaryObservedCompleteEvidence.child)
      (@List.nil (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles))))
Yulang.GeneralDictionaryObservedCompleteClosure.generated_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  @Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      Yulang.GeneralDictionaryObservedCompleteExample.root focus →
    Or
      (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) focus
        Yulang.GeneralDictionaryObservedCompleteExample.root)
      (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) focus
        Yulang.GeneralDictionaryObservedCompleteEvidence.child)
Yulang.GeneralDictionaryObservedCompleteClosure.merges_closed : ∀
  (first last : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  @Membership.mem (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles)
      (List (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles))
      (@List.instMembership (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles))
      (@Yulang.GeneralNominalSaturationState.State.sites Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
      first →
    @Membership.mem (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles)
        (List (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles))
        (@List.instMembership (Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles))
        (@Yulang.GeneralNominalSaturationState.State.sites Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryObservedCompleteInstallation.installed))
        last →
      @Yulang.GeneralNominalFeedbackSites.SameInputs Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
          first last →
        @Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
          (@Yulang.GeneralSourceDictionaries.Occurrence.identity Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles first))
          (@Yulang.GeneralSourceDictionaries.Occurrence.identity Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles last))
Yulang.GeneralDictionaryObservedCompleteClosure.varying_model : ∀ (name : Nat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) name →
    @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      (Yulang.GeneralDictionaryObservedCompleteClosure.varying name)
Yulang.GeneralDictionaryObservedCompleteClosure.refresh_large_unknown : ∀
  (next : Yulang.GeneralNominalCandidates.Context)
  (certificate :
    @Yulang.GeneralNominalCycleSteps.Refresh Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      next)
  (id : Nat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) id →
    Not (Yulang.GeneralNominalState.Known next.state id)
Yulang.GeneralDictionaryObservedCompleteClosure.context_complete : @Yulang.GeneralNominalSaturationState.ContextComplete
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
Yulang.GeneralDictionaryObservedCompleteClosure.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  Yulang.GeneralDictionaryObservedCompleteClosure.current.state
Yulang.GeneralDictionaryObservedCompleteCoverage.ordinary_trace : @Yulang.B4Target.Steps
  (Yulang.GeneralNominalSupport.Tracked Yulang.GeneralDeclarationExamples.roles)
  (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteExample.registry Yulang.GeneralDictionaryObservedCompleteExample.root)
  Yulang.GeneralDictionaryObservedCompleteExample.start Yulang.GeneralDictionaryObservedCompleteInstallation.installed
@Yulang.GeneralDictionaryObservedCompleteCoverage.alias_equal : ∀ {first last : Nat},
  @Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      first last →
    @Eq Nat first last
Yulang.GeneralDictionaryObservedCompleteCoverage.related_child : ∀
  (site : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  @Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      Yulang.GeneralDictionaryObservedCompleteEvidence.child site →
    @Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles site)
      Yulang.GeneralDictionaryObservedCompleteEvidence.child

```
