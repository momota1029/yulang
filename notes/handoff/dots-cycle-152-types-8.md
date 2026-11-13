# Cycle152 exact theorem types (8)

```lean
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
Yulang.GeneralDictionaryObservedRequestTransport.observed_extension : ∀
  (before after : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralDictionaryOrdinaryTrace.Extension before after →
    ∀ (requests : List Yulang.GeneralNominalMaterialization.Request),
      Iff (Yulang.GeneralDictionaryObservedScalarRequests.Observed after.state after.interpretation requests)
        (Yulang.GeneralDictionaryObservedScalarRequests.Observed before.state before.interpretation requests)
@Yulang.GeneralDictionaryObservedRequestTransport.observed_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
      (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root) before after →
    ∀ (requests : List Yulang.GeneralNominalMaterialization.Request),
      Iff
        (Yulang.GeneralDictionaryObservedScalarRequests.Observed
          (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
          (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles after)).interpretation
          requests)
        (Yulang.GeneralDictionaryObservedScalarRequests.Observed
          (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles before)).state
          (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles before)).interpretation
          requests)
@Yulang.GeneralDictionaryObservedRequestTransport.generated_models_after_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
      (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root) before after →
    ∀ (requests : List Yulang.GeneralNominalMaterialization.Request),
      Yulang.GeneralDictionaryObservedScalarRequests.Observed
          (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles before)).state
          (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles before)).interpretation
          requests →
        ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
          (report :
            Yulang.GeneralNominalRecursiveInspection.Report
              (@Yulang.GeneralNominalSaturationState.State.context roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state)
          (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models
              (@Yulang.GeneralNominalSaturationState.State.context roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
              model →
            Yulang.GeneralNominalMaterialization.Models
              (@Yulang.GeneralNominalSaturationState.State.context roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
              declaration capture report
              (Yulang.GeneralNominalMaterialization.generated
                (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
                (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles after)).interpretation
                requests)
              model
@Yulang.GeneralDictionaryObservedRequestTransport.actual_requests_models_after_trace : ∀
  {roles : Yulang.Roles.RoleDecls} (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
      (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root) before after →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (captures : Yulang.GeneralNominalAllocation.Bindings),
      Yulang.GeneralDictionaryVariableRequirements.VariableClauses declaration →
        Yulang.GeneralDictionaryObservedScalarRequests.Observed
            (@Yulang.GeneralNominalSaturationState.State.context roles
                (@Yulang.GeneralNominalSupport.Tracked.current roles before)).state
            (@Yulang.GeneralNominalSaturationState.State.context roles
                (@Yulang.GeneralNominalSupport.Tracked.current roles before)).interpretation
            (@Yulang.GeneralNominalMaterialization.rootRequests roles declaration root) →
          ∀ (capture : Yulang.GeneralDeclarationDemands.Capture)
            (report :
              Yulang.GeneralNominalRecursiveInspection.Report
                (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state)
            (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models
                (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
                model →
              Yulang.GeneralNominalMaterialization.Models
                (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
                declaration capture report
                (Yulang.GeneralNominalMaterialization.generated
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                      (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                      (@Yulang.GeneralNominalSupport.Tracked.current roles after)).interpretation
                  (@Yulang.GeneralNominalMaterialization.requests roles
                    (@Yulang.GeneralNominalSaturationState.State.context roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles after)).state
                    registry root declaration checked captures))
                model
@Yulang.GeneralDictionaryObservedStableCoverage.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
              (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
            ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
              @Yulang.GeneralDictionaryObservedAliasJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  registry focus chosen checked →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryObservedAliasJoint.Covered roles registry state focus chosen checked →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        @Yulang.GeneralNominalSaturationState.Models roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                          @Yulang.GeneralNominalJointCandidates.Joint roles registry
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryObservedStableCoverage.stable_instances_generated : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
          @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
              (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
            ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
              @Yulang.GeneralDictionaryObservedAliasJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  registry focus chosen checked →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryObservedAliasJoint.Covered roles registry state focus chosen checked →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        @Yulang.GeneralNominalSaturationState.Models roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                          @Yulang.GeneralNominalSupportSteps.Stable roles registry state focus →
                            And
                              (∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
                                @Yulang.GeneralNominalSaturationState.Models roles
                                    (@Yulang.GeneralNominalSupport.Tracked.current roles state) assignment →
                                  @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
                                    (@Yulang.GeneralNominalSaturationState.State.context roles
                                      (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                                    assignment focus key children)
                              (∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                                @Membership.mem (Yulang.GeneralSourceDictionaries.Occurrence roles)
                                    (List (Yulang.GeneralSourceDictionaries.Occurrence roles))
                                    (@List.instMembership (Yulang.GeneralSourceDictionaries.Occurrence roles)) children
                                    child →
                                  @Yulang.GeneralNominalSaturationState.Generated roles
                                    (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus child)
@Yulang.GeneralDictionaryObservedStableCoverage.covered_of_variable : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryVariableStableCoverage.Covered roles registry state root →
    @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root
@Yulang.GeneralDictionaryObservedStableCoverage.stable_descendant : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
    @Yulang.GeneralNominalSaturationState.Generated roles (@Yulang.GeneralNominalSupport.Tracked.current roles state)
        root focus →
      @Yulang.GeneralNominalSupportSteps.Stable roles registry state focus
@Yulang.GeneralDictionaryObservedStableCoverage.selected_instance_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root →
            @Yulang.GeneralNominalSaturationState.Generated roles
                (@Yulang.GeneralNominalSupport.Tracked.current roles state) root focus →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                    (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                      (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                  ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                    @Yulang.GeneralNominalSaturationState.Models roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                      And
                        (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
                          (@Yulang.GeneralNominalSaturationState.State.context roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                          model focus key children)
                        (∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                          @Membership.mem (Yulang.GeneralSourceDictionaries.Occurrence roles)
                              (List (Yulang.GeneralSourceDictionaries.Occurrence roles))
                              (@List.instMembership (Yulang.GeneralSourceDictionaries.Occurrence roles)) children
                              child →
                            @Yulang.GeneralNominalSaturationState.Generated roles
                              (@Yulang.GeneralNominalSupport.Tracked.current roles state) root child)
@Yulang.GeneralDictionaryObservedStableCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryObservedStableCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryObservedStableCoverage.root_dictionary_all_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root →
            ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
              @Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                  (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
                    (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                    (Yulang.GeneralNominalSupportBoundary.boundary roles))
                  registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                  @Yulang.GeneralNominalSaturationState.Models roles
                      (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                      (@Yulang.GeneralNominalSaturationState.State.context roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                      model root dictionary
@Yulang.GeneralDictionaryObservedStableCoverage.covered_descendant : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root →
    @Yulang.GeneralNominalSaturationState.Generated roles (@Yulang.GeneralNominalSupport.Tracked.current roles state)
        root focus →
      @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state focus

```
