# Cycle151 exact quantified theorem types

```text
            (@Yulang.GeneralNominalSaturationState.Packet.context roles packet)
            (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles state))) →
      ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
        @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
            (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
            @Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape roles
                (@Yulang.GeneralNominalSaturationState.State.context roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                focus chosen →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                    (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                      (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                  @Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered roles registry state focus chosen →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      @Yulang.GeneralNominalSaturationState.Models roles
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                        @Yulang.GeneralNominalJointCandidates.Joint roles registry
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
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
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              @Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered roles registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        @Yulang.GeneralNominalSaturationState.Models roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                          @Yulang.GeneralNominalJointCandidates.Joint roles registry
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_nonterminal_packet : ∀ {roles : Yulang.Roles.RoleDecls}
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
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              @Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered roles registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        @Yulang.GeneralNominalSaturationState.Models roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                          @Yulang.GeneralNominalSupportSteps.Stable roles registry state focus →
                            @Ne (List (Yulang.GeneralSourceDictionaries.Occurrence roles)) children
                                (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence roles)) →
                              @Exists (Yulang.GeneralNominalSaturationState.Packet roles) fun packet =>
                                And
                                  (@Membership.mem (Yulang.GeneralNominalSaturationState.Packet roles)
                                    (List (Yulang.GeneralNominalSaturationState.Packet roles))
                                    (@List.instMembership (Yulang.GeneralNominalSaturationState.Packet roles))
                                    (@Yulang.GeneralNominalSaturationState.State.packets roles
                                      (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                                    packet)
                                  (@Eq (Yulang.GeneralSourceDictionaries.Occurrence roles)
                                    (@Yulang.GeneralNominalDemandMerging.Site.occurrence roles
                                      (@Yulang.GeneralNominalSaturationState.Packet.site roles packet))
                                    focus)
@Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_instances_generated : ∀ {roles : Yulang.Roles.RoleDecls}
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
            Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
              @Yulang.GeneralDictionaryUnrecordedVariableJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryUnrecordedVariableJoint.Covered roles registry state focus chosen →
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
@Yulang.GeneralDictionaryVariableRequirements.emission_empty : ∀ {roles : Yulang.Roles.RoleDecls} (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (clause : Yulang.GeneralDeclarations.Clause)
  (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (allocate : Yulang.GeneralDeclarationDemands.Allocation roles clause),
  @Eq (List Yulang.GeneralDeclarations.Equation) clause.outputs (@List.nil Yulang.GeneralDeclarations.Equation) →
    (∀ (pattern : Yulang.GeneralDeclarationPatterns.Pattern),
        @Membership.mem Yulang.GeneralDeclarationPatterns.Pattern (List Yulang.GeneralDeclarationPatterns.Pattern)
            (@List.instMembership Yulang.GeneralDeclarationPatterns.Pattern) clause.arguments pattern →
          @Exists Nat fun name =>
            @Eq Yulang.GeneralDeclarationPatterns.Pattern (Yulang.GeneralDeclarationPatterns.normalize pattern)
              (Yulang.GeneralDeclarationPatterns.Pattern.var name)) →
      @Eq (List Yulang.GeneralNominalMaterialization.Request)
        (@Yulang.GeneralNominalMaterialization.emissionRequests roles
          (@Yulang.GeneralDeclarationDemands.emit roles invocation declaration clause valid capture allocate))
        (@List.nil Yulang.GeneralNominalMaterialization.Request)
@Yulang.GeneralDictionaryVariableRequirements.requests_empty : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (captures : Yulang.GeneralNominalAllocation.Bindings),
  @Eq (List Yulang.GeneralSourceState.Output)
      (@Yulang.GeneralSourceState.Demand.outputs roles (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles root))
      (@List.nil Yulang.GeneralSourceState.Output) →
    Yulang.GeneralDictionaryVariableRequirements.VariableClauses declaration →
      @Eq (List Yulang.GeneralNominalMaterialization.Request)
        (@Yulang.GeneralNominalMaterialization.requests roles state registry root declaration checked captures)
        (@List.nil Yulang.GeneralNominalMaterialization.Request)
@Yulang.GeneralDictionaryVariableRequirements.generated_empty : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
  @Eq (List Yulang.GeneralSourceState.Output)
      (@Yulang.GeneralSourceState.Demand.outputs roles (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles root))
      (@List.nil Yulang.GeneralSourceState.Output) →
    Yulang.GeneralDictionaryVariableRequirements.VariableClauses declaration →
      @Eq Yulang.GeneralNominalMaterialization.Schema
        (@Yulang.GeneralNominalRecursiveCandidates.generated roles registry context root declaration checked bounds) { }
@Yulang.GeneralDictionaryVariableStableCoverage.stable_descendant : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
    @Yulang.GeneralNominalSaturationState.Generated roles (@Yulang.GeneralNominalSupport.Tracked.current roles state)
        root focus →
      @Yulang.GeneralNominalSupportSteps.Stable roles registry state focus
@Yulang.GeneralDictionaryVariableStableCoverage.selected_instance_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryVariableStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryVariableStableCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →

```
