# Cycle152 exact theorem types (1)

```lean
@Yulang.GeneralDictionaryAliasInstallationObstruction.different_selected_not_installable : ∀
  {roles : Yulang.Roles.RoleDecls} (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSupport.Tracked roles) (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (firstKey lastKey : Nat) (firstChildren lastChildren : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand firstKey firstChildren) →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      @Yulang.GeneralNominalJointCandidates.Related roles (@Yulang.GeneralNominalSupport.Tracked.current roles state)
          focus site →
        @Yulang.GeneralNominalSupportBoundary.Local roles registry state
            (@Yulang.GeneralNominalDemandMerging.Site.occurrence roles site)
            (@Yulang.CommonRoleOutermostResolver.Frontier.selected
              (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand lastKey lastChildren) →
          @Ne Nat firstKey lastKey →
            ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
              @Eq (Yulang.GeneralSourceDictionaries.Occurrence roles)
                  (@Yulang.GeneralNominalDemandMerging.Site.occurrence roles
                    (@Yulang.GeneralNominalSaturationState.Packet.site roles packet))
                  focus →
                Not
                  (@Yulang.GeneralNominalFeedbackSteps.Installable roles registry
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state) packet)
@Yulang.GeneralDictionaryClosedAliasJoint.selected_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
      @Yulang.GeneralDictionaryClosedAliasJoint.Shape roles
          (@Yulang.GeneralNominalSaturationState.State.context roles
            (@Yulang.GeneralNominalSupport.Tracked.current roles state))
          registry focus chosen checked →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
              (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                And (@Eq Nat chosen.id key)
                  (@Yulang.GeneralNominalJointCandidates.BranchAt roles registry
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus chosen.id model)
@Yulang.GeneralDictionaryClosedAliasJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.GeneralNominalSupportSteps.SourceFormed roles registry root state →
    (∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        @Membership.mem (Yulang.GeneralNominalSaturationState.Packet roles)
            (List (Yulang.GeneralNominalSaturationState.Packet roles))
            (@List.instMembership (Yulang.GeneralNominalSaturationState.Packet roles))
            (@Yulang.GeneralNominalSaturationState.State.packets roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles state))
            packet →
          Yulang.GeneralDictionaryOrdinaryTrace.Extension
            (@Yulang.GeneralNominalSaturationState.Packet.context roles packet)
            (@Yulang.GeneralNominalSaturationState.State.context roles
              (@Yulang.GeneralNominalSupport.Tracked.current roles state))) →
      ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
        @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
            (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
          ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
            @Yulang.GeneralDictionaryClosedAliasJoint.Shape roles
                (@Yulang.GeneralNominalSaturationState.State.context roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                registry focus chosen checked →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                    (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                      (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                  @Yulang.GeneralDictionaryClosedAliasJoint.Covered roles registry state focus chosen checked →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      @Yulang.GeneralNominalSaturationState.Models roles
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                        @Yulang.GeneralNominalJointCandidates.Joint roles registry
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryClosedAliasJoint.ordinary_stable_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state focus →
          ∀ (chosen : Yulang.GeneralDeclarations.Declaration),
            @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
                (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
              ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen),
                @Yulang.GeneralDictionaryClosedAliasJoint.Shape roles
                    (@Yulang.GeneralNominalSaturationState.State.context roles
                      (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                    registry focus chosen checked →
                  ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                    @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                        (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                          (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                      @Yulang.GeneralDictionaryClosedAliasJoint.Covered roles registry state focus chosen checked →
                        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                          @Yulang.GeneralNominalSaturationState.Models roles
                              (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                            ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload),
                              @Yulang.CommonRoleOutermostResolver.All₂
                                  (Yulang.GeneralSourceDictionaries.Occurrence roles)
                                  Yulang.GeneralDictionaryReadback.Payload
                                  (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                                    (@Yulang.GeneralNominalSaturationState.State.context roles
                                      (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                                    model)
                                  children dictionaries →
                                @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                                  (@Yulang.GeneralNominalSaturationState.State.context roles
                                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                                  model focus (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryClosedStableCoverage.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
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
              @Yulang.GeneralDictionaryClosedAliasJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  registry focus chosen checked →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryClosedAliasJoint.Covered roles registry state focus chosen checked →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        @Yulang.GeneralNominalSaturationState.Models roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                          @Yulang.GeneralNominalJointCandidates.Joint roles registry
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryClosedStableCoverage.stable_instances_generated : ∀ {roles : Yulang.Roles.RoleDecls}
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
              @Yulang.GeneralDictionaryClosedAliasJoint.Shape roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  registry focus chosen checked →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryClosedAliasJoint.Covered roles registry state focus chosen checked →
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
@Yulang.GeneralDictionaryClosedStableCoverage.covered_of_observed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryObservedStableCoverage.Covered roles registry state root →
    @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state root
@Yulang.GeneralDictionaryClosedStableCoverage.stable_descendant : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
    @Yulang.GeneralNominalSaturationState.Generated roles (@Yulang.GeneralNominalSupport.Tracked.current roles state)
        root focus →
      @Yulang.GeneralNominalSupportSteps.Stable roles registry state focus
@Yulang.GeneralDictionaryClosedStableCoverage.selected_instance_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryClosedStableCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryClosedStableCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryClosedStableCoverage.root_dictionary_all_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  @Yulang.GeneralNominalSourceFormation.InitialSource roles registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      @Yulang.B4Target.Steps (Yulang.GeneralNominalSupport.Tracked roles)
          (@Yulang.GeneralDictionarySupportOrdinaryExecution.Step roles registry root)
          (@Yulang.GeneralNominalSupport.initial roles context root) state →
        @Yulang.GeneralNominalSupportSteps.Stable roles registry state root →
          @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state root →
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
@Yulang.GeneralDictionaryClosedStableCoverage.covered_descendant : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state root →
    @Yulang.GeneralNominalSaturationState.Generated roles (@Yulang.GeneralNominalSupport.Tracked.current roles state)
        root focus →
      @Yulang.GeneralDictionaryClosedStableCoverage.Covered roles registry state focus
@Yulang.GeneralDictionaryClosedTreeBranch.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : @Yulang.GeneralDictionaryClosedTreeBranch.Shape roles context registry root declaration checked)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models context.state model →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
        (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
          (@Yulang.GeneralDictionaryClosedTreeBranch.Shape.slot roles context registry root declaration checked shape)
          (@Yulang.GeneralDictionaryClosedTreeBranch.Shape.slot roles context registry root declaration checked shape))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state)))
      model
@Yulang.GeneralDictionaryClosedTreeBranch.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : @Yulang.GeneralDictionaryClosedTreeBranch.Shape roles context registry root declaration checked),
  @Yulang.GeneralNominalRecursiveCandidates.RequestReady roles registry context root declaration checked
    (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
      (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
        (@Yulang.GeneralDictionaryClosedTreeBranch.Shape.slot roles context registry root declaration checked shape)
        (@Yulang.GeneralDictionaryClosedTreeBranch.Shape.slot roles context registry root declaration checked shape))
      (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state)))
@Yulang.GeneralDictionaryClosedTreeBranch.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape : @Yulang.GeneralDictionaryClosedTreeBranch.Shape roles context registry root declaration checked),
      Yulang.GeneralNominalRecursiveCandidates.Metadata registry context →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models context.state model →
            @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry context model root declaration.id
              (@Yulang.GeneralNominalAllocation.children roles registry.constructors context.state registry root
                declaration checked
                (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration
                    (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
                      (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
                        (@Yulang.GeneralDictionaryClosedTreeBranch.Shape.slot roles context registry root declaration
                          checked shape)
                        (@Yulang.GeneralDictionaryClosedTreeBranch.Shape.slot roles context registry root declaration
                          checked shape))
                      (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state))))))
@Yulang.GeneralDictionaryClosedTreeBranch.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape :
        @Yulang.GeneralDictionaryClosedTreeBranch.Shape roles
          (@Yulang.GeneralNominalSaturationState.State.context roles state) registry root declaration checked)
      (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralNominalFeedbackK2.Local roles registry state root
          (@Yulang.CommonRoleOutermostResolver.Frontier.selected
            (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand key children) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models (@Yulang.GeneralNominalSaturationState.State.context roles state).state
              model →
            And (@Eq Nat declaration.id key)
              (@Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
                (@Yulang.GeneralNominalSaturationState.State.context roles state) model root key children)

```
