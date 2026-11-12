# Cycle151 checkpoint theorem types

```text
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_locality : ∀
  (site : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  @Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionarySupportRecursiveExample.finish)
      Yulang.GeneralNominalExamples.displayChild site →
    @Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles site)
      Yulang.GeneralNominalExamples.displayChild
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.covered : @Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalExamples.registry
  Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayChild
  Yulang.GeneralNominalExamples.intDisplay
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionarySupportRecursiveExample.finish)
      assignment →
    @Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalExamples.registry
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionarySupportRecursiveExample.finish)
      Yulang.GeneralNominalExamples.displayChild (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
Yulang.GeneralDictionaryUnrecordedAliasLeafExample.actual_unrecorded_stable_joint : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish)
  (And
    (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionarySupportRecursiveExample.finish
      Yulang.GeneralNominalExamples.displayChild)
    (And
      (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionarySupportRecursiveExample.finish)
        Yulang.GeneralNominalExamples.model)
      (And
        (@Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralNominalExamples.registry
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionarySupportRecursiveExample.finish)
          Yulang.GeneralNominalExamples.displayChild (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Not
          (@Exists (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles) fun packet =>
            And
              (@Membership.mem (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)
                (List (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
                (@List.instMembership
                  (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
                (@Yulang.GeneralNominalSaturationState.State.packets Yulang.GeneralDeclarationExamples.roles
                  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
                    Yulang.GeneralDictionarySupportRecursiveExample.finish))
                packet)
              (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
                (@Yulang.GeneralNominalDemandMerging.Site.occurrence Yulang.GeneralDeclarationExamples.roles
                  (@Yulang.GeneralNominalSaturationState.Packet.site Yulang.GeneralDeclarationExamples.roles packet))
                Yulang.GeneralNominalExamples.displayChild))))))
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      @Yulang.GeneralDictionaryAliasTreeLocality.Leaf roles
          (@Yulang.GeneralNominalSaturationState.State.context roles
            (@Yulang.GeneralNominalSupport.Tracked.current roles state))
          focus chosen →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
              (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                @Yulang.GeneralDictionaryRecursiveEvidence.Instance roles registry
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  model focus chosen.id (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence roles))
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_selected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations chosen →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
      @Yulang.GeneralDictionaryAliasTreeLocality.Leaf roles
          (@Yulang.GeneralNominalSaturationState.State.context roles
            (@Yulang.GeneralNominalSupport.Tracked.current roles state))
          focus chosen →
        ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
              (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                And (@Eq Nat chosen.id key)
                  (@Eq (List (Yulang.GeneralSourceDictionaries.Occurrence roles))
                    (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence roles)) children)
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
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
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles chosen →
            @Yulang.GeneralDictionaryAliasTreeLocality.Leaf roles
                (@Yulang.GeneralNominalSaturationState.State.context roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                focus chosen →
              ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                    (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                      (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                  @Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered roles registry state focus chosen →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      @Yulang.GeneralNominalSaturationState.Models roles
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                        @Yulang.GeneralNominalJointCandidates.Joint roles registry
                          (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.initial_trace_joint : ∀ {roles : Yulang.Roles.RoleDecls}
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
              @Yulang.GeneralDictionaryAliasTreeLocality.Leaf roles
                  (@Yulang.GeneralNominalSaturationState.State.context roles
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                  focus chosen →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  @Yulang.GeneralNominalSupportBoundary.Local roles registry state focus
                      (@Yulang.CommonRoleOutermostResolver.Frontier.selected
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles).Demand key children) →
                    @Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.Covered roles registry state focus chosen →
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        @Yulang.GeneralNominalSaturationState.Models roles
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                          @Yulang.GeneralNominalJointCandidates.Joint roles registry
                            (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus key
@Yulang.GeneralDictionaryUnrecordedVariableJoint.selected_branch : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSupport.Tracked roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (chosen : Yulang.GeneralDeclarations.Declaration),
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
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                And (@Eq Nat chosen.id key)
                  (@Yulang.GeneralNominalJointCandidates.BranchAt roles registry
                    (@Yulang.GeneralNominalSupport.Tracked.current roles state) focus chosen.id model)
@Yulang.GeneralDictionaryUnrecordedVariableJoint.covered_joint : ∀ {roles : Yulang.Roles.RoleDecls}
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

```
