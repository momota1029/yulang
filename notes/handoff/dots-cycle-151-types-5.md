# Cycle151 exact quantified theorem types

```text
  Yulang.GeneralDictionaryObservedScalarRequests.Observed state interpretation requests →
    And
      (@Eq (List Yulang.GeneralNominalMaterialization.Use)
        (Yulang.GeneralNominalMaterialization.generated state interpretation requests).variables
        (@List.nil Yulang.GeneralNominalMaterialization.Use))
      (And (@Eq Bool (Yulang.GeneralNominalMaterialization.generated state interpretation requests).unknown false)
        (∀ (test : Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test),
          @Membership.mem
              (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)
              (List
                (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test))
              (@List.instMembership
                (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test))
              (Yulang.GeneralNominalMaterialization.generated state interpretation requests).tests test →
            @Exists (Fin state.base.slots) fun slot =>
              @Exists Yulang.Inference.Base fun base =>
                And
                  (@Eq
                    (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)
                    test
                    (@Prod.mk Yulang.GeneralNominalRecursiveInspection.Origin
                      Yulang.GeneralNominalRecursiveInspection.Test
                      (Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot))
                      (Yulang.GeneralNominalRecursiveInspection.Test.scalar base)))
                  (@Eq
                    (@Yulang.GeneralNormalizedObservation.Head
                      (@Yulang.GeneralNormalizedObservation.Snapshot.kinds state.base state.view)
                      (@Yulang.GeneralNormalizedObservation.Snapshot.shapes state.base state.view) state.base.slots)
                    (@Yulang.GeneralNormalizedObservation.Snapshot.heads state.base state.view slot)
                    (@Yulang.GeneralNormalizedObservation.Head.scalar
                      (@Yulang.GeneralNormalizedObservation.Snapshot.kinds state.base state.view)
                      (@Yulang.GeneralNormalizedObservation.Snapshot.shapes state.base state.view) state.base.slots
                      base))))
@Yulang.GeneralDictionaryObservedScalarRequests.requests_root : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (captures : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralDictionaryVariableRequirements.VariableClauses declaration →
    @Eq (List Yulang.GeneralNominalMaterialization.Request)
      (@Yulang.GeneralNominalMaterialization.requests roles state registry root declaration checked captures)
      (@Yulang.GeneralNominalMaterialization.rootRequests roles declaration root)
Yulang.GeneralDictionaryObservedScalarRequests.generated_models : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedScalarRequests.Observed state interpretation requests →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
      (report : Yulang.GeneralNominalRecursiveInspection.Report state)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        Yulang.GeneralNominalMaterialization.Models state declaration capture report
          (Yulang.GeneralNominalMaterialization.generated state interpretation requests) model
@Yulang.GeneralDictionaryObservedTreeBranch.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : @Yulang.GeneralDictionaryObservedTreeBranch.Shape roles context registry root declaration checked)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models context.state model →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels roles registry context root declaration checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
        (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
          (@Yulang.GeneralDictionaryObservedTreeBranch.Shape.slot roles context registry root declaration checked shape)
          (@Yulang.GeneralDictionaryObservedTreeBranch.Shape.slot roles context registry root declaration checked
            shape))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state)))
      model
@Yulang.GeneralDictionaryObservedTreeBranch.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : @Yulang.GeneralDictionaryObservedTreeBranch.Shape roles context registry root declaration checked),
  @Yulang.GeneralNominalRecursiveCandidates.RequestReady roles registry context root declaration checked
    (@List.cons (Yulang.GeneralNominalInspection.Bounds context.state)
      (@Prod.mk (Fin context.state.base.slots) (Fin context.state.base.slots)
        (@Yulang.GeneralDictionaryObservedTreeBranch.Shape.slot roles context registry root declaration checked shape)
        (@Yulang.GeneralDictionaryObservedTreeBranch.Shape.slot roles context registry root declaration checked shape))
      (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state)))
@Yulang.GeneralDictionaryObservedTreeBranch.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape : @Yulang.GeneralDictionaryObservedTreeBranch.Shape roles context registry root declaration checked),
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
                        (@Yulang.GeneralDictionaryObservedTreeBranch.Shape.slot roles context registry root declaration
                          checked shape)
                        (@Yulang.GeneralDictionaryObservedTreeBranch.Shape.slot roles context registry root declaration
                          checked shape))
                      (@List.nil (Yulang.GeneralNominalInspection.Bounds context.state))))))
@Yulang.GeneralDictionaryObservedTreeBranch.selected_instance : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  @Membership.mem Yulang.GeneralDeclarations.Declaration (List Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership Yulang.GeneralDeclarations.Declaration) registry.declarations declaration →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (shape :
        @Yulang.GeneralDictionaryObservedTreeBranch.Shape roles
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
Yulang.GeneralDictionaryObservedTreeExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryObservedTreeExample.declaration
Yulang.GeneralDictionaryObservedTreeExample.requests_exact : @Eq (List Yulang.GeneralNominalMaterialization.Request)
  (@Yulang.GeneralNominalMaterialization.requests Yulang.GeneralDeclarationExamples.roles
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralDictionaryObservedTreeExample.registry
    Yulang.GeneralDictionaryObservedTreeExample.root Yulang.GeneralDictionaryObservedTreeExample.declaration
    Yulang.GeneralDictionaryObservedTreeExample.checked
    (Yulang.GeneralNominalRecursiveInspection.bindings (Yulang.GeneralNominalExamples.state true)
      (Yulang.GeneralNominalRecursiveCandidates.report (Yulang.GeneralNominalExamples.context true)
        Yulang.GeneralDictionaryObservedTreeExample.declaration
        (@List.cons (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)
          (@Prod.mk (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
            (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
            (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
              (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0)))
            (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
              (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0))))
          (@List.nil (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state))))))
  (@List.cons Yulang.GeneralNominalMaterialization.Request
    {
      pattern :=
        Yulang.GeneralDeclarationPatterns.Pattern.app (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@List.nil Yulang.GeneralDeclarationPatterns.Pattern),
      target := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
      mode := Yulang.GeneralNominalMaterialization.Mode.actual }
    (@List.nil Yulang.GeneralNominalMaterialization.Request))
Yulang.GeneralDictionaryObservedTreeExample.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryObservedTreeExample.registry (Yulang.GeneralNominalExamples.context true)
Yulang.GeneralDictionaryObservedTreeExample.named_request_present : @Ne (List Yulang.GeneralSourceState.Output)
  (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedTreeExample.root))
  (@List.nil Yulang.GeneralSourceState.Output)
Yulang.GeneralDictionaryObservedTreeExample.nonterminal : @Ne (List Yulang.GeneralDeclarations.Clause)
  Yulang.GeneralDictionaryObservedTreeExample.declaration.requirements (@List.nil Yulang.GeneralDeclarations.Clause)
Yulang.GeneralDictionaryObservedTreeExample.every_source_model : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) assignment →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryObservedTreeExample.registry (Yulang.GeneralNominalExamples.context true)
      Yulang.GeneralDictionaryObservedTreeExample.root Yulang.GeneralDictionaryObservedTreeExample.declaration
      Yulang.GeneralDictionaryObservedTreeExample.checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)
        (@Prod.mk (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
          (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
          (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
            (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
            (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0))))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)))
      assignment
Yulang.GeneralDictionaryObservedTreeExample.actual_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedTreeExample.registry
  (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.model
  Yulang.GeneralDictionaryObservedTreeExample.root Yulang.GeneralDictionaryObservedTreeExample.declaration.id
  (@Yulang.GeneralNominalAllocation.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.constructors (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralDictionaryObservedTreeExample.registry Yulang.GeneralDictionaryObservedTreeExample.root
    Yulang.GeneralDictionaryObservedTreeExample.declaration Yulang.GeneralDictionaryObservedTreeExample.checked
    (Yulang.GeneralNominalRecursiveInspection.bindings (Yulang.GeneralNominalExamples.state true)
      (Yulang.GeneralNominalRecursiveCandidates.report (Yulang.GeneralNominalExamples.context true)
        Yulang.GeneralDictionaryObservedTreeExample.declaration
        (@List.cons (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)
          (@Prod.mk (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
            (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
            (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
              (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0)))
            (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
              (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0))))
          (@List.nil (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state))))))
@Yulang.GeneralDictionarySelectedAliasConflict.branch_selected_key : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (key selectedKey : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalJointCandidates.BranchAt roles registry state focus key model →
    ∀ (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralNominalFeedbackK2.Local roles registry state focus
          (@Yulang.CommonRoleOutermostResolver.Frontier.selected
            (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand selectedKey children) →
        @Eq Nat key selectedKey
@Yulang.GeneralDictionarySelectedAliasConflict.joint_related_selected_key : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (key selectedKey : Nat),
  @Yulang.GeneralNominalJointCandidates.Joint roles registry state focus key →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      @Yulang.GeneralNominalJointCandidates.Related roles state focus site →
        ∀ (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          @Yulang.GeneralNominalFeedbackK2.Local roles registry state
              (@Yulang.GeneralNominalDemandMerging.Site.occurrence roles site)
              (@Yulang.CommonRoleOutermostResolver.Frontier.selected

```
