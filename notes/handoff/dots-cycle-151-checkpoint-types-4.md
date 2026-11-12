# Cycle151 checkpoint theorem types

```text
                      (@Yulang.GeneralNominalSaturationState.State.context roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                      model focus dictionary
@Yulang.GeneralDictionaryVariableTreeCoverage.dictionaries_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.GeneralNominalSupportSteps.SourceFormed roles registry root state →
    ∀ (domain : Yulang.GeneralSourceDictionaries.Occurrence roles → Prop),
      @Yulang.GeneralDictionaryVariableTreeCoverage.CoveredOn roles registry state domain →
        @Yulang.GeneralDictionaryVariableTreeCoverage.ClosedOn roles registry state domain →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            @Yulang.GeneralNominalSaturationState.Models roles
                (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
              ∀ (dictionaries : List Yulang.GeneralDictionaryReadback.Payload)
                (demands : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                (∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
                    @Membership.mem (Yulang.GeneralSourceDictionaries.Occurrence roles)
                        (List (Yulang.GeneralSourceDictionaries.Occurrence roles))
                        (@List.instMembership (Yulang.GeneralSourceDictionaries.Occurrence roles)) demands focus →
                      domain focus) →
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
@Yulang.GeneralDictionaryVariableTreeCoverage.reachable_dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  @Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
      (Yulang.GeneralNominalSupportBoundary.boundary roles) registry root state →
    ∀ (domain : Yulang.GeneralSourceDictionaries.Occurrence roles → Prop),
      domain root →
        @Yulang.GeneralDictionaryVariableTreeCoverage.CoveredOn roles registry state domain →
          @Yulang.GeneralDictionaryVariableTreeCoverage.ClosedOn roles registry state domain →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              @Yulang.GeneralNominalSaturationState.Models roles
                  (@Yulang.GeneralNominalSupport.Tracked.current roles state) model →
                ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                  @Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                      (@Yulang.B4TargetV5.SourceBoundary.toSourceBoundary
                        (Yulang.GeneralNominalSupportBoundary.vocabulary roles)
                        (Yulang.GeneralNominalSupportBoundary.boundary roles))
                      registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence roles registry
                      (@Yulang.GeneralNominalSaturationState.State.context roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                      model root dictionary
Yulang.GeneralDictionaryVariableTreeEvidence.children_exact : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryVariableTreeExample.children
  (@List.cons (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeEvidence.child
    (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
Yulang.GeneralDictionaryVariableTreeEvidence.captures_exact : @Eq Yulang.GeneralNominalAllocation.Bindings
  Yulang.GeneralDictionaryVariableTreeEvidence.captures
  (@List.cons (Prod Nat (Prod Nat Nat))
    (@Prod.mk Nat (Prod Nat Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@List.cons (Prod Nat (Prod Nat Nat))
      (@Prod.mk Nat (Prod Nat Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@List.nil (Prod Nat (Prod Nat Nat)))))
Yulang.GeneralDictionaryVariableTreeEvidence.child_arguments : @Eq
  (Option (List (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state)))
  (@Yulang.GeneralNominalRecursiveCandidates.arguments Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralNominalBranchExample.context Yulang.GeneralDictionaryVariableTreeEvidence.child)
  (@some
    (List
      (Prod (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)))
    (@List.cons
      (Prod (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots))
      (@Prod.mk (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 1)
          (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 1)))
        (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 1)
          (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 1))))
      (@List.nil
        (Prod (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
          (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)))))
Yulang.GeneralDictionaryVariableTreeEvidence.leaf_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration
Yulang.GeneralDictionaryVariableTreeEvidence.child_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralDictionaryVariableTreeEvidence.child Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeEvidence.child_evidence : @Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralDictionaryVariableTreeEvidence.child
  (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
    (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
Yulang.GeneralDictionaryVariableTreeEvidence.full_evidence : @Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralNominalBranchExample.root
  (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.declaration.id
    (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
        (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
      (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary)))
Yulang.GeneralDictionaryVariableTreeEvidence.reachable_inhabited_full_evidence : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
    Yulang.GeneralDictionaryVariableTreeExample.start)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.start)
      Yulang.GeneralNominalBranchExample.model)
    (And
      (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.registry
        (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryVariableTreeExample.start))
        Yulang.GeneralNominalBranchExample.model Yulang.GeneralNominalBranchExample.root
        (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.declaration.id
          (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
            (Yulang.CommonRoleOutermostResolver.Dictionary.node
              Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
              (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
            (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))))
      (@Ne (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
        Yulang.GeneralDictionaryVariableTreeExample.children
        (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))))
Yulang.GeneralDictionaryVariableTreeExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryVariableTreeExample.declaration
Yulang.GeneralDictionaryVariableTreeExample.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
Yulang.GeneralDictionaryVariableTreeExample.nonterminal : @Ne (List Yulang.GeneralDeclarations.Clause)
  Yulang.GeneralDictionaryVariableTreeExample.declaration.requirements (@List.nil Yulang.GeneralDeclarations.Clause)
Yulang.GeneralDictionaryVariableTreeExample.actual_children_count : @Eq Nat
  (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeExample.children)
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
Yulang.GeneralDictionaryVariableTreeExample.actual_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.declaration.id
  Yulang.GeneralDictionaryVariableTreeExample.children
Yulang.GeneralDictionaryVariableTreeExample.inhabited_nonterminal : And
  (Yulang.GeneralNominalState.Models Yulang.GeneralNominalBranchExample.state Yulang.GeneralNominalBranchExample.model)
  (And
    (@Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
      Yulang.GeneralNominalBranchExample.model Yulang.GeneralNominalBranchExample.root
      Yulang.GeneralDictionaryVariableTreeExample.declaration.id Yulang.GeneralDictionaryVariableTreeExample.children)
    (@Ne (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
      Yulang.GeneralDictionaryVariableTreeExample.children
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))))
Yulang.GeneralDictionaryVariableTreeExample.initial_source : @Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.root
Yulang.GeneralDictionaryVariableTreeExample.initial_models : @Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralNominalBranchExample.model
Yulang.GeneralDictionaryVariableTreeExample.actual_reachable : @Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
  Yulang.GeneralDictionaryVariableTreeExample.start

```
