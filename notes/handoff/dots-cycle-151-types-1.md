# Cycle151 exact quantified theorem types

```text
Yulang.GeneralDictionaryEarlyMergeScalarClassification.parent_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  Yulang.GeneralDictionaryEarlyMergeScalarClassification.current Yulang.GeneralNominalExamples.model
  Yulang.GeneralNominalExamples.displayRoot (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  Yulang.GeneralDictionaryEarlyMergeScalarExample.children
Yulang.GeneralDictionaryEarlyMergeScalarClassification.acyclic : ∀ (source : Nat),
  Not
    (@Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      source)
Yulang.GeneralDictionaryEarlyMergeScalarClassification.child_selected : ∀ (n : Nat),
  @Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
    (@Yulang.CommonRoleOutermostResolver.Frontier.selected
      (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@List.nil (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
Yulang.GeneralDictionaryEarlyMergeScalarClassification.supported_child : ∀ (n : Nat),
  @Yulang.GeneralNominalSupportBoundary.Local Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralDictionaryEarlyMergeScalarExample.finish
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
    (@Yulang.CommonRoleOutermostResolver.Frontier.selected
      (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@List.nil (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.parent_instance : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      Yulang.GeneralNominalExamples.displayRoot (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      Yulang.GeneralDictionaryEarlyMergeScalarExample.children
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.child_instance : ∀ (n : Nat)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.child_evidence : ∀ (n : Nat)
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.child n)
      (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.full_evidence : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  @Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      assignment →
    @Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current assignment
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.edges_exact : @Eq
  (List
    (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
  (@Yulang.GeneralNominalSaturationState.State.edges Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.finish))
  (@List.cons
    (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
    (@Prod.mk (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralNominalExamples.displayRoot
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.child
        (@OfNat.ofNat Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
    (@List.cons
      (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
      (@Prod.mk (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
        Yulang.GeneralNominalExamples.displayRoot
        (Yulang.GeneralDictionaryEarlyMergeScalarExample.child
          (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
      (@List.nil
        (Prod (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
          (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))))
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.generated_cases : ∀
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  @Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      Yulang.GeneralNominalExamples.displayRoot focus →
    Or
      (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) focus
        Yulang.GeneralNominalExamples.displayRoot)
      (Or
        (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) focus
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child
            (@OfNat.ofNat Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
        (@Eq (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) focus
          (Yulang.GeneralDictionaryEarlyMergeScalarExample.child
            (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))))
Yulang.GeneralDictionaryEarlyMergeScalarEvidence.reachable_full_evidence : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryEarlyMergeScalarExample.finish)
      Yulang.GeneralNominalExamples.model)
    (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
      Yulang.GeneralDictionaryEarlyMergeScalarClassification.current Yulang.GeneralNominalExamples.model
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarEvidence.payload))
Yulang.GeneralDictionaryEarlyMergeScalarExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
Yulang.GeneralDictionaryEarlyMergeScalarExample.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
Yulang.GeneralDictionaryEarlyMergeScalarExample.all_source_decisions : ∀
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  (∀
      (index :
        Fin
          (Yulang.GeneralDeclarationExamples.roles
              (@Yulang.GeneralSourceState.Demand.role Yulang.GeneralDeclarationExamples.roles
                (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
                  root))).arity),
      @Eq Yulang.GeneralSourceState.Interval
        (@Yulang.GeneralSourceState.Demand.arguments Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles root) index)
        (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
    @Yulang.GeneralNominalSupport.DecisionGuard Yulang.GeneralDeclarationExamples.roles
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.start root)
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry root
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryEarlyMergeScalarExample.query : @Eq (List Yulang.GeneralNominalInspection.Query)
  (Yulang.GeneralNominalInspection.queries (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralNominalExamples.interpretation Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration)
  (@List.cons Yulang.GeneralNominalInspection.Query
    (Yulang.GeneralNominalInspection.Query.nominal (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Yulang.GeneralNominalInspection.Query
        (Yulang.GeneralNominalInspection.Query.variables
          (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
        (@List.nil Yulang.GeneralNominalInspection.Query)))
    (@List.nil Yulang.GeneralNominalInspection.Query))
Yulang.GeneralDictionaryEarlyMergeScalarExample.schema : @Eq Yulang.GeneralNominalMaterialization.Schema
  (@Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryEarlyMergeScalarExample.registry (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
    Yulang.GeneralDictionaryEarlyMergeScalarExample.checked
    (@List.cons (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)
      (@Prod.mk (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
        (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
        (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
          (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0)))
        (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
          (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0))))
      (@List.nil (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state))))
  { }
Yulang.GeneralDictionaryEarlyMergeScalarExample.branch : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) m →
    @Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryEarlyMergeScalarExample.registry (Yulang.GeneralNominalExamples.context true)
      Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration
      Yulang.GeneralDictionaryEarlyMergeScalarExample.checked
      (@List.cons (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)
        (@Prod.mk (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
          (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots)
          (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
            (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat (Fin (Yulang.GeneralNominalExamples.context true).state.base.slots) (nat_lit 0)
            (@Fin.instOfNat (Yulang.GeneralNominalExamples.context true).state.base.slots ⋯ (nat_lit 0))))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds (Yulang.GeneralNominalExamples.context true).state)))
      m
Yulang.GeneralDictionaryEarlyMergeScalarExample.prepared : @Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
  Yulang.GeneralDictionaryEarlyMergeScalarExample.declaration Yulang.GeneralDictionaryEarlyMergeScalarExample.checked
Yulang.GeneralDictionaryEarlyMergeScalarExample.survivor : @Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Yulang.GeneralDictionaryEarlyMergeScalarExample.children
Yulang.GeneralDictionaryEarlyMergeScalarExample.selected : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralNominalExamples.displayRoot
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Yulang.GeneralDictionaryEarlyMergeScalarExample.children)
Yulang.GeneralDictionaryEarlyMergeScalarExample.children_exact : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryEarlyMergeScalarExample.children
  (@List.cons (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.child (@OfNat.ofNat Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
    (@List.cons (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (Yulang.GeneralDictionaryEarlyMergeScalarExample.child
        (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))))
Yulang.GeneralDictionaryEarlyMergeScalarExample.enabled : @Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryEarlyMergeScalarExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot))
  Yulang.GeneralDictionaryEarlyMergeScalarExample.packet
Yulang.GeneralDictionaryEarlyMergeScalarExample.packet_guard : @Yulang.GeneralNominalSupportSteps.PacketGuard
  Yulang.GeneralDeclarationExamples.roles
  (Yulang.GeneralDictionaryEarlyMergeScalarExample.start Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionaryEarlyMergeScalarExample.packet
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))

```
