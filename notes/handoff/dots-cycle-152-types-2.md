# Cycle152 exact theorem types (2)

```lean
Yulang.GeneralDictionaryObservedClosedExample.observed : Yulang.GeneralDictionaryObservedClosedRequests.Observed
  (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.interpretation
  (@List.cons Yulang.GeneralNominalMaterialization.Request Yulang.GeneralDictionaryObservedClosedExample.request
    (@List.nil Yulang.GeneralNominalMaterialization.Request))
Yulang.GeneralDictionaryObservedClosedExample.not_scalar_observed : Not
  (Yulang.GeneralDictionaryObservedScalarRequests.Observed (Yulang.GeneralNominalExamples.state true)
    Yulang.GeneralNominalExamples.interpretation
    (@List.cons Yulang.GeneralNominalMaterialization.Request Yulang.GeneralDictionaryObservedClosedExample.request
      (@List.nil Yulang.GeneralNominalMaterialization.Request)))
Yulang.GeneralDictionaryObservedClosedExample.tests_exact : @Eq
  (List (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test))
  (Yulang.GeneralNominalMaterialization.generated (Yulang.GeneralNominalExamples.state true)
      Yulang.GeneralNominalExamples.interpretation
      (@List.cons Yulang.GeneralNominalMaterialization.Request Yulang.GeneralDictionaryObservedClosedExample.request
        (@List.nil Yulang.GeneralNominalMaterialization.Request))).tests
  (@List.cons (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)
    (@Prod.mk Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test
      (Yulang.GeneralNominalRecursiveInspection.Origin.source (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Yulang.GeneralNominalRecursiveInspection.Test.nominal (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@List.cons (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test)
      (@Prod.mk Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test
        ((Yulang.GeneralNominalRecursiveInspection.Origin.source
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).nominal
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
      (@List.nil (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test))))
Yulang.GeneralDictionaryObservedClosedExample.every_source_model : ∀
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report : Yulang.GeneralNominalRecursiveInspection.Report (Yulang.GeneralNominalExamples.state true))
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) assignment →
    Yulang.GeneralNominalMaterialization.Models (Yulang.GeneralNominalExamples.state true) declaration capture report
      (Yulang.GeneralNominalMaterialization.generated (Yulang.GeneralNominalExamples.state true)
        Yulang.GeneralNominalExamples.interpretation
        (@List.cons Yulang.GeneralNominalMaterialization.Request Yulang.GeneralDictionaryObservedClosedExample.request
          (@List.nil Yulang.GeneralNominalMaterialization.Request)))
      assignment
Yulang.GeneralDictionaryObservedClosedExample.inhabited_request_models : ∀
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report : Yulang.GeneralNominalRecursiveInspection.Report (Yulang.GeneralNominalExamples.state true)),
  And (Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.model)
    (Yulang.GeneralNominalMaterialization.Models (Yulang.GeneralNominalExamples.state true) declaration capture report
      (Yulang.GeneralNominalMaterialization.generated (Yulang.GeneralNominalExamples.state true)
        Yulang.GeneralNominalExamples.interpretation
        (@List.cons Yulang.GeneralNominalMaterialization.Request Yulang.GeneralDictionaryObservedClosedExample.request
          (@List.nil Yulang.GeneralNominalMaterialization.Request)))
      Yulang.GeneralNominalExamples.model)
Yulang.GeneralDictionaryObservedClosedRequests.empty_valid : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model { }
Yulang.GeneralDictionaryObservedClosedRequests.append_valid : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (first last : Yulang.GeneralNominalMaterialization.Schema),
  Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model first →
    Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model last →
      Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model (first.append last)
Yulang.GeneralDictionaryObservedClosedRequests.prepend_valid : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (value : Yulang.GeneralNominalMaterialization.Schema)
  (test : Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test),
  Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model value →
    Yulang.GeneralDictionaryObservedClosedRequests.TestValid model test →
      Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
        { variables := value.variables,
          tests :=
            @List.cons
              (Prod Yulang.GeneralNominalRecursiveInspection.Origin Yulang.GeneralNominalRecursiveInspection.Test) test
              value.tests,
          unknown := value.unknown }
Yulang.GeneralDictionaryObservedClosedRequests.nominal_valid : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      @Eq (Option (Yulang.GeneralNominalState.Descriptor state.base.slots)) (state.nominals slot)
          (@some (Yulang.GeneralNominalState.Descriptor state.base.slots) descriptor) →
        ∀ (arity : Nat),
          @Eq Nat
              (@List.length (Yulang.GeneralNominalState.Parameter state.base.slots)
                (@Yulang.GeneralNominalState.Descriptor.arguments state.base.slots descriptor))
              arity →
            ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
              Yulang.GeneralNominalSpineFacts.Matches state model slot origin →
                Yulang.GeneralDictionaryObservedClosedRequests.TestValid model
                  (@Prod.mk Yulang.GeneralNominalRecursiveInspection.Origin
                    Yulang.GeneralNominalRecursiveInspection.Test origin
                    (Yulang.GeneralNominalRecursiveInspection.Test.nominal
                      (@Yulang.GeneralNominalState.Descriptor.declaration state.base.slots descriptor).name arity))
Yulang.GeneralDictionaryObservedClosedRequests.tree_schema : ∀ (state : Yulang.GeneralNominalState.State)
  {slot : Fin state.base.slots} {query : Yulang.GeneralNominalInspection.Query}
  (tree : Yulang.GeneralDictionaryObservedClosedRequests.Tree state slot query)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin) (mode : Yulang.GeneralNominalMaterialization.Mode),
      Yulang.GeneralNominalSpineFacts.Matches state model slot origin →
        Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
          (Yulang.GeneralNominalMaterialization.schema query origin mode)
Yulang.GeneralDictionaryObservedClosedRequests.tree_shape : ∀ (state : Yulang.GeneralNominalState.State)
  {slot : Fin state.base.slots} {query : Yulang.GeneralNominalInspection.Query}
  (tree : Yulang.GeneralDictionaryObservedClosedRequests.Tree state slot query)
  (origin : Yulang.GeneralNominalRecursiveInspection.Origin) (mode : Yulang.GeneralNominalMaterialization.Mode),
  And
    (@Eq (List Yulang.GeneralNominalMaterialization.Use)
      (Yulang.GeneralNominalMaterialization.schema query origin mode).variables
      (@List.nil Yulang.GeneralNominalMaterialization.Use))
    (@Eq Bool (Yulang.GeneralNominalMaterialization.schema query origin mode).unknown false)
Yulang.GeneralDictionaryObservedClosedRequests.generated_shape : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedClosedRequests.Observed state interpretation requests →
    And
      (@Eq (List Yulang.GeneralNominalMaterialization.Use)
        (Yulang.GeneralNominalMaterialization.generated state interpretation requests).variables
        (@List.nil Yulang.GeneralNominalMaterialization.Use))
      (@Eq Bool (Yulang.GeneralNominalMaterialization.generated state interpretation requests).unknown false)
Yulang.GeneralDictionaryObservedClosedRequests.generated_valid : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedClosedRequests.Observed state interpretation requests →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        Yulang.GeneralDictionaryObservedClosedRequests.ClosedValid model
          (Yulang.GeneralNominalMaterialization.generated state interpretation requests)
Yulang.GeneralDictionaryObservedClosedRequests.generated_models : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedClosedRequests.Observed state interpretation requests →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
      (report : Yulang.GeneralNominalRecursiveInspection.Report state)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        Yulang.GeneralNominalMaterialization.Models state declaration capture report
          (Yulang.GeneralNominalMaterialization.generated state interpretation requests) model
Yulang.GeneralDictionaryObservedClosedRequests.observed_of_scalar : ∀ (state : Yulang.GeneralNominalState.State)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation)
  (requests : List Yulang.GeneralNominalMaterialization.Request),
  Yulang.GeneralDictionaryObservedScalarRequests.Observed state interpretation requests →
    Yulang.GeneralDictionaryObservedClosedRequests.Observed state interpretation requests
Yulang.GeneralDictionaryObservedCompleteClassification.acyclic : ∀ (source : Nat),
  Not
    (@Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
      source)
Yulang.GeneralDictionaryObservedCompleteClassification.parent_selected : @Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
  Yulang.GeneralDictionaryObservedCompleteExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
    Yulang.GeneralDictionaryObservedCompleteExample.children)
Yulang.GeneralDictionaryObservedCompleteClassification.child_selected : @Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryObservedCompleteInstallation.installed)
  Yulang.GeneralDictionaryObservedCompleteEvidence.child
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralNominalExamples.intDisplay.id
    (@List.nil (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))
Yulang.GeneralDictionaryObservedCompleteClassification.supported_parent : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed Yulang.GeneralDictionaryObservedCompleteExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryObservedCompleteExample.declaration.id
    Yulang.GeneralDictionaryObservedCompleteExample.children)
Yulang.GeneralDictionaryObservedCompleteClassification.supported_child : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryObservedCompleteExample.registry
  Yulang.GeneralDictionaryObservedCompleteInstallation.installed Yulang.GeneralDictionaryObservedCompleteEvidence.child
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralNominalExamples.intDisplay.id
    (@List.nil (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand))

```
