import Yulang.GeneralDictionaryObservedClosedRequests

/-! Tree branches with finite named-output or compound-input requests already
supported by closed nominal source trees. No terminal/no-output hypothesis. Closed queries have no variables; internal nominal edges are point intervals. -/
namespace Yulang.GeneralDictionaryClosedTreeBranch
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence

structure Shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration) where
  role : declaration.role = root.demand.role
  slot : Fin context.state.base.slots
  arity : Nat
  names : Fin arity → Nat
  distinct : Function.Injective names
  inputs : declaration.inputNames = List.ofFn names
  bounds : Fin arity → GeneralNominalInspection.Bounds context.state
  tree : GeneralNominalTreeFacts.Tree context.state names bounds slot
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [tree.query]
  located : arguments context root = some [(slot,slot)]
  defined : GeneralNominalMaterialization.RootDefined declaration root
  observed : GeneralDictionaryObservedClosedRequests.Observed context.state context.interpretation
    (GeneralNominalMaterialization.requests context.state registry root declaration checked
      (bindings context.state (report context declaration [(slot,slot)])))

theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context registry root declaration checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.slot,shape.slot)] model := by
  have privateValid := GeneralNominalTreeFacts.private_models context registry root declaration shape.names shape.distinct shape.inputs shape.bounds shape.tree shape.query model valid
  exact ⟨privateValid.1,privateValid.2,
    GeneralDictionaryObservedClosedRequests.generated_models context.state context.interpretation _
      shape.observed declaration _ _ model valid⟩

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context registry root declaration checked) :
    RequestReady registry context root declaration checked [(shape.slot,shape.slot)] :=
  ⟨shape.defined,(GeneralDictionaryObservedClosedRequests.generated_shape context.state
    context.interpretation _ shape.observed).2⟩

theorem instance_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context registry root declaration checked)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id
      (GeneralNominalAllocation.children context.state registry root declaration checked
        (bindings context.state (report context declaration [(shape.slot,shape.slot)]))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,
    ready context registry root declaration checked shape,rfl,metadata,
    branch_models context registry root declaration checked shape model valid⟩
  rw [GeneralNominalTreeFacts.report_exact context declaration shape.tree shape.query]
  exact GeneralNominalTreeFacts.tree_finished context.state shape.tree none

/-- Actual selected key and children are derived by uniqueness; no conclusion
about output equations is smuggled into the structural observation witness. -/
theorem selected_instance (registry : Registry) (state : GeneralNominalSaturationState.State roles)
    (root : Occurrence roles) (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.context registry root declaration checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state.context.state model) :
    declaration.id = key ∧ Instance registry state.context model root key children := by
  have metadata : Metadata registry state.context := by
    cases selected with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have rule := instance_of_shape state.context registry root declaration visible checked shape metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry state root model declaration.id key
    _ children rule selected
  exact ⟨same.1,by simpa only [same.1,same.2] using rule⟩
end Yulang.GeneralDictionaryClosedTreeBranch
