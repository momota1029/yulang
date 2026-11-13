import Yulang.GeneralDictionaryObservedFiniteRequests
import Yulang.GeneralNominalSpineFacts
import Yulang.GeneralDictionaryNestedLeaf
import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! Structural arbitrary finite-spine nominal leaves need no recorded packet. Their complete branch
is valid at every current source model, before comparing against selection. -/
namespace Yulang.GeneralDictionary170NamedSpine
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralDictionaryRecursiveEvidence

/-- Syntax/state witnesses only: no BranchModels, Instance, Evidence, packet,
Joint, Installable, or assumption about a successful selected declaration. -/
structure Shape (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration) where
  terminal : declaration.requirements = []
  role : declaration.role = root.demand.role
  slot : Fin context.state.base.slots
  arity : Nat
  names : Fin arity → Nat
  distinct : Function.Injective names
  inputs : declaration.inputNames = List.ofFn names
  bounds : Fin arity → GeneralNominalInspection.Bounds context.state
  spine : GeneralNominalSpineFacts.Spine context.state names bounds slot
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [spine.query]
  located : arguments context root = some [(slot,slot)]
  defined : GeneralNominalMaterialization.RootDefined declaration root
  observed : GeneralDictionaryObservedFiniteRequests.Observed context.state context.interpretation
    (GeneralNominalMaterialization.requests context.state registry root declaration checked
      (bindings context.state (report context declaration [(slot,slot)])))

theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape registry context root declaration checked)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.slot,shape.slot)] model := by
  have privateValid := GeneralNominalSpineFacts.private_models context registry root declaration shape.names shape.distinct shape.inputs shape.bounds shape.spine shape.query model valid
  refine ⟨privateValid.1,privateValid.2,?_⟩
  exact GeneralDictionaryObservedFiniteRequests.generated_models context.state context.interpretation _
    shape.observed declaration _ _ model valid

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape registry context root declaration checked) :
    RequestReady registry context root declaration checked [(shape.slot,shape.slot)] := by
  exact ⟨shape.defined,(GeneralDictionaryObservedFiniteRequests.generated_shape context.state
    context.interpretation _ shape.observed).2⟩

/-- A semantic instance is constructed independently of selected key/children,
using only current metadata and a structural leaf witness. -/
theorem instance_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape registry context root declaration checked)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id [] := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,?_,?_,metadata,?_⟩
  · rw [GeneralNominalSpineFacts.report_exact context declaration shape.names shape.bounds shape.spine shape.query]
    exact GeneralNominalSpineFacts.spine_finished context.state shape.names shape.bounds shape.spine none
  · exact ready context registry root declaration checked shape
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked shape.terminal _).symm
  · exact branch_models context registry root declaration checked shape model valid

theorem evidence_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape registry context root declaration checked)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Evidence registry context model root (.node declaration.id []) :=
  (evidence_leaf_iff registry context model root declaration.id).mpr
    (instance_of_shape context registry root declaration visible checked shape metadata model valid)
end Yulang.GeneralDictionary170NamedSpine
