import Yulang.GeneralNominalSpineFacts
import Yulang.GeneralDictionaryNestedLeaf
import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! Structural arbitrary finite-spine nominal leaves need no recorded packet. Their complete branch
is valid at every current source model, before comparing against selection. -/
namespace Yulang.GeneralDictionarySpineLeaf
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralDictionaryRecursiveEvidence

/-- Syntax/state witnesses only: no BranchModels, Instance, Evidence, packet,
Joint, Installable, or assumption about a successful selected declaration. -/
structure SpineLeafShape (context : Context) (root : Occurrence roles)
    (declaration : Declaration) where
  terminal : declaration.requirements = []
  outputs : root.demand.outputs = []
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

theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : SpineLeafShape context root declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.slot,shape.slot)] model := by
  have privateValid := GeneralNominalSpineFacts.private_models context registry root declaration shape.names shape.distinct shape.inputs shape.bounds shape.spine shape.query model valid
  refine ⟨privateValid.1,privateValid.2,?_⟩
  rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked shape.terminal shape.outputs]
  exact GeneralNominalMaterialization.empty_models ..

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : SpineLeafShape context root declaration) :
    RequestReady registry context root declaration checked [(shape.slot,shape.slot)] := by
  constructor
  · intro output member
    rw [shape.outputs] at member
    cases member
  · rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked shape.terminal shape.outputs]

/-- A semantic instance is constructed independently of selected key/children,
using only current metadata and a structural leaf witness. -/
theorem instance_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : SpineLeafShape context root declaration)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id [] := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,?_,?_,metadata,?_⟩
  · rw [GeneralNominalSpineFacts.report_exact context declaration shape.names shape.bounds shape.spine shape.query]
    exact GeneralNominalSpineFacts.spine_finished context.state shape.names shape.bounds shape.spine none
  · exact ready context registry root declaration checked shape
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked shape.terminal _).symm
  · exact branch_models context registry root declaration checked shape model valid

/-- An unrecorded leaf can identify the current selected declaration by actual
uniqueness. No assumption equates its source declaration ID with the selected key. -/
theorem selected_leaf (registry : Registry) (state : State roles) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : SpineLeafShape state.context root declaration)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model) :
    declaration.id = key ∧ children = [] ∧ Instance registry state.context model root key [] ∧
      Evidence registry state.context model root (.node key []) := by
  have metadata : Metadata registry state.context := by
    cases selected with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have instanceRule := instance_of_shape state.context registry root declaration visible checked shape metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry state root model declaration.id key
    [] children instanceRule selected
  refine ⟨same.1,same.2.symm,?_,?_⟩
  · simpa only [same.1] using instanceRule
  · apply (evidence_leaf_iff registry state.context model root key).mpr
    simpa only [same.1] using instanceRule

/-- A compact, purely structural alternative to historical packet coverage. -/
def HasSpineLeaf (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ∃ declaration ∈ registry.declarations,
    DeclarationChecked registry.constructors roles declaration ∧ Nonempty (SpineLeafShape context root declaration)

/-- Directly usable in a mixed historical/structural coverage proof. The
selected key is derived, not included in HasSpineLeaf. -/
theorem selected_of_coverage (registry : Registry) (state : State roles) (root : Occurrence roles)
    (coverage : HasSpineLeaf registry state.context root)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model) :
    children = [] ∧ Instance registry state.context model root key [] ∧
      Evidence registry state.context model root (.node key []) := by
  obtain ⟨declaration,visible,checked,⟨shape⟩⟩ := coverage
  exact (selected_leaf registry state root declaration visible checked shape key children selected model valid).2

/-- The previously handled one-level finite nominal head is the zero-wrapper
case of the recursive source spine. -/
def ofLinearShape (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : GeneralDictionaryLinearLeaf.LinearLeafShape context root declaration) :
    SpineLeafShape context root declaration where
  terminal := shape.terminal
  outputs := shape.outputs
  role := shape.role
  slot := shape.slot
  arity := shape.arity
  names := shape.names
  distinct := shape.distinct
  inputs := shape.inputs
  bounds := shape.bounds
  spine := .leaf shape.slot shape.descriptor shape.recorded shape.parameters
  query := shape.query
  located := shape.located

theorem linear_covered (registry : Registry) (context : Context) (root : Occurrence roles)
    (covered : GeneralDictionaryLinearLeaf.HasLinearLeaf registry context root) :
    HasSpineLeaf registry context root := by
  obtain ⟨declaration,visible,checked,⟨shape⟩⟩ := covered
  exact ⟨declaration,visible,checked,⟨ofLinearShape context root declaration shape⟩⟩

/-- The earlier depth-two fragment embeds into the same recursive template. -/
def ofNestedShape (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : GeneralDictionaryNestedLeaf.NestedLeafShape context root declaration) :
    SpineLeafShape context root declaration where
  terminal := shape.terminal
  outputs := shape.outputs
  role := shape.role
  slot := shape.head.outer
  arity := shape.head.arity
  names := shape.head.names
  distinct := shape.head.distinct
  inputs := shape.head.inputs
  bounds := shape.head.bounds
  spine := .wrap shape.head.outer shape.head.inner shape.head.outerDescriptor shape.head.outerRecorded
    shape.head.outerParameters (.leaf shape.head.inner shape.head.innerDescriptor shape.head.innerRecorded shape.head.innerParameters)
  query := shape.head.query
  located := shape.located

theorem nested_covered (registry : Registry) (context : Context) (root : Occurrence roles)
    (covered : GeneralDictionaryNestedLeaf.HasNestedLeaf registry context root) :
    HasSpineLeaf registry context root := by
  obtain ⟨declaration,visible,checked,⟨shape⟩⟩ := covered
  exact ⟨declaration,visible,checked,⟨ofNestedShape context root declaration shape⟩⟩
end Yulang.GeneralDictionarySpineLeaf
