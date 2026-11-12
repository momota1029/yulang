import Yulang.GeneralNominalNestedLinearFacts
import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! Structural depth-two nominal leaves need no recorded packet. Their complete branch
is valid at every current source model, before comparing against selection. -/
namespace Yulang.GeneralDictionaryNestedLeaf
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralDictionaryRecursiveEvidence

/-- Syntax/state witnesses only: no BranchModels, Instance, Evidence, packet,
Joint, Installable, or assumption about a successful selected declaration. -/
structure NestedLeafShape (context : Context) (root : Occurrence roles)
    (declaration : Declaration) where
  terminal : declaration.requirements = []
  outputs : root.demand.outputs = []
  role : declaration.role = root.demand.role
  head : GeneralNominalNestedLinearFacts.NestedShape context declaration
  located : arguments context root = some [(head.outer,head.outer)]

theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : NestedLeafShape context root declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.head.outer,shape.head.outer)] model := by
  have privateValid := GeneralNominalNestedLinearFacts.private_models context registry root declaration shape.head model valid
  refine ⟨privateValid.1,privateValid.2,?_⟩
  rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked shape.terminal shape.outputs]
  exact GeneralNominalMaterialization.empty_models ..

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : NestedLeafShape context root declaration) :
    RequestReady registry context root declaration checked [(shape.head.outer,shape.head.outer)] := by
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
    (shape : NestedLeafShape context root declaration)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id [] := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.head.outer,shape.head.outer)],shape.located,?_,?_,?_,metadata,?_⟩
  · rw [GeneralNominalNestedLinearFacts.report_exact context declaration shape.head]
    exact ⟨rfl,rfl,rfl⟩
  · exact ready context registry root declaration checked shape
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked shape.terminal _).symm
  · exact branch_models context registry root declaration checked shape model valid

/-- An unrecorded leaf can identify the current selected declaration by actual
uniqueness. No assumption equates its source declaration ID with the selected key. -/
theorem selected_leaf (registry : Registry) (state : State roles) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : NestedLeafShape state.context root declaration)
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
def HasNestedLeaf (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ∃ declaration ∈ registry.declarations,
    DeclarationChecked registry.constructors roles declaration ∧ Nonempty (NestedLeafShape context root declaration)

/-- Directly usable in a mixed historical/structural coverage proof. The
selected key is derived, not included in HasNestedLeaf. -/
theorem selected_of_coverage (registry : Registry) (state : State roles) (root : Occurrence roles)
    (coverage : HasNestedLeaf registry state.context root)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model) :
    children = [] ∧ Instance registry state.context model root key [] ∧
      Evidence registry state.context model root (.node key []) := by
  obtain ⟨declaration,visible,checked,⟨shape⟩⟩ := coverage
  exact (selected_leaf registry state root declaration visible checked shape key children selected model valid).2
end Yulang.GeneralDictionaryNestedLeaf
