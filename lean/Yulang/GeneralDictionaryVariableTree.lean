import Yulang.GeneralDictionaryVariableRequirements

/-! Nonterminal, variable-only where obligations under arbitrary finite binary tree heads.
Source branch validity is independent of child classification; emitted children are retained. -/
namespace Yulang.GeneralDictionaryVariableTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralDictionaryRecursiveEvidence

/-- Syntax/state witnesses only: no BranchModels, Instance, Evidence, packet,
Joint, Installable, or assumption about a successful selected declaration. -/
structure TreeBranchShape (context : Context) (root : Occurrence roles)
    (declaration : Declaration) where
  variables : GeneralDictionaryVariableRequirements.VariableClauses declaration
  outputs : root.demand.outputs = []
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

theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : TreeBranchShape context root declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.slot,shape.slot)] model := by
  have privateValid := GeneralNominalTreeFacts.private_models context registry root declaration shape.names shape.distinct shape.inputs shape.bounds shape.tree shape.query model valid
  refine ⟨privateValid.1,privateValid.2,?_⟩
  rw [GeneralDictionaryVariableRequirements.generated_empty context registry root declaration checked _ shape.outputs shape.variables]
  exact GeneralNominalMaterialization.empty_models ..

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : TreeBranchShape context root declaration) :
    RequestReady registry context root declaration checked [(shape.slot,shape.slot)] := by
  constructor
  · intro output member
    rw [shape.outputs] at member
    cases member
  · rw [GeneralDictionaryVariableRequirements.generated_empty context registry root declaration checked _ shape.outputs shape.variables]

/-- A semantic instance is constructed independently of selected key/children,
using only current metadata and a structural variable-requirement tree witness. -/
theorem instance_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : TreeBranchShape context root declaration)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id
      (GeneralNominalAllocation.children context.state registry root declaration checked
        (bindings context.state (report context declaration [(shape.slot,shape.slot)]))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,?_,?_,metadata,?_⟩
  · rw [GeneralNominalTreeFacts.report_exact context declaration shape.tree shape.query]
    exact GeneralNominalTreeFacts.tree_finished context.state shape.tree none
  · exact ready context registry root declaration checked shape
  · rfl
  · exact branch_models context registry root declaration checked shape model valid


/-- Selection fixes the independently constructed instance's actual child list.
No stability, recorded packet, or Joint premise is used. -/
theorem selected_instance (registry : Registry) (state : State roles)
    (root : Occurrence roles) (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : TreeBranchShape state.context root declaration)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model) :
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

def HasVariableTree (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ∃ declaration ∈ registry.declarations,
    DeclarationChecked registry.constructors roles declaration ∧ Nonempty (TreeBranchShape context root declaration)

theorem selected_of_coverage (registry : Registry) (state : State roles)
    (root : Occurrence roles) (coverage : HasVariableTree registry state.context root)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model) :
    Instance registry state.context model root key children := by
  obtain ⟨declaration,visible,checked,⟨shape⟩⟩ := coverage
  exact (selected_instance registry state root declaration visible checked shape key children selected model valid).2

/-- The actual selected children need their own evidence, in the same model.
In particular nonempty where requirements are not erased or assumed successful. -/
theorem selected_evidence (registry : Registry) (state : State roles)
    (root : Occurrence roles) (coverage : HasVariableTree registry state.context root)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.context model) children dictionaries) :
    Evidence registry state.context model root (.node key dictionaries) :=
  evidence_node registry state.context model root key children dictionaries
    (selected_of_coverage registry state root coverage key children selected model valid) given

end Yulang.GeneralDictionaryVariableTree
