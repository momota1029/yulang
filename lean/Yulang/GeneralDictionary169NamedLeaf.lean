import Yulang.GeneralDictionaryScalarLeaf
import Yulang.GeneralDictionaryFiniteObservedExample

namespace Yulang.GeneralDictionary169NamedLeaf
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralDictionaryRecursiveEvidence

structure LeafShape (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) where
  terminal : declaration.requirements = []
  role : declaration.role = root.demand.role
  slot : Fin context.state.base.slots
  base : Inference.Base
  noNominal : context.state.nominals slot = none
  head : context.state.view.heads slot = .scalar base
  inputs : declaration.inputNames = []
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [.scalar base]
  located : arguments context root = some [(slot,slot)]
  defined : GeneralNominalMaterialization.RootDefined declaration root
  observed : GeneralDictionaryObservedFiniteRequests.Observed context.state context.interpretation
    (GeneralNominalMaterialization.requests context.state registry root declaration checked
      (bindings context.state (report context declaration [(slot,slot)])))

theorem report_exact (context : Context) (root : Occurrence roles) (declaration : Declaration)
    {registry : Registry} {checked : DeclarationChecked registry.constructors roles declaration}
    (shape : LeafShape registry context root declaration checked) :
    report context declaration [(shape.slot,shape.slot)] =
      { inspected := [(shape.slot,shape.slot)], checked := [(shape.slot,shape.slot),(shape.slot,shape.slot)] } := by
  simp [report,shape.query,inspectMany,inspect,shape.noNominal,shape.head,Report.visit,Report.append]

theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : LeafShape registry context root declaration checked)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.slot,shape.slot)] model := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact context root declaration shape]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,shape.inputs]
    · simp [selfChecks,PresenceNormalForm.All]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [report_exact context root declaration shape]
    simp [ProjectionModels]
  · exact GeneralDictionaryObservedFiniteRequests.generated_models context.state context.interpretation _
      shape.observed declaration _ _ model valid

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : LeafShape registry context root declaration checked) :
    RequestReady registry context root declaration checked [(shape.slot,shape.slot)] := by
  exact ⟨shape.defined,(GeneralDictionaryObservedFiniteRequests.generated_shape context.state
    context.interpretation _ shape.observed).2⟩

/-- A semantic instance is constructed independently of selected key/children,
using only current metadata and a structural leaf witness. -/
theorem instance_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : LeafShape registry context root declaration checked)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id [] := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,?_,?_,metadata,?_⟩
  · rw [report_exact context root declaration shape]
    exact ⟨rfl,rfl,rfl⟩
  · exact ready context registry root declaration checked shape
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked shape.terminal _).symm
  · exact branch_models context registry root declaration checked shape model valid


theorem evidence_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : LeafShape registry context root declaration checked)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Evidence registry context model root (.node declaration.id []) :=
  (evidence_leaf_iff registry context model root declaration.id).mpr
    (instance_of_shape context registry root declaration visible checked shape metadata model valid)

open GeneralDictionaryFiniteObservedExample in
def actual_shape : LeafShape registry context root declaration checked where
  terminal := rfl
  role := rfl
  slot := ⟨1,by decide⟩
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,interpretation,GeneralNominalExamples.interpretation]
  located := by decide +kernel
  defined := by
    intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨equation,List.mem_singleton_self _,rfl⟩
  observed := by
    rw [actual_requests_exact]
    exact observed

open GeneralDictionaryFiniteObservedExample in
theorem actual_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Evidence registry context assignment root (.node declaration.id []) :=
  evidence_of_shape context registry root declaration (by simp) checked actual_shape metadata assignment valid

open GeneralDictionaryFiniteObservedExample in
theorem actual_nonempty_output :
    Nonempty (LeafShape registry context root declaration checked) ∧ root.demand.outputs ≠ [] ∧
    ∃ assignment, GeneralNominalState.Models state assignment ∧
      Evidence registry context assignment root (.node declaration.id []) :=
  ⟨⟨actual_shape⟩,named_request_present,model,state_models,actual_evidence model state_models⟩

end Yulang.GeneralDictionary169NamedLeaf
