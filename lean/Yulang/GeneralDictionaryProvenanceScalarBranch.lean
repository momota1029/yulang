import Yulang.GeneralDictionaryRequestProvenance
import Yulang.GeneralDictionaryScalarLeaf

/-! Scalar current heads with arbitrary variable-free materialization requests
supported by actual history. Unlike ScalarLeafShape, this certificate imposes
neither empty named outputs nor terminal declaration syntax. -/
namespace Yulang.GeneralDictionaryProvenanceScalarBranch
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence

structure Shape (context : Context) (root : Occurrence roles) (declaration : Declaration) where
  role : declaration.role = root.demand.role
  slot : Fin context.state.base.slots
  base : Inference.Base
  noNominal : context.state.nominals slot = none
  head : context.state.view.heads slot = .scalar base
  inputs : declaration.inputNames = []
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [.scalar base]
  located : arguments context root = some [(slot,slot)]
  defined : GeneralNominalMaterialization.RootDefined declaration root

theorem report_exact (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context root declaration) :
    report context declaration [(shape.slot,shape.slot)] =
      { inspected := [(shape.slot,shape.slot)], checked := [(shape.slot,shape.slot),(shape.slot,shape.slot)] } := by
  simp [report,shape.query,inspectMany,inspect,shape.noNominal,shape.head,Report.visit,Report.append]

theorem branch_models (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchModels registry state.current.context root declaration checked [(shape.slot,shape.slot)] model := by
  refine ⟨?_,?_,GeneralDictionaryRequestProvenance.models registry saturationRoot state reachable _ supported declaration _ _ model valid⟩
  · unfold privateState
    rw [report_exact state.current.context root declaration shape]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid.1,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,shape.inputs]
    · simp [selfChecks,PresenceNormalForm.All]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [report_exact state.current.context root declaration shape]
    simp [ProjectionModels]

theorem instance_of_shape (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (metadata : Metadata registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model root declaration.id
      (GeneralNominalAllocation.children state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,?_,rfl,metadata,
    branch_models registry saturationRoot root state reachable declaration checked shape supported model valid⟩
  · rw [report_exact state.current.context root declaration shape]; exact ⟨rfl,rfl,rfl⟩
  · exact ⟨shape.defined,(GeneralDictionaryRequestProvenance.shape registry saturationRoot state reachable _ supported).2⟩

theorem selected_instance (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model root key children := by
  have old := GeneralNominalValueBoundary.selected_old selected
  have metadata : Metadata registry state.current.context := by
    cases old with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have rule := instance_of_shape registry saturationRoot root state reachable declaration visible checked shape supported metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry state.current root model declaration.id key _ children rule old
  simpa only [same.1,same.2] using rule
end Yulang.GeneralDictionaryProvenanceScalarBranch
