import Yulang.GeneralDictionaryMultiScalarInspection

/-! Current scalar heads of arbitrary finite arity, with potentially nonempty
where/named-output requests. Shape is checked source syntax; provenance follows
actual operations. No arbitrary nonpoint or variable-capture theorem is claimed. -/
namespace Yulang.GeneralDictionaryProvenanceMultiScalarBranch
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralDictionaryMultiScalarInspection

theorem branch_models (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (points shape.entries)))))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchModels registry state.current.context root declaration checked (points shape.entries) model := by
  have current := private_models registry state.current.context root declaration shape model valid.1
  exact ⟨current.1,current.2,GeneralDictionaryRequestProvenance.models registry saturationRoot state
    reachable _ supported declaration _ _ model valid⟩

theorem instance_of_shape (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (points shape.entries)))))
    (metadata : Metadata registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model root declaration.id
      (GeneralNominalAllocation.children state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (points shape.entries)))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,(points shape.entries),shape.located,?_,?_,rfl,metadata,
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
        (bindings state.current.context.state (report state.current.context declaration (points shape.entries)))))
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
end Yulang.GeneralDictionaryProvenanceMultiScalarBranch
