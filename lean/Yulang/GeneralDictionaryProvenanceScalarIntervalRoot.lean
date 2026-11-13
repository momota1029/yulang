import Yulang.GeneralDictionaryScalarIntervalInspection

/-! Arbitrary finite scalar interval arguments at the ORIGINAL reachable root.
Endpoint inequalities come from initial formation and actual model preservation,
not a new all-model premise. Child occurrences are not covered by this module. -/
namespace Yulang.GeneralDictionaryProvenanceScalarIntervalRoot
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralDictionaryScalarIntervalInspection

theorem branch_models (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry root state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (intervals shape.entries)))))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchModels registry state.current.context root declaration checked (intervals shape.entries) model := by
  have current := private_models registry state.current.context root declaration shape model valid.1
    (GeneralDictionaryReachableRootIntervals.located_intervals registry root state reachable _ shape.located model valid)
  exact ⟨current.1,current.2,GeneralDictionaryRequestProvenance.models registry root state
    reachable _ supported declaration _ _ model valid⟩

theorem instance_of_shape (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry root state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (intervals shape.entries)))))
    (metadata : Metadata registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model root declaration.id
      (GeneralNominalAllocation.children state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (intervals shape.entries)))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,(intervals shape.entries),shape.located,?_,?_,rfl,metadata,
    branch_models registry root state reachable declaration checked shape supported model valid⟩
  · rw [report_exact state.current.context root declaration shape]; exact ⟨rfl,rfl,rfl⟩
  · exact ⟨shape.defined,(GeneralDictionaryRequestProvenance.shape registry root state reachable _ supported).2⟩

theorem selected_instance (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry root state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration (intervals shape.entries)))))
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
  have rule := instance_of_shape registry root state reachable declaration visible checked shape supported metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry state.current root model declaration.id key _ children rule old
  simpa only [same.1,same.2] using rule
end Yulang.GeneralDictionaryProvenanceScalarIntervalRoot
