import Yulang.GeneralDictionaryRequestProvenance
import Yulang.GeneralDictionaryHistoricalTreeBranch

/-! Current finite-tree heads with output requests distributed across the actual
history. Requests may mix actual earlier observations and packet coverage;
Joint, initial output observation, and current output slots are not premises. -/
namespace Yulang.GeneralDictionaryProvenanceTreeBranch
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence
open GeneralDictionaryHistoricalTreeBranch (Shape)

/-- All-model branch validity from current head structure and distributed recorded
request coverage. No current output-observation certificate is required. -/
theorem branch_models (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context registry root declaration checked)
    (covered : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    BranchModels registry state.current.context root declaration checked [(shape.slot,shape.slot)] model := by
  have privateValid := GeneralNominalTreeFacts.private_models state.current.context registry root declaration
    shape.names shape.distinct shape.inputs shape.bounds shape.tree shape.query model valid.1
  exact ⟨privateValid.1,privateValid.2,
    GeneralDictionaryRequestProvenance.models registry saturationRoot state
      reachable _ covered declaration _ _ model valid⟩

theorem ready (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context registry root declaration checked)
    (covered : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)])))) :
    RequestReady registry state.current.context root declaration checked [(shape.slot,shape.slot)] :=
  ⟨shape.defined,(GeneralDictionaryRequestProvenance.shape
    registry saturationRoot state reachable _ covered).2⟩

theorem instance_of_shape (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context registry root declaration checked)
    (covered : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (metadata : Metadata registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    Instance registry state.current.context model root declaration.id
      (GeneralNominalAllocation.children state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,
    ready registry saturationRoot root state reachable declaration checked shape covered,rfl,metadata,
    branch_models registry saturationRoot root state reachable declaration checked shape covered model valid⟩
  rw [GeneralNominalTreeFacts.report_exact state.current.context declaration shape.tree shape.query]
  exact GeneralNominalTreeFacts.tree_finished state.current.context.state shape.tree none

/-- Selected key and child identities come from the actual current judgment;
output materialization is supplied by per-request operational provenance. -/
theorem selected_instance (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context registry root declaration checked)
    (covered : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state.current root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    declaration.id = key ∧ Instance registry state.current.context model root key children := by
  have metadata : Metadata registry state.current.context := by
    cases selected with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have rule := instance_of_shape registry saturationRoot root state reachable declaration visible checked
    shape covered metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry state.current root model declaration.id key
    _ children rule selected
  exact ⟨same.1,by simpa only [same.1,same.2] using rule⟩

/-- The same final model satisfies the actual branch used by alias Joint.
Current output syntax is not an extra assumption. -/
theorem selected_branch (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context registry root declaration checked)
    (covered : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state.current root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    declaration.id = key ∧ GeneralNominalJointCandidates.BranchAt registry state.current root declaration.id model := by
  have rule := selected_instance registry saturationRoot root state reachable declaration visible checked
    shape covered key children selected model valid
  have survivor : Survivor registry state.current.context root key children := by
    cases selected with | selected _ unique => exact unique.1
  exact ⟨rule.1,rule.1.symm ▸ GeneralNominalStructuralSelectedGraph.branchAt_of_instance
    registry state.current root key children survivor model rule.2⟩


theorem value_node_evidence (registry : Registry) (saturationRoot root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry saturationRoot state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context registry root declaration checked)
    (covered : GeneralDictionaryRequestProvenance.Supported registry saturationRoot state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (bindings state.current.context.state (report state.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model root (.node key dictionaries) := by
  have rule := selected_instance registry saturationRoot root state reachable
    declaration visible checked shape covered key children
    (GeneralNominalValueBoundary.selected_old selected) model valid
  exact evidence_node registry state.current.context model root key children dictionaries rule.2 given

end Yulang.GeneralDictionaryProvenanceTreeBranch
