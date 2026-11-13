import Yulang.GeneralDictionaryProvenanceScalarBranch
import Yulang.GeneralDictionaryProvenanceTreeBranch

/-! A structural union of finite nominal-tree and scalar current heads. Both
alternatives retain their exact syntax restrictions and request provenance. -/
namespace Yulang.GeneralDictionaryProvenanceHeadBranch
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

def Structural (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (focus : Occurrence roles) (chosen : Declaration)
    (checked : DeclarationChecked registry.constructors roles chosen) : Prop :=
  (∃ shape : GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry focus chosen checked,
    GeneralDictionaryRequestProvenance.Supported registry root state
      (GeneralNominalMaterialization.requests state.current.context.state registry focus chosen checked
        (bindings state.current.context.state (report state.current.context chosen [(shape.slot,shape.slot)])))) ∨
  (∃ shape : GeneralDictionaryProvenanceScalarBranch.Shape state.current.context focus chosen,
    GeneralDictionaryRequestProvenance.Supported registry root state
      (GeneralNominalMaterialization.requests state.current.context.state registry focus chosen checked
        (bindings state.current.context.state (report state.current.context chosen [(shape.slot,shape.slot)]))))

theorem selected_instance (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (structural : Structural registry root state focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  rcases structural with ⟨shape,provenance⟩ | ⟨shape,provenance⟩
  · exact (GeneralDictionaryProvenanceTreeBranch.selected_instance registry root focus state reachable
      chosen visible checked shape provenance key children (GeneralNominalValueBoundary.selected_old selected) model valid).2
  · exact GeneralDictionaryProvenanceScalarBranch.selected_instance registry root focus state reachable
      chosen visible checked shape provenance key children selected model valid

theorem node_evidence (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (structural : Structural registry root state focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node registry state.current.context model focus key children dictionaries
    (selected_instance registry root focus state reachable chosen visible checked structural key children selected model valid) given
end Yulang.GeneralDictionaryProvenanceHeadBranch
