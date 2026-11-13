import Yulang.GeneralDictionaryProvenanceScalarIntervalRoot
import Yulang.GeneralDictionaryReachableRequestHistory

/-! Original-root scalar interval evidence using the actual finite variable-free
journal catalog. Catalog coverage and current scalar Shape remain explicit;
no final operational Supported premise or branch-validity hypothesis is supplied. -/
namespace Yulang.GeneralDictionaryCatalogScalarIntervalRoot
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralDictionaryScalarIntervalInspection
open GeneralDictionaryReachableRequestHistory (safeCatalog safe_history)

theorem selected_instance (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.current.context root declaration)
    (included : ∀ request ∈ GeneralNominalMaterialization.requests state.current.context.state
      registry root declaration checked
      (bindings state.current.context.state (report state.current.context declaration (intervals shape.entries))),
      request ∈ safeCatalog state)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    Instance registry state.current.context model root key children :=
  GeneralDictionaryProvenanceScalarIntervalRoot.selected_instance registry root state reachable
    declaration visible checked shape
    (GeneralDictionaryCollectedRequests.supported_subset (safe_history reachable) _ included)
    key children selected model valid
end Yulang.GeneralDictionaryCatalogScalarIntervalRoot
