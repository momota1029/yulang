import Yulang.GeneralDictionaryCatalogEvidence
import Yulang.GeneralDictionaryMultiArgumentCoverage

/-! Arbitrary finite scalar-point heads consume actual collected histories or
finite journal catalogs, with no final Supported premise. The recursive result
retains current shape and selected-request coverage, not general evidenceNode. -/
namespace Yulang.GeneralDictionaryCatalogMultiArgumentEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralNominalMaterialization
open GeneralDictionaryReachableRequestHistory (safeCatalog safe_history)
open GeneralDictionaryMultiScalarInspection (Shape points)
variable {roles : Roles.RoleDecls}

theorem instance_of_history (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (batch : List Request) (history : GeneralDictionaryCollectedRequests.Collected registry root state batch)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (included : ∀ request ∈ requests state.current.context.state registry focus chosen checked
      (bindings state.current.context.state (report state.current.context chosen (points shape.entries))), request ∈ batch)
    (metadata : Metadata registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus chosen.id
      (GeneralNominalAllocation.children state.current.context.state registry focus chosen checked
        (bindings state.current.context.state (report state.current.context chosen (points shape.entries)))) :=
  GeneralDictionaryProvenanceMultiScalarBranch.instance_of_shape registry root focus state
    (GeneralDictionaryCollectedRequests.reachable history) chosen visible checked shape
    (GeneralDictionaryCollectedRequests.supported_subset history _ included) metadata model valid

theorem instance_of_catalog (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (included : ∀ request ∈ requests state.current.context.state registry focus chosen checked
      (bindings state.current.context.state (report state.current.context chosen (points shape.entries))),
      request ∈ safeCatalog state)
    (metadata : Metadata registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus chosen.id
      (GeneralNominalAllocation.children state.current.context.state registry focus chosen checked
        (bindings state.current.context.state (report state.current.context chosen (points shape.entries)))) :=
  instance_of_history registry root focus state _ (safe_history reachable) chosen visible checked shape
    included metadata model valid

def Structural (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (checked : DeclarationChecked registry.constructors roles chosen) : Prop :=
  GeneralDictionaryCatalogEvidence.Structural registry state focus chosen checked ∨
  ∃ shape : Shape state.current.context focus chosen,
    ∀ request ∈ requests state.current.context.state registry focus chosen checked
      (bindings state.current.context.state (report state.current.context chosen (points shape.entries))),
      request ∈ safeCatalog state

theorem structural {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    {focus chosen checked} (shape : Structural registry state focus chosen checked) :
    GeneralDictionaryMultiArgumentCoverage.Structural registry root state focus chosen checked := by
  rcases shape with old | ⟨shape,included⟩
  · exact Or.inl (GeneralDictionaryCatalogEvidence.structural reachable old)
  · exact Or.inr ⟨shape,GeneralDictionaryCollectedRequests.supported_subset (safe_history reachable) _ included⟩

def Covered (registry : Registry) (root : Occurrence roles) (state : Tracked roles) : Prop :=
  ∀ focus, GeneralDictionarySelectionPolicy.SelectedPath
    (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus →
    ∀ key children, GeneralNominalValueBoundary.Local registry state focus (.selected key children) →
    ∃ chosen ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles chosen, Structural registry state focus chosen checked

theorem covered {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (coverage : Covered registry root state) :
    GeneralDictionaryMultiArgumentCoverage.Covered registry root state := by
  intro focus path key children selected
  obtain ⟨chosen,visible,checked,shape⟩ := coverage focus path key children selected
  exact ⟨chosen,visible,checked,structural reachable shape⟩

theorem dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (coverage : Covered registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  GeneralDictionaryMultiArgumentCoverage.root_dictionary_evidence registry root state reachable
    (covered reachable coverage) model valid dictionary derived
end Yulang.GeneralDictionaryCatalogMultiArgumentEvidence
