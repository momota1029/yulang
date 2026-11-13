import Yulang.GeneralDictionaryReachableRequestHistory
import Yulang.GeneralDictionarySelectedProvenanceCoverage

/-! Current-head structural evidence using membership in the actual finite
variable-free journal catalog. Reachability automatically supplies operational
request history. Coverage of all selected heads is still an explicit restriction. -/
namespace Yulang.GeneralDictionaryCatalogEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralNominalMaterialization
open GeneralDictionaryReachableRequestHistory (safeCatalog safe_history)
variable {roles : Roles.RoleDecls}

def Structural (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (checked : DeclarationChecked registry.constructors roles chosen) : Prop :=
  (∃ shape : GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry focus chosen checked,
    ∀ request ∈ requests state.current.context.state registry focus chosen checked
      (bindings state.current.context.state (report state.current.context chosen [(shape.slot,shape.slot)])),
      request ∈ safeCatalog state) ∨
  (∃ shape : GeneralDictionaryProvenanceScalarBranch.Shape state.current.context focus chosen,
    ∀ request ∈ requests state.current.context.state registry focus chosen checked
      (bindings state.current.context.state (report state.current.context chosen [(shape.slot,shape.slot)])),
      request ∈ safeCatalog state)

theorem structural {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    {focus chosen checked} (shape : Structural registry state focus chosen checked) :
    GeneralDictionaryProvenanceHeadBranch.Structural registry root state focus chosen checked := by
  rcases shape with ⟨shape,included⟩ | ⟨shape,included⟩
  · exact Or.inl ⟨shape,GeneralDictionaryCollectedRequests.supported_subset (safe_history reachable) _ included⟩
  · exact Or.inr ⟨shape,GeneralDictionaryCollectedRequests.supported_subset (safe_history reachable) _ included⟩

theorem node_evidence (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Structural registry state focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  GeneralDictionaryProvenanceHeadBranch.node_evidence registry root focus state reachable chosen visible checked
    (structural reachable shape) key children selected model valid dictionaries given

def Covered (registry : Registry) (root : Occurrence roles) (state : Tracked roles) : Prop :=
  ∀ focus, GeneralDictionarySelectionPolicy.SelectedPath
    (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus →
    ∀ key children, GeneralNominalValueBoundary.Local registry state focus (.selected key children) →
    ∃ chosen ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles chosen, Structural registry state focus chosen checked

theorem covered {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (coverage : Covered registry root state) :
    GeneralDictionarySelectedProvenanceCoverage.Covered registry root state := by
  intro focus path key children selected
  obtain ⟨chosen,visible,checked,shape⟩ := coverage focus path key children selected
  exact ⟨chosen,visible,checked,structural reachable shape⟩

/-- Conditional full recursive-payload soundness. The hypotheses are actual
reachability, current scalar/finite nominal shape, and finite catalog membership;
there is no assumed final Supported, semantic branch validity, or executor. -/
theorem dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (coverage : Covered registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  GeneralDictionarySelectedProvenanceCoverage.root_dictionary_evidence registry root state reachable
    (covered reachable coverage) model valid dictionary derived
end Yulang.GeneralDictionaryCatalogEvidence
