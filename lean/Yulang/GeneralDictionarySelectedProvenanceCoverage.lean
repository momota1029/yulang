import Yulang.GeneralDictionaryProvenanceHeadBranch
import Yulang.GeneralDictionaryProvenanceClassification
import Yulang.GeneralDictionaryProvenanceTreeBranch
import Yulang.GeneralDictionaryCoveredEvidence
import Yulang.GeneralDictionarySelectionPolicy

/-! Conditional soundness of the actual Value classifier's entire recursive
payload. Coverage is syntax and operational request provenance only for the selected
source descendants of the root, not evidence or all-model branch validity. Deriving this coverage for
arbitrary reachable states remains open. -/
namespace Yulang.GeneralDictionarySelectedProvenanceCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
variable {roles : Roles.RoleDecls}

def Covered (registry : Registry) (root : Occurrence roles) (state : Tracked roles) : Prop :=
  ∀ focus, GeneralDictionarySelectionPolicy.SelectedPath
    (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus →
    ∀ key children, GeneralNominalValueBoundary.Local registry state focus (.selected key children) →
    ∃ chosen ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles chosen,
        GeneralDictionaryProvenanceHeadBranch.Structural registry root state focus chosen checked

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
      (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
      (covered : Covered registry root state)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionary : GeneralDictionaryReadback.Payload) (focus : Occurrence roles)
      (path : GeneralDictionarySelectionPolicy.SelectedPath
        (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus)
      (derived : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
        registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,safe,unique,classified⟩ :=
        GeneralDictionaryCoveredEvidence.classify_node_parts (v := GeneralNominalValueBoundary.vocabulary roles)
          (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state focus key dictionaries derived
      have selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children) :=
        (GeneralNominalValueBoundary.local_correspondence registry state focus _).mp
          (B4TargetV3.Local.selected safe unique)
      obtain ⟨chosen,visible,checked,structural⟩ := covered focus path key children selected
      exact GeneralDictionaryProvenanceHeadBranch.node_evidence registry root focus state reachable
        chosen visible checked structural key children selected model valid dictionaries
        (dictionaries_evidence registry root state reachable covered model valid dictionaries children
          (fun child member => .child path (.selected safe unique) member) classified)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
      (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
      (covered : Covered registry root state)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionaries : List GeneralDictionaryReadback.Payload) (focuses : List (Occurrence roles))
      (paths : ∀ focus ∈ focuses, GeneralDictionarySelectionPolicy.SelectedPath
        (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
          registry state focus (.selected dictionary)) focuses dictionaries) :
      All₂ (Evidence registry state.current.context model) focuses dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root state reachable covered model valid _ _ (paths _ List.mem_cons_self) first)
        (dictionaries_evidence registry root state reachable covered model valid _ _
          (fun focus member => paths focus (List.mem_cons_of_mem _ member)) rest)
  termination_by sizeOf dictionaries
end
/-- Root soundness uses only the actual selected source tree; unrelated demands
in the same state need no shape/provenance certificate. -/
theorem root_dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (covered : Covered registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  dictionary_evidence registry root state reachable covered model valid dictionary root .root derived

/-- A completed actual diagnostic tree yields current dictionary evidence.
This does not assume an executor is exact or prove that it returns this tree. -/
theorem completed_tree_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (covered : Covered registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (tree : CommonRoleOutermostResolver.Tree)
    (resolved : CommonRoleOutermostResolver.Resolves
      (B4TargetV3.Local (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state) root tree)
    (dictionary : GeneralDictionaryReadback.Payload)
    (completed : B4TargetV3.Completed tree (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  root_dictionary_evidence registry root state reachable covered model valid dictionary
    (B4TargetV3.tree_classifies (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry state tree root _ resolved completed)

/-- The prior global coverage condition implies selected-descendant coverage. -/
theorem covered_of_global (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (covered : GeneralDictionaryProvenanceClassification.Covered registry root state) :
    Covered registry root state := by
  intro focus _path key children selected
  obtain ⟨chosen,visible,checked,shape,provenance⟩ := covered focus key children selected
  exact ⟨chosen,visible,checked,Or.inl ⟨shape,provenance⟩⟩

end Yulang.GeneralDictionarySelectedProvenanceCoverage
