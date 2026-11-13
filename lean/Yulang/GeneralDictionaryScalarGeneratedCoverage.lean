import Yulang.GeneralDictionaryScalarRegistryIntervals
import Yulang.GeneralDictionaryRequestCatalog
import Yulang.GeneralDictionarySelectedProvenanceCoverage
import Yulang.GeneralDictionaryProvenanceMultiScalarBranch
import Yulang.GeneralDictionaryProvenanceHeadBranch
import Yulang.GeneralDictionaryProvenanceClassification
import Yulang.GeneralDictionaryProvenanceTreeBranch
import Yulang.GeneralDictionaryCoveredEvidence
import Yulang.GeneralDictionarySelectionPolicy

/-! Conditional soundness of the actual Value classifier's entire recursive
payload. Coverage is syntax and operational request provenance only for the selected
source descendants of the root, not evidence or all-model branch validity. Deriving this coverage for
arbitrary reachable states remains open. -/
namespace Yulang.GeneralDictionaryScalarGeneratedCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
variable {roles : Roles.RoleDecls}

/-- Current scalar intervals at an actual graph-generated focus, with finite syntactic request membership. No endpoint ordering or Instance premise. -/
def Structural (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (focus : Occurrence roles) (chosen : Declaration)
    (checked : DeclarationChecked registry.constructors roles chosen) : Prop :=
  Generated state.current root focus ∧
  ∃ shape : GeneralDictionaryScalarIntervalInspection.Shape state.current.context focus chosen,
    ∀ request ∈ GeneralNominalMaterialization.requests state.current.context.state registry focus chosen checked
      (bindings state.current.context.state (report state.current.context chosen
        (GeneralDictionaryScalarIntervalInspection.intervals shape.entries))),
      request ∈ GeneralDictionaryRequestCatalog.catalog state

theorem selected_instance (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (fragment : GeneralDictionaryScalarRegistryIntervals.ScalarVariableRegistry registry state.current.context.interpretation)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (structural : Structural registry root state focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  obtain ⟨generated,shape,included⟩ := structural
  exact GeneralDictionaryScalarRegistryIntervals.selected_instance registry root focus state fragment reachable
    generated chosen visible checked shape
    (GeneralDictionaryRequestCatalog.supported registry root state _ included) key children selected model valid

def Covered (registry : Registry) (root : Occurrence roles) (state : Tracked roles) : Prop :=
  ∀ focus, GeneralDictionarySelectionPolicy.SelectedPath
    (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state root focus →
    ∀ key children, GeneralNominalValueBoundary.Local registry state focus (.selected key children) →
    ∃ chosen ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles chosen,
        Structural registry root state focus chosen checked

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
      (fragment : GeneralDictionaryScalarRegistryIntervals.ScalarVariableRegistry registry state.current.context.interpretation)
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
      exact evidence_node registry state.current.context model focus key children dictionaries
        (selected_instance registry root focus state fragment reachable chosen visible checked structural key children selected model valid)
        (dictionaries_evidence registry root state fragment reachable covered model valid dictionaries children
          (fun child member => .child path (.selected safe unique) member) classified)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
      (fragment : GeneralDictionaryScalarRegistryIntervals.ScalarVariableRegistry registry state.current.context.interpretation)
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
      exact .cons (dictionary_evidence registry root state fragment reachable covered model valid _ _ (paths _ List.mem_cons_self) first)
        (dictionaries_evidence registry root state fragment reachable covered model valid _ _
          (fun focus member => paths focus (List.mem_cons_of_mem _ member)) rest)
  termination_by sizeOf dictionaries
end
/-- Root soundness uses only the actual selected source tree; unrelated demands
in the same state need no shape/provenance certificate. -/
theorem root_dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (fragment : GeneralDictionaryScalarRegistryIntervals.ScalarVariableRegistry registry state.current.context.interpretation)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (covered : Covered registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  dictionary_evidence registry root state fragment reachable covered model valid dictionary root .root derived

/-- A completed actual diagnostic tree yields current dictionary evidence.
This does not assume an executor is exact or prove that it returns this tree. -/
theorem completed_tree_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (fragment : GeneralDictionaryScalarRegistryIntervals.ScalarVariableRegistry registry state.current.context.interpretation)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (covered : Covered registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (tree : CommonRoleOutermostResolver.Tree)
    (resolved : CommonRoleOutermostResolver.Resolves
      (B4TargetV3.Local (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state) root tree)
    (dictionary : GeneralDictionaryReadback.Payload)
    (completed : B4TargetV3.Completed tree (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  root_dictionary_evidence registry root state fragment reachable covered model valid dictionary
    (B4TargetV3.tree_classifies (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry state tree root _ resolved completed)

end Yulang.GeneralDictionaryScalarGeneratedCoverage
