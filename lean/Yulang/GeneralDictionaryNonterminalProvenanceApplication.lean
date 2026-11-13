import Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification
import Yulang.GeneralDictionarySelectedProvenanceCoverage

/-! A genuinely recursive selected payload through the new provenance pipeline:
ternary nominal parent with named output and one scalar child. Neither current
Evidence nor branch-model validity is used to construct the coverage certificate. -/
namespace Yulang.GeneralDictionaryNonterminalProvenanceApplication
set_option backward.isDefEq.respectTransparency false
open GeneralDictionaryFiniteObservedExampleNonterminal
open GeneralDictionaryFiniteObservedExampleNonterminalInstallation
open GeneralDictionaryFiniteObservedExampleNonterminalEvidence
open GeneralDictionaryFiniteObservedExampleNonterminalClosure
open GeneralDictionaryFiniteObservedExampleNonterminalClassification
open GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence
open GeneralDictionaryFiniteObservedExample (descriptor interpretation constructors model)
open GeneralNominalExamples (intDisplay)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalSaturationState

noncomputable abbrev parent_tree : GeneralNominalTreeFacts.Tree current.state
    (n := 3) Fin.val (fun _ => ((1 : Fin 2),(1 : Fin 2))) (0 : Fin 2) :=
  GeneralNominalTreeFacts.Tree.leaf (state := current.state) (n := 3)
    Fin.val (fun _ => ((1 : Fin 2),(1 : Fin 2))) (0 : Fin 2) descriptor rfl
    (show descriptor.arguments = List.ofFn (fun _ : Fin 3 => GeneralNominalState.Parameter.type ((1 : Fin 2),1)) by simp [List.ofFn_succ])

noncomputable abbrev parent_shape : GeneralDictionaryHistoricalTreeBranch.Shape current registry root declaration checked where
  role := rfl
  slot := (0 : Fin 2)
  arity := 3
  names := Fin.val
  distinct := fun _ _ equal => Fin.ext equal
  inputs := by decide +kernel
  bounds := fun _ => ((1 : Fin 2),(1 : Fin 2))
  tree := parent_tree
  query := by
    change GeneralNominalInspection.queries source interpretation declaration = [parent_tree.query]
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,interpretation,constructors,
      GeneralNominalTreeFacts.Tree.query,List.ofFn_succ]
  located := rfl
  defined := shape.defined

noncomputable abbrev child_shape : GeneralDictionaryProvenanceScalarBranch.Shape current child intDisplay where
  role := rfl
  slot := (1 : Fin 2)
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    change GeneralNominalInspection.queries source interpretation intDisplay = [.scalar .int]
    exact leafShape.query
  located := by change arguments context child = some [(1,1)]; exact child_arguments
  defined := by intro output member; cases member

theorem parent_requests (capture : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests current.state registry root declaration checked capture =
      [GeneralDictionaryFiniteObservedExample.request] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by
    intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact ⟨rfl,by intro pattern member; have same := List.mem_singleton.mp member; subst pattern; exact ⟨0,rfl⟩⟩)]
  rfl

theorem parent_structural : GeneralDictionaryProvenanceHeadBranch.Structural registry root installed root declaration checked := by
  refine Or.inl ⟨parent_shape,?_⟩
  rw [parent_requests]
  apply GeneralDictionaryRequestProvenance.supported_of_observed registry root start installed
    ⟨start,⟨context,initial_source,rfl⟩,.refl⟩ (.tail .refl value_install_step)
  exact GeneralDictionaryFiniteObservedExample.observed

theorem child_requests (capture : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests current.state registry child intDisplay int_display_checked capture = [] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro clause member; cases member)]
  rfl

theorem child_structural : GeneralDictionaryProvenanceHeadBranch.Structural registry root installed child intDisplay int_display_checked := by
  refine Or.inr ⟨child_shape,?_⟩
  rw [child_requests]
  intro request member; cases member

private theorem two_node_path {v : B4Target.Vocabulary} {b : B4Target.SourceBoundary v}
    {r : v.Registry} {s : v.State} {origin leaf focus : v.Demand} {parentKey leafKey : Nat}
    (path : GeneralDictionarySelectionPolicy.SelectedPath b r s origin focus)
    (parentSelected : B4TargetV3.Local b r s origin (.selected parentKey [leaf]))
    (leafSelected : B4TargetV3.Local b r s leaf (.selected leafKey [])) :
    focus = origin ∨ focus = leaf := by
  induction path with
  | root => exact Or.inl rfl
  | @child parent key children child path selected member ih =>
    rcases ih with rfl | rfl
    · have same := B4TargetV3.local_functional parentSelected selected
      cases same
      exact Or.inr (List.mem_singleton.mp member)
    · have same := B4TargetV3.local_functional leafSelected selected
      cases same
      cases member

theorem selected_path_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (path : GeneralDictionarySelectionPolicy.SelectedPath
      (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry installed root focus) :
    focus = root ∨ focus = child := by
  have parent := (GeneralNominalValueBoundary.local_correspondence registry installed root _).mpr value_parent
  rw [children_exact] at parent
  exact two_node_path path parent
    ((GeneralNominalValueBoundary.local_correspondence registry installed child _).mpr value_child)

theorem covered : GeneralDictionarySelectedProvenanceCoverage.Covered registry root installed := by
  intro focus path key children selected
  rcases selected_path_cases focus path with rfl | rfl
  · exact ⟨declaration,by simp,checked,parent_structural⟩
  · exact ⟨intDisplay,by simp,int_display_checked,child_structural⟩

theorem classifier_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root payload :=
  GeneralDictionarySelectedProvenanceCoverage.root_dictionary_evidence registry root installed
    value_reachable covered assignment valid payload value_classified

theorem inhabited_recursive_application :
    Models installed.current model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry current model root payload ∧
    children.length = 1 ∧ root.demand.outputs ≠ [] :=
  ⟨models_of_source model source_models,classifier_evidence model (models_of_source model source_models),
    actual_children_count,named_request_present⟩
end Yulang.GeneralDictionaryNonterminalProvenanceApplication
