import Yulang.GeneralDictionaryReservedInstalledClassification
import Yulang.GeneralDictionaryReservedMixedProvenance
import Yulang.GeneralDictionarySelectedProvenanceCoverage

/-! Actual selected-payload soundness through the structural/provenance pipeline.
The selected source tree is a leaf. Coverage is derived, not postulated globally;
this does not assert saturation stability or an exact executing algorithm. -/
namespace Yulang.GeneralDictionaryReservedClassifierSoundness
set_option backward.isDefEq.respectTransparency false
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration checked equation interpretation)
open GeneralDictionaryReservedInstalledClassification
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralDeclarationExamples (roles)

noncomputable abbrev scalar_shape :
    GeneralDictionaryProvenanceScalarBranch.Shape current root declaration := by
  refine ⟨rfl,(1 : Fin 2),.int,rfl,rfl,rfl,?_,by decide +kernel,?_⟩
  · change GeneralNominalInspection.queries state interpretation declaration = [.scalar .int]
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,interpretation,GeneralNominalExamples.interpretation]
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨equation,List.mem_singleton_self _,rfl⟩

theorem current_requests_exact (capture : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests current.state registry root declaration checked capture = [request] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by
    intro clause member; cases member)]
  rfl

theorem structural : GeneralDictionaryProvenanceHeadBranch.Structural registry root installed
    root declaration checked := by
  refine Or.inr ⟨scalar_shape,?_⟩
  rw [current_requests_exact]
  exact GeneralDictionaryRequestProvenance.supported_of_recorded registry root installed [request]
    GeneralDictionaryReservedMixedProvenance.reserved_covered

private theorem leaf_path {v : B4Target.Vocabulary} {b : B4Target.SourceBoundary v}
    {r : v.Registry} {s : v.State} {origin focus : v.Demand} {key : Nat}
    (path : GeneralDictionarySelectionPolicy.SelectedPath b r s origin focus)
    (chosen : B4TargetV3.Local b r s origin (.selected key [])) : focus = origin := by
  induction path with
  | root => rfl
  | @child parent key children child path selected member ih =>
    have sameParent := ih
    subst parent
    have same := B4TargetV3.local_functional chosen selected
    cases same
    cases member

theorem selected_path_root (focus : GeneralSourceDictionaries.Occurrence roles)
    (path : GeneralDictionarySelectionPolicy.SelectedPath
      (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry installed root focus) :
    focus = root :=
  leaf_path path ((GeneralNominalValueBoundary.local_correspondence registry installed root _).mpr value_selected)

theorem covered : GeneralDictionarySelectedProvenanceCoverage.Covered registry root installed := by
  intro focus path key children selected
  have same := selected_path_root focus path
  subst focus
  exact ⟨declaration,by simp,checked,structural⟩

theorem classifier_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root (.node declaration.id []) :=
  GeneralDictionarySelectedProvenanceCoverage.root_dictionary_evidence registry root installed
    value_reachable covered assignment valid (.node declaration.id []) classified

theorem inhabited_classifier_evidence :
    GeneralDictionaryRecursiveEvidence.Evidence registry current positive root (.node declaration.id []) ∧
    ¬ GeneralNominalValueSteps.Stable registry installed root :=
  ⟨classifier_evidence positive installed_models,GeneralDictionaryReservedEqualityStep.installed_not_stable⟩
end Yulang.GeneralDictionaryReservedClassifierSoundness
