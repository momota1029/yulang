import Yulang.GeneralDictionaryUnrecordedAliasLeafJoint
import Yulang.GeneralDictionaryFiniteJournalJointExample

/-! A genuine reachable, inhabited, stable focus with no journal packet meets
our independent structural Joint criterion. No raw-state example is used. -/
namespace Yulang.GeneralDictionaryUnrecordedAliasLeafExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState GeneralNominalJointCandidates
open GeneralDeclarationExamples (roles)

noncomputable def shape : GeneralDictionaryScalarLeaf.ScalarLeafShape
    finish.current.context displayChild intDisplay where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := ⟨1,by decide +kernel⟩
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      ]
    change GeneralNominalInspection.translate GeneralDeclarationExamples.constructors interpretation
      (.app 2 []) = .scalar .int
    simp [GeneralNominalInspection.translate,interpretation]
  located := rfl

theorem child_locality (site : GeneralNominalDemandMerging.Site roles)
    (related : Related finish.current displayChild site) : site.occurrence = displayChild := by
  obtain ⟨member,alias⟩ := related
  rw [GeneralDictionarySupportRecursiveClosure.sites_exact] at member
  rcases List.mem_cons.mp member with rfl | tail
  · have impossible := GeneralDictionaryFiniteJournalJointExample.alias_eq alias
    contradiction
  · have same := List.mem_singleton.mp tail
    subst site
    rfl

theorem covered : GeneralDictionaryUnrecordedAliasLeafJoint.Covered registry finish displayChild intDisplay := by
  intro site related
  have same := child_locality site related
  rw [same]
  exact ⟨Or.inr ⟨shape⟩,3,[],supported_leaf_selected⟩

/-- The journal model is arbitrary. Its branch is derived from scalar syntax,
not by replaying a nonexistent child packet. -/
theorem child_joint (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) : Joint registry finish.current displayChild 3 :=
  GeneralDictionaryUnrecordedAliasLeafJoint.initial_trace_joint registry displayRoot displayChild
    (context true) initial_source finish GeneralDictionaryRecordedCoverageLimit.ordinary_trace
    intDisplay (by simp) int_display_checked (Or.inr ⟨shape⟩)
    3 [] supported_leaf_selected covered assignment valid

/-- Nonvacuity, with actual source reachability and the absence of a focus packet. -/
theorem actual_unrecorded_stable_joint :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayChild ∧
    Models finish.current model ∧ Joint registry finish.current displayChild 3 ∧
    ¬ ∃ packet ∈ finish.current.packets, packet.site.occurrence = displayChild :=
  ⟨actual_reachable,GeneralDictionaryRecordedCoverageLimit.leaf_stable,current_model,
    child_joint model current_model,GeneralDictionaryRecordedCoverageLimit.no_leaf_packet⟩
end Yulang.GeneralDictionaryUnrecordedAliasLeafExample
