import Yulang.GeneralDictionaryNonpointStrictOutput
import Yulang.GeneralDictionaryCheckedNonpointEvidence

/-! A nonempty associated-output instance inhabits strict nonpoint collapse.
This is a positive private/source model witness, NOT a certified operational
transition or a theorem about all models of an arbitrary reachable state. -/
namespace Yulang.GeneralDictionaryNonpointStrictEvidence
open GeneralDictionaryNonpointStrictOutput
open GeneralDictionaryNonpointStrict (context shape revision model bounds source interpretation)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence

noncomputable abbrev currentContext := GeneralDictionarySemanticCollapseBranch.currentContext revision

theorem old_located : arguments context outputRoot = some bounds := by decide +kernel

theorem current_located : arguments currentContext outputRoot = some bounds := old_located

theorem ready : RequestReady registry context outputRoot declaration checked bounds := by
  constructor
  · intro output member
    cases List.mem_singleton.mp member
    exact ⟨⟨43,0,.var 7⟩,by simp,rfl⟩
  · rw [generated_exact]

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name primitive found
  cases found

theorem old_instance : Instance registry context model outputRoot declaration.id [] := by
  refine ⟨declaration,by simp,checked,rfl,rfl,bounds,old_located,?_,ready,?_,metadata,old_branch⟩
  · rw [report_exact]
    exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry outputRoot declaration checked rfl _).symm

theorem current_instance : Instance registry currentContext model outputRoot declaration.id [] := by
  refine ⟨declaration,by simp,checked,rfl,rfl,bounds,current_located,?_,?_,?_,metadata,?_⟩
  · exact (GeneralDictionaryCollapseReadiness.finished shape declaration queries).2
  · exact (GeneralDictionaryCollapseReadiness.ready_same shape registry outputRoot declaration checked rfl).mpr ready
  · exact (GeneralDictionaryLinearLeaf.children_empty currentContext registry outputRoot declaration checked rfl _).symm
  · exact GeneralDictionaryCheckedNonpointEvidence.branch shape registry outputRoot declaration checked queries names rfl model
      old_branch GeneralDictionaryNonpointStrict.revised_models

theorem old_evidence : Evidence registry context model outputRoot (.node declaration.id []) :=
  evidence_node registry context model outputRoot declaration.id [] [] old_instance .nil

theorem current_evidence : Evidence registry currentContext model outputRoot (.node declaration.id []) :=
  evidence_node registry currentContext model outputRoot declaration.id [] [] current_instance .nil

theorem positive_strict_output_evidence :
    body.variables.length = 1 ∧ shape.first.1 ≠ shape.first.2 ∧
    Evidence registry context model outputRoot (.node declaration.id []) ∧
    Evidence registry currentContext model outputRoot (.node declaration.id []) :=
  ⟨rfl,GeneralDictionaryNonpointStrict.nonpoint_leaf.1,old_evidence,current_evidence⟩
end Yulang.GeneralDictionaryNonpointStrictEvidence
