import Yulang.GeneralDictionaryOrdinaryTransportExamples
import Yulang.GeneralDictionaryFeedbackEvidenceExamples
import Yulang.GeneralDictionaryRecursiveEvidenceFacts

/-! The existing actual child-descriptor refresh has current-context source
meaning for its recorded parent. This concrete regression does not extend the
ordinary-only transport theorem to arbitrary descriptor-changing refreshes. -/
namespace Yulang.GeneralDictionaryRefreshCurrentEvidence
open GeneralNominalFeedbackObstruction
open GeneralNominalFeedbackRefresh
open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveCandidates

abbrev zero : Fin refreshedContext.state.base.slots := ⟨0,by decide +kernel⟩
abbrev capturedBounds : GeneralNominalInspection.Bounds refreshedContext.state :=
  (⟨2,by decide +kernel⟩,⟨3,by decide +kernel⟩)

theorem refreshed_report : report refreshedContext declaration [(zero,zero)] =
    GeneralNominalUnaryCaptureFacts.captured refreshedContext.state zero 0 0 capturedBounds := by
  apply GeneralNominalUnaryCaptureFacts.report_exact refreshedContext declaration zero
    GeneralNominalIntervalExamples.descriptor
  · rfl
  · rfl
  · simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,refreshedContext,
      GeneralNominalFeedbackRefresh.refreshedState]
    rfl

theorem original_report : report context declaration [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] =
    GeneralNominalUnaryCaptureFacts.captured source ⟨0,by decide +kernel⟩ 0 0 (2,3) := by
  exact report_exact

/-- The parent's report still observes its original list interval. The new
nominal descriptor is installed at the generated child's source, not that head. -/
theorem refreshed_parent_branch (m : Assignment) (valid : Models refreshed m) :
    BranchModels registry refreshedContext root declaration declaration_checked [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] m := by
  have old := valid.2.1 packet (by simp [refreshed,regenerate,installed,GeneralNominalFeedbackSites.install])
  change BranchModels registry context root declaration declaration_checked [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] m at old
  rw [GeneralDictionaryRecursiveEvidence.branch_models_iff] at old ⊢
  refine ⟨valid.1,?_⟩
  unfold generated at old ⊢
  rw [original_report] at old
  rw [refreshed_report]
  refine ⟨old.2.1,old.2.2.1,old.2.2.2.1,?_,?_⟩
  · exact GeneralNominalUnaryCaptureFacts.projection_models refreshedContext.state m valid.1
      zero GeneralNominalIntervalExamples.descriptor rfl 0 capturedBounds rfl
  · have material := old.2.2.2.2.2
    simp only [GeneralNominalMaterialization.Models,GeneralNominalUnaryCaptureFacts.captured,
      List.mem_singleton,forall_eq] at material ⊢
    exact material

theorem refreshed_current_parent_instance (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child] := by
  have old := GeneralDictionaryFeedbackEvidenceExamples.refreshed_source_instance m valid
  obtain ⟨decl,visible,checked,key,role,bounds,located,finished,ready,children,metadata,branch⟩ := old
  have same := List.mem_singleton.mp visible
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] := Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  refine ⟨declaration,by simp,declaration_checked,rfl,rfl,[(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)],?_,?_,?_,?_,?_,refreshed_parent_branch m valid⟩
  · exact located
  · rw [refreshed_report]
    exact ⟨rfl,rfl,rfl⟩
  · rw [RequestReady,generated,refreshed_report]
    exact ⟨ready.1,by decide +kernel⟩
  · rw [refreshed_report]
    have h := children_exact.symm
    unfold Packet.children Packet.bindings at h
    rw [report_exact] at h
    exact h
  · exact metadata

end Yulang.GeneralDictionaryRefreshCurrentEvidence
