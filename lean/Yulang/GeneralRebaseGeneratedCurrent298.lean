import Yulang.GeneralNominalVersionedMixedCurrentCandidate235
import Yulang.GeneralRebaseCompiledEvidenceAt277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseGeneratedCurrent298
open GeneralNominalExamples (registry model displayRoot displayChild intDisplay)
open GeneralDeclarationExamples (roles display)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompiledDisplay277 (after compiled effect)
open GeneralRebaseCompiledSelection277 (child child_frame unique_child after_model picked_child)
open GeneralNominalVersionedMixedCurrentCandidate235 (Current)
open GeneralNominalVersionedInstall232 (InstallationModels installCore)
open GeneralRebaseDisplayFrame276 (classes_empty)

noncomputable def certificate : Effect roles :=
  ⟨compiled,after.core,child,child_frame,
    GeneralRebaseCompiledChild277.no_children.symm ▸ unique_child,
    GeneralRebaseCompiledEvidence277.ready child⟩

theorem noEmits : GeneralNominalVersionedChildren232.emitted child = [] := by
  apply List.length_eq_zero_iff.mp
  rw [GeneralNominalVersionedChildren232.emitted_length]
  rfl

theorem sameSites : (installCore after.core child).erased.current.sites = after.core.erased.current.sites := by
  change after.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites child = _
  simp [GeneralNominalVersionedChildren232.rawSites,noEmits]

theorem noRequests (focus) : GeneralNominalCenteredHeadOutputs.requests (installCore after.core child) focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  have before := (GeneralNominalVersionedRefresh232.requests_iff_of_same_lists
    (root := focus) (output := output) sameSites rfl).mp member
  rw [GeneralRebaseCompiledInstall277.no_new_request] at before
  cases before

theorem commonModel : InstallationModels after certificate model := by
  have held := GeneralRebaseCompiledChild277.holds model after_model
  refine ⟨after_model,held,⟨GeneralNominalVersionedPlans231.head_models held,
    classes_empty (GeneralRebaseCompiledInstall277.no_new_request displayChild) child model⟩,
    classes_empty (noRequests displayChild) child model,?_,?_⟩
  · intro old member
    cases member
  · intro old member
    exact classes_empty (noRequests old.plan.packet.site.occurrence) old.plan model

theorem alias_eq {a b} (p : GeneralNominalSaturationState.Alias after.core.erased.current a b) : a = b := by
  induction p with
  | refl => rfl
  | edge absurd => cases absurd
  | symm _ ih => exact ih.symm
  | trans _ _ i j => exact i.trans j

theorem compatible : GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current child.packet := by
  intro old member same
  have no := alias_eq same
  change old ∈ [GeneralRebaseCompiledDisplay277.parent.packet] at member
  cases List.mem_singleton.mp member
  exact False.elim ((by decide : displayChild.identity ≠ displayRoot.identity) no)

theorem inspection_length :
    (GeneralNominalCenteredSteps.inspection child).inspected.length =
      (GeneralNominalCenteredSteps.inspection child).tests.length := by
  unfold GeneralNominalCenteredSteps.inspection
  rw [show GeneralNominalInspection.queries child.packet.context.state
    child.packet.context.interpretation child.packet.declaration = [.scalar .int] from GeneralRebaseCompiledChild277.query]
  have absent : GeneralRebaseCompiledChild277.context.state.nominals (1 : Fin 2) = none := rfl
  have scalar : GeneralRebaseCompiledChild277.context.state.view.heads (1 : Fin 2) = .scalar .int := rfl
  simp [absent,scalar,GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append,
    GeneralRebaseCompiledChild277.packet,GeneralNominalNonleafPlan193.centerSite]
  decide +kernel

theorem positions : GeneralNominalVersionedCycles232.Safe after child :=
  ⟨inspection_length, fun entry _ => GeneralRebaseDisplaySafety276.semantic after_model entry.1⟩

theorem alternatives : GeneralNominalVersionedMixedKernel234.AlternativesSafe compiled after child.input := by
  intro plan _ frame
  have eq := GeneralRebaseCompiledStable277.framed_child frame
  subst plan
  exact positions

theorem current : Current compiled after displayChild certificate := by
  refine ⟨rfl,rfl,rfl,?_,compatible,positions,alternatives,⟨model,commonModel⟩⟩
  change (GeneralNominalVersionedPlans231.emittedSchema child).unknown = false
  rw [GeneralRebaseCompiledChild277.emitted_empty]

theorem installable_but_committed :
    GeneralNominalVersionedMixedKernel234.Installable compiled after certificate ∧
      GeneralNominalVersionedMixedKernel234.Committed after certificate.plan :=
  ⟨GeneralNominalVersionedMixedCurrentCandidate235.source_installable current
      GeneralRebaseCompiledInstall277.reachable picked_child,
    GeneralRebaseCompiledStable277.committed_child⟩

end Yulang.GeneralRebaseGeneratedCurrent298
