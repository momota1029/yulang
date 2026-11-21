import Yulang.GeneralSharedNamedTrace310
import Yulang.GeneralVersionedHistoryChoice310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 17500000
/-! The root uses recorded ownership and both children use an unrecorded
aliased class. All three use the same actual checked run and its model. -/
namespace Yulang.GeneralSharedNamedCurrentGuards310
open GeneralSharedNamedSource310 (registry compiled checked)
open GeneralSharedNamedNodes310 (Node focus current_frame)
open GeneralSharedNamedSelection310 (actual_pick ready)
open GeneralSharedNamedMerge310 (merged added reached inhabited)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedMixedCurrentCandidate235 (Current)
open GeneralNominalVersionedMixedFrameSelection235 (effect_of_selected)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)

noncomputable def candidate (n : Node) : Effect roles :=
  effect_of_selected (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp (actual_pick n))
    (current_frame n) (ready n)

theorem compatible_root :
    GeneralNominalCycleSteps.ChoiceCompatible merged.core.erased.current (candidate .parent).plan.packet := by
  apply GeneralVersionedHistoryChoice310.choice_of_rechecked_history ⟨rfl,checked⟩ reached
    (actual_pick .parent) inhabited
  intro packet member _
  change packet ∈ [GeneralSharedNamedPlan310.packet] at member
  cases List.mem_singleton.mp member
  refine ⟨rfl,reserved GeneralSharedNamedPlan310.packet,atoms GeneralSharedNamedPlan310.packet ++ added,allocated GeneralSharedNamedPlan310.packet,?_,?_⟩
  · have ctx := GeneralSharedNamedCurrent310.current_parent.context_eq.symm
    rw [GeneralSharedNamedHistoryReplay310.composed_parent] at ctx
    exact ctx
  · exact List.Subset.refl _

theorem compatible (n : Node) :
    GeneralNominalCycleSteps.ChoiceCompatible merged.core.erased.current (candidate n).plan.packet := by
  cases n
  · exact compatible_root
  · exact GeneralSharedNamedNoHistory310.compatible .low
  · exact GeneralSharedNamedNoHistory310.compatible .high

theorem joint (n : Node) (m : Assignment) (valid : Models merged m) :
    GeneralNominalVersionedInstall232.InstallationModels merged (candidate n) m := by
  apply (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ reached rfl rfl).mpr
  have sem := (GeneralSharedNamedTrace310.committed n).1 m valid
  exact ⟨valid,sem.1,sem.2⟩

theorem current (n : Node) : Current compiled merged (focus n) (candidate n) :=
  GeneralNominalVersionedMixedGuardReduction235.current rfl rfl (current_frame n).occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp (actual_pick n))
    (GeneralNominalVersionedMixedReady235.materialized reached (current_frame n))
    (compatible n) ⟨_,joint n _ inhabited⟩

theorem all_installable (n : Node) : Installable compiled merged (candidate n) :=
  GeneralNominalVersionedMixedCurrentCandidate235.source_installable (current n) reached (actual_pick n)

end Yulang.GeneralSharedNamedCurrentGuards310
