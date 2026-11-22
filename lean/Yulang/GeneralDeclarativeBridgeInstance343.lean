import Yulang.GeneralDeclarativeOriginSplit343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 8700000
namespace Yulang.GeneralDeclarativeBridgeInstance343
open GeneralDeclarativeModeBridge343 (joined with_actual_site)
open GeneralDeclarativeRankedBridge343 (CoLevels preserves_rank)
open GeneralDeclarativePlacement343 (view rows symbolic actual)
open GeneralDeclarativeLogicalChild343 (output child)
open GeneralDeclarativeFreshModel343 (kept fixed_output_model)
open GeneralDeclarativeFreshValues343 (mode_match)
open GeneralDeclarativeFrameRank343 (level level_lo level_mid level_hi logical_levels)
open GeneralDeclarativeFrameGuard343 (ranked)
open GeneralDeclarativeVersionedChildView342 (d actual_arguments)
open GeneralDeclarativeVersionedTree342 (child_requests)
open GeneralDeclarativeVersionedPhysical342 (new_registered)
open GeneralDeclarativeStoppedPaired341 (activeDemand Placement)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

theorem current_demand : activeDemand final.mixed newChild = d := by
  unfold activeDemand
  rw [actual_arguments,child_requests] <;> rfl

theorem exact_join : joined (output kept) (activeDemand final.mixed newChild) (child kept) = view := by
  rw [current_demand]
  rfl

theorem matching_levels :
    All₂ (CoLevels level) (activeDemand final.mixed newChild).arguments (child kept).arguments := by
  rw [current_demand]
  exact .cons ⟨level_lo.trans logical_levels.1.symm,level_mid.trans logical_levels.2.1.symm,
    level_hi.trans logical_levels.2.2.symm⟩ .nil

theorem bare_rank : Ranked (output kept) level := by
  refine ⟨ranked.bounded,?_,?_⟩
  · intro a b got
    exact ranked.flat (List.mem_append_left rows got)
  · intro row got n used notVar
    exact ranked.compound row (List.mem_append_left rows got) n used notVar

theorem ranked_by_generic_bridge : Ranked view level :=
  exact_join ▸ preserves_rank bare_rank matching_levels

theorem models_by_generic_bridge (m : Assignment) (valid : Models final m) :
    ∃ n, Models final n ∧ (∀ k ∈ kept, n k = m k) ∧
      GeneralDeclarativeHead320.Models view n ∧
      Placement final.mixed view newChild.occurrence (child kept) := by
  obtain ⟨n,ordinary,agrees,raw⟩ := fixed_output_model m valid
  have modes := mode_match n raw ordinary
  have ordered : All₂ (GeneralStoppedPlacement335.Meaning n)
      (activeDemand final.mixed newChild).arguments (child kept).arguments := by
    rw [current_demand]
    exact .cons modes .nil
  have role : (activeDemand final.mixed newChild).role = (child kept).role := rfl
  have targets : (activeDemand final.mixed newChild).outputs = (child kept).outputs := by
    rw [current_demand]
    rfl
  have same := with_actual_site new_registered role targets ordered ordinary
  rw [exact_join] at same
  exact ⟨n,raw,agrees,same⟩

end Yulang.GeneralDeclarativeBridgeInstance343
