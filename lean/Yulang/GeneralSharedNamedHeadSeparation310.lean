import Yulang.GeneralSharedNamedObserverGap310
import Yulang.GeneralVersionedCandidateReplay310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 12500000
/-! Even exact current Survivor (candidate id and ordered children) fails to
distinguish the two real checkpoints. Class administration matters. -/
namespace Yulang.GeneralSharedNamedHeadSeparation310
open GeneralSharedNamedSource310 (registry compiled)
open GeneralSharedNamedPlan310 (loSite)
open GeneralSharedNamedInstall310 (after)
open GeneralSharedNamedMerge310 (merged added supported after_context)
open GeneralVersionedCandidateReplay310 (survivor Implied)
open GeneralNominalVersionedCandidates231 (Survivor)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)

theorem implied : Implied after.core.erased.current.context added :=
  fun m _ => GeneralSharedNamedMerge310.added_model m

theorem observer_exact (d : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    Survivor compiled merged.core.erased.current.context d key children ↔
      Survivor compiled after.core.erased.current.context d key children := by
  rw [after_context]
  exact survivor _ _ _ d key children supported implied

theorem both_have_real_candidate :
    Survivor compiled after.core.erased.current.context loSite.occurrence 2 [] ∧
    Survivor compiled merged.core.erased.current.context loSite.occurrence 2 [] := by
  have final := GeneralSharedNamedSelection310.survivor .low
  exact ⟨(observer_exact _ _ _).mp final,final⟩

theorem equal_observations_different_selection :
    (∀ (d : Occurrence roles) (key : Nat) (children : List (Occurrence roles)), Survivor compiled after.core.erased.current.context d key children ↔
      Survivor compiled merged.core.erased.current.context d key children) ∧
    GeneralSharedNamedObserverGap310.observe after = GeneralSharedNamedObserverGap310.observe merged ∧
    ¬ Local registry after loSite.occurrence (.selected 2 []) ∧
    Local registry merged loSite.occurrence (.selected 2 []) :=
  ⟨fun d key children => (observer_exact d key children).symm,
    GeneralSharedNamedObserverGap310.indistinguishable,
    GeneralSharedNamedObserverGap310.not_selected_before,
    GeneralSharedNamedObserverGap310.selected_after⟩

end Yulang.GeneralSharedNamedHeadSeparation310
