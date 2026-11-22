import Yulang.GeneralDeclarativeFrameShape343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeFrameRank343
open GeneralDeclarativeFrameShape343 (b0 b1 e0 e1 e2 edges exact_rows exact_intervals retained_constraints)
open GeneralDeclarativePlacement343 (actual symbolic bridge view fresh_lower)
open GeneralDeclarativeLogicalChild343 (stage fresh protect capture)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeInitialModels343 (first_capture second_capture parts)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeNewNames321 (before_after)
open GeneralDeclarativeFootprint321 (stateNames atomSources)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralDeclarativeVersionedChildBody342 (lo_level mid_level hi_level level2)
open PresenceNormalForm (Atom)

noncomputable abbrev lowNames := [2,b0.lower,b0.upper,b1.lower,b1.upper]
noncomputable def level (n : Nat) : Nat := if n ∈ lowNames then 0 else 1

theorem level_low {n : Nat} (mem : n ∈ lowNames) : level n = 0 := by simp [level,mem]
theorem level_high {n : Nat} (mem : n ∉ lowNames) : level n = 1 := by simp [level,mem]

theorem old_below {n : Nat} (keep : n ∈ kept) (s : State) :
    n < (GeneralDeclarativeAggregate324.span s kept typePoint []).lower := by
  unfold GeneralDeclarativeAggregate324.span GeneralDeclarativeFreshTerms324.first
  apply before_after
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ keep)))

theorem low_not_old {n : Nat} (keep : n ∈ kept) (notTwo : n ≠ 2) : n ∉ lowNames := by
  intro hit
  have a := old_below keep observedRoot
  have b := old_below keep (GeneralDeclarativeAggregate324.ready observedRoot kept typePoint [])
  rw [← first_capture kept] at a
  rw [← second_capture kept] at b
  change n < b0.lower at a
  change n < b1.lower at b
  have hi0 : b0.upper = b0.lower + 1 := by
    change (capture kept 0).upper = (capture kept 0).lower + 1
    rw [first_capture]
    rfl
  have hi1 : b1.upper = b1.lower + 1 := by
    change (capture kept 1).upper = (capture kept 1).lower + 1
    rw [second_capture]
    rfl
  change n ∈ [2,b0.lower,b0.upper,b1.lower,b1.upper] at hit
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with eq | eq | eq | eq | eq <;> omega

theorem level_lo : level actual.lower = 1 := by
  apply level_high (low_not_old (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))) ?_)
  intro h
  change loNow = 2 at h
  have h' := lo_level
  rw [h,level2] at h'
  omega

theorem level_mid : level actual.center = 1 := by
  apply level_high (low_not_old (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) ?_)
  intro h
  change mid = 2 at h
  have h' := mid_level
  rw [h,level2] at h'
  omega

theorem level_hi : level actual.upper = 1 := by
  apply level_high (low_not_old (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self))))) ?_)
  intro h
  change hi = 2 at h
  have h' := hi_level
  rw [h,level2] at h'
  omega

theorem ordinary_layout : (stage kept).normal.ordinary = edges b0 ++ edges b1 := rfl

theorem before_fresh {n : Nat} (seen : n ∈ lowNames) : n < fresh kept := by
  unfold fresh GeneralDeclarativeFreshWhere325.seed
  apply before_after
  apply List.mem_append_left _
  apply List.mem_append_left _
  unfold stateNames
  apply List.mem_append_left _
  apply List.mem_append_left _
  rw [ordinary_layout,List.flatMap_append]
  simp only [lowNames,List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl|rfl|rfl
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.tyLe (.var 2) (.var 2),List.mem_cons_self,List.mem_cons_self⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.tyLe (.var b0.lower) (.var 2),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),List.mem_cons_self⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.tyLe (.var b0.upper) (.var 2),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),List.mem_cons_self⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.tyLe (.var b1.lower) (.var 2),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),List.mem_cons_self⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.tyLe (.var b1.upper) (.var 2),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),List.mem_cons_self⟩)

theorem logical_levels : level symbolic.lower = 1 ∧ level symbolic.center = 1 ∧ level symbolic.upper = 1 := by
  refine ⟨level_high ?_,level_high ?_,level_high ?_⟩ <;> intro h
  · have less := before_fresh h
    change fresh kept < fresh kept at less
    omega
  · have less := before_fresh h
    change fresh kept + 1 < fresh kept at less
    omega
  · have less := before_fresh h
    change fresh kept + 2 < fresh kept at less
    omega

theorem level_root : level 0 = 1 :=
  level_high (low_not_old List.mem_cons_self (by decide))

theorem level2_here : level 2 = 0 := level_low List.mem_cons_self
theorem levelL0 : level b0.lower = 0 := level_low (List.mem_cons_of_mem _ List.mem_cons_self)
theorem levelH0 : level b0.upper = 0 := level_low (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem levelL1 : level b1.lower = 0 := level_low (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
theorem levelH1 : level b1.upper = 0 := level_low (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

private theorem one_edge {a b : Nat} (cap : Capture)
    (lo : level cap.lower = 0) (hi : level cap.upper = 0)
    (given : Atom.tyLe (.var a) (.var b) ∈ edges cap) :
    level a ≤ level b := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at given
  rcases given with one | one | one | one | one | one | one | one <;> cases one <;>
    simp only [level2_here,lo,hi,Nat.le_refl]

theorem ordinary_edge {a b : Nat} (given : Atom.tyLe (.var a) (.var b) ∈ view.normal.ordinary) :
    level a ≤ level b := by
  rw [retained_constraints,List.mem_append] at given
  exact given.elim (one_edge b0 levelL0 levelH0) (one_edge b1 levelL1 levelH1)

theorem bound_levels {a b : Nat} (h : Bound view.normal a b) : level a ≤ level b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | trans _ _ lo hi => exact Nat.le_trans lo hi
  | constraint given => exact ordinary_edge given
  | interval given =>
    rw [exact_intervals] at given
    rcases List.mem_cons.mp given with same|other
    · cases same
      rw [logical_levels.1,logical_levels.2.1]
      exact Nat.le_refl _
    · cases List.mem_singleton.mp other
      rw [logical_levels.2.1,logical_levels.2.2]
      exact Nat.le_refl _

end Yulang.GeneralDeclarativeFrameRank343
