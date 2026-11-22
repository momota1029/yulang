import Yulang.GeneralDeclarativeVersionedPaired342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17200
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeVersionedStale342
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWhereOriginSingleCells318 (oldChild loOld loNow hi exact_old)
open GeneralWherePhysicalCurrentRead319 (child_bounds)
open GeneralWherePhysicalChildModel319 (child_center)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionInstall317 (Models)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeVersionedChildView342 (arg d)
open GeneralDeclarativeDemand320 (Demand)
open GeneralStoppedOrdinarySite335 (demand argument)
open GeneralStoppedPlacement335 (SameCapture SameDemand)
open GeneralDeclarativeVersionedPhysical342 (same_id_not_occurrence)
open GeneralDeclarativeVersionedSeparation342 (not_current_lower)
open CommonNominalFullCarrier (Equivalent)

abbrev historical : Capture := ⟨loOld,mid,hi⟩

theorem old_center : oldChild.center (0 : Fin 1) = mid := rfl

theorem historical_argument : argument oldChild (0 : Fin 1) = historical := by
  unfold argument
  rw [exact_old,old_center]

theorem actual_argument : argument newChild (0 : Fin 1) = arg := by
  unfold argument
  rw [child_bounds,child_center]

theorem old_arguments : (demand oldChild).arguments = [historical] := by
  unfold demand
  simp only [List.ofFn_succ]
  rw [historical_argument]
  rfl

theorem active_history : (GeneralDeclarativeStoppedPaired341.activeDemand final.mixed oldChild).arguments = [historical] :=
  old_arguments

/-- Even owner ID *plus* actual center *plus* correct reused upper
address is insufficient to justify substituting an archived child.
The lower side cannot be bridged by a checked normalized alias on
any view that preserves an actual current versioned model. -/
theorem no_substitute (s : State) (m : Assignment) (raw : Models final m)
    (ordinary : GeneralDeclarativeHead320.Models s m) :
    oldChild.occurrence.identity = newChild.occurrence.identity ∧
    (argument oldChild (0 : Fin 1)).center = (argument newChild (0 : Fin 1)).center ∧
    (argument oldChild (0 : Fin 1)).upper = (argument newChild (0 : Fin 1)).upper ∧
    ¬ SameDemand s (GeneralDeclarativeStoppedPaired341.activeDemand final.mixed oldChild) d := by
  refine ⟨same_id_not_occurrence.1,?_,?_,?_⟩
  · rw [historical_argument,actual_argument]
  · rw [historical_argument,actual_argument]
  · intro matchSite
    have matched := (GeneralStoppedPlacement335.demands_models ordinary matchSite).2.2
    rw [active_history] at matched
    change CommonRoleOutermostResolver.All₂ (GeneralStoppedPlacement335.Meaning m) [historical] [arg] at matched
    cases matched with
    | cons atFirst _ =>
      exact not_current_lower m raw atFirst.1

end Yulang.GeneralDeclarativeVersionedStale342
