import Yulang.GeneralDeclarativeLogicalChild343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 5300000
namespace Yulang.GeneralDeclarativeInitialModels343
open GeneralDeclarativeVersionedRootGuard342 (observedRoot every_model)
open GeneralDeclarativeVersionedRootShape342 (spans typePoint)
open GeneralDeclarativeLogicalChild343 (stage capture fallback)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeStableAssemble329 (merged assemble witness_projection)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeAggregate324 (ready span assembled)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeMerge320 (equality_sound)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

theorem parts (keep : List Nat) :
    stage keep = ready (ready observedRoot keep typePoint []) keep typePoint [] := rfl

theorem first_capture (keep : List Nat) :
    capture keep 0 = span observedRoot keep typePoint [] := rfl

theorem second_capture (keep : List Nat) :
    capture keep 1 = span (ready observedRoot keep typePoint []) keep typePoint [] := rfl

theorem ranges : ∀ a ∈ spans, Bounds observedRoot a.2 := by
  intro a used
  rcases List.mem_cons.mp used with same|out
  · cases same
    exact point_bounded _ _
  · cases List.mem_singleton.mp out
    exact point_bounded _ _

theorem equal_uses (m : Assignment) : EqualUses m spans := by
  intro key a b aMem bMem
  have first : ∀ q : Capture, (key,q) ∈ spans → q.center = 2 := by
    intro q here
    rcases List.mem_cons.mp here with one|rest
    · cases one
      rfl
    · cases List.mem_singleton.mp rest
      rfl
  rw [first a aMem,first b bMem]
  exact eqv_refl _

theorem kept_stage (keep : List Nat) (m : Assignment) (fit : Models observedRoot m) :
    ∃ n, Models (stage keep) n ∧ ∀ k ∈ keep, n k = m k := by
  obtain ⟨n,valid,agrees⟩ := (witness_projection (assemble keep spans fallback ranges) m).mp
    ⟨fit,equal_uses m⟩
  exact ⟨n,valid,fun k used => agrees k (List.mem_append_right _ used)⟩

theorem singleton_bounds {s : State} : ∀ a ∈ [typePoint], Bounds s a :=
  fun _ h => List.mem_singleton.mp h ▸ point_bounded _ _

theorem first_values (keep : List Nat) (m : Assignment) (fit : Models (stage keep) m) :
    Equivalent (m (capture keep 0).lower).1 (m 2).1 ∧
    (capture keep 0).center = 2 ∧
    Equivalent (m (capture keep 0).upper).1 (m 2).1 := by
  rw [parts] at fit
  have inner : Models (ready observedRoot keep typePoint []) m :=
    restrict (GeneralDeclarativeOpaqueGroup328.aggregate_grows _ _ _ _) m fit
  have readings := assembled (s := observedRoot) (extra := keep) (seed := typePoint) (rest := []) singleton_bounds
  have basic : Models (GeneralDeclarativeAggregate324.aggregates observedRoot keep typePoint []) m :=
    ((GeneralDeclarativeAggregate324.ready_iff (extra := keep) singleton_bounds m).mp inner)
  rw [first_capture]
  exact ⟨equality_sound readings.lowerEq m basic,rfl,equality_sound readings.upperEq m basic⟩

end Yulang.GeneralDeclarativeInitialModels343
