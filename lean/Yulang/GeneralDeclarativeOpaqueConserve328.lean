import Yulang.GeneralDeclarativeOpaqueVariantNames328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueConserve328
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeGrowth327 (Extends trans facts ordinary restrict)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeOpaqueIntervals328 (Ends low high protect left right ready)
open GeneralDeclarativeEntailment320 (Entails)


structure Retains (s t : State) (keep : List Nat) : Prop where
  grows : Extends s t
  lifts : ∀ m, Models s m → ∃ n, Models t n ∧ ∀ v ∈ stateNames s ++ keep, n v = m v

theorem stateGrows {s t : State} (h : Extends s t) : stateNames s ⊆ stateNames t := by
  intro n used
  rcases List.mem_append.mp used with normal|equation
  · apply List.mem_append_left
    rcases List.mem_append.mp normal with laws|intervals
    · apply List.mem_append_left
      obtain ⟨a,owned,found⟩ := List.mem_flatMap.mp laws
      exact List.mem_flatMap.mpr ⟨a,h.constraints owned,found⟩
    · apply List.mem_append_right
      obtain ⟨r,owned,found⟩ := List.mem_flatMap.mp intervals
      exact List.mem_flatMap.mpr ⟨r,h.intervals owned,found⟩
  · apply List.mem_append_right
    obtain ⟨e,owned,found⟩ := List.mem_flatMap.mp equation
    exact List.mem_flatMap.mpr ⟨e,h.equations owned,found⟩

theorem refl (s : State) (keep : List Nat) : Retains s s keep := by
  refine ⟨⟨fun _ h => h,fun _ h => h,fun _ h => h⟩,?_⟩
  intro m valid
  exact ⟨m,valid,fun _ _ => rfl⟩

theorem chain {s t u : State} (first : Retains s t keep) (later : Retains t u keep) : Retains s u keep := by
  refine ⟨trans first.grows later.grows,?_⟩
  intro m allowed
  obtain ⟨after,good,keepFirst⟩ := first.lifts m allowed
  obtain ⟨last,valid,keepAfter⟩ := later.lifts after good
  refine ⟨last,valid,fun n track => Eq.trans (keepAfter n ?_) (keepFirst n track)⟩
  rcases List.mem_append.mp track with before|named
  · exact List.mem_append_left _ (stateGrows first.grows before)
  · exact List.mem_append_right _ named

theorem exact {s t : State} (h : Retains s t keep) (m) :
    Models s m ↔ ∃ n, Models t n ∧ ∀ v ∈ stateNames s ++ keep, n v = m v :=
  ⟨h.lifts m,fun ⟨n,good,preserved⟩ =>
    (preserves_models s (fun v listed => preserved v (List.mem_append_left _ listed))).mp
      (restrict h.grows n good)⟩

theorem pairs {s : State} {a : Capture} (bounds : Bounds s a)
    (lo : Entails s ⟨a.lower,low e⟩) (hi : Entails s ⟨a.upper,high e⟩) (keep : List Nat) :
    Retains s (ready s a.center keep e) keep := by
  refine ⟨trans (facts _ _) (ordinary _ _),?_⟩
  intro m valid
  obtain ⟨n,read,seen⟩ := (GeneralDeclarativeOpaqueIntervals328.preserved bounds lo hi keep m).mp valid
  refine ⟨n,read,fun v uses => seen v ?_⟩
  rcases List.mem_append.mp uses with old|named
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ named))

theorem variants {s : State} {a : Capture} (bounds : Bounds s a)
    (lo : Entails s ⟨a.lower,.variant tag (.variable l)⟩)
    (hi : Entails s ⟨a.upper,.variant tag (.variable h)⟩) (keep : List Nat) :
    Retains s (GeneralDeclarativeOpaqueVariantNames328.ready s tag a.center l h keep) keep := by
  refine ⟨trans (facts _ _) (ordinary _ _),?_⟩
  intro m valid
  obtain ⟨n,read,seen⟩ := (GeneralDeclarativeOpaqueVariantNames328.conservative bounds lo hi keep m).mp valid
  refine ⟨n,read,fun v uses => seen v ?_⟩
  rcases List.mem_append.mp uses with old|named
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ named)))

end Yulang.GeneralDeclarativeOpaqueConserve328
