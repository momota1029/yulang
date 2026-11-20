import Yulang.GeneralMixedControlLabels306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedControlTrace306
open GeneralMixedControlMask306
open GeneralMixedControlAtoms306 (BasicFacts refresh_basic)
open GeneralMixedControlBisim306 (Observe labelled project_observe)
open GeneralDictionaryOutputDepth252 (roles)
open GeneralNominalVersionedJournal232 (State)

inductive Route : Mask → List (Fin 2 × Mask) → Mask → Prop
  | done : Route x [] x
  | advance : fire q x y = true → Route y suffix z → Route x ((q,y)::suffix) z

inductive RawTrace : State roles → List (Fin 2 × Mask) → State roles → Prop
  | done : RawTrace s [] s
  | advance : Observe q s t → RawTrace t suffix u → RawTrace s ((q,project t)::suffix) u

theorem preserve_basic {q : Fin 2} {s t : State roles}
    (v : BasicFacts s) (hop : Observe q s t) : BasicFacts t := by
  cases hop with
  | refresh ctx cert _ _ _ => exact refresh_basic v cert

theorem route_forward {s t : State roles} (taken : RawTrace s route t) :
    Route (project s) route (project t) := by
  induction taken with
  | done => exact .done
  | advance actual _ ih => exact .advance (project_observe actual) ih

theorem route_lift {s : State roles} (v : BasicFacts s) (made : Route (project s) route goal) :
    ∃ t, RawTrace s route t ∧ project t = goal := by
  induction route generalizing s with
  | nil =>
    cases made
    exact ⟨s,.done,rfl⟩
  | cons entry suffix ih =>
    obtain ⟨q,target⟩ := entry
    cases made with
    | advance step rest =>
      obtain ⟨next,hop,projected⟩ := (labelled v target q).mp step
      have remaining : Route (project next) suffix goal := projected.symm ▸ rest
      obtain ⟨last,done,final⟩ := ih (preserve_basic v hop) remaining
      exact ⟨last,projected ▸ (RawTrace.advance hop done),final⟩

theorem route_exact {s : State roles} (v : BasicFacts s) :
    Route (project s) route goal ↔ ∃ t, RawTrace s route t ∧ project t = goal :=
  ⟨route_lift v,fun ⟨_,h,eq⟩ => eq ▸ route_forward h⟩

theorem length_bound {x y : Mask} (made : Route x route y) :
    route.length + rank y ≤ rank x := by
  induction made with
  | done => simp
  | @advance q x y rest z hop _ ih =>
    have decreases := GeneralMixedControlLiveness306.rank_moves x y
      ((moves_exact x y).mpr ⟨q,hop⟩)
    simp only [List.length_cons]
    omega

end Yulang.GeneralMixedControlTrace306
