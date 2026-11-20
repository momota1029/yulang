import Yulang.GeneralRebaseRowSourceLeaf287

/-! Formal scope of the row example: actual raw kernel steps do not make
it an admissible instance of the more restrictive outer GroundRoots entry. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowOuterBoundary287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowGroundBoundary287 (cannot_ground)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedBoundary234 (boundary Initial)

theorem source_same_step {s t : State universeRoles} (move : Step registry₀ root₀ s t) :
    s.core.erased.source = t.core.erased.source := by
  obtain ⟨_,_,atMove⟩ := move
  cases atMove with
  | administrative rule => cases rule <;> rfl
  | refresh => rfl
  | install => rfl
  | merge => rfl

theorem source_same_path {s t : State universeRoles} (path : B4Target.Steps (Step registry₀ root₀) s t) :
    s.core.erased.source = t.core.erased.source := by
  induction path with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (source_same_step edge)

theorem initial_requires_other_context (choice : Bool) {s : State roles}
    (same : s.core.erased.source = ctx) :
    ¬ Initial (registry choice) root s := by
  rintro ⟨legacy,⟨rc,labels,_,_,ground,_,legacyEq⟩,stateEq⟩
  have context : rc = ctx := by
    rw [stateEq,legacyEq] at same
    exact same
  exact cannot_ground labels (context ▸ ground)

theorem no_outer_before (choice : Bool) :
    ¬ (boundary roles).Initial (registry choice) root before :=
  initial_requires_other_context choice rfl

theorem no_outer_reach (choice : Bool) :
    ¬ B4TargetV8.Reachable (boundary roles) (registry choice) root (after choice) := by
  rintro ⟨s,initial,path⟩
  exact initial_requires_other_context choice (source_same_path path) initial

end Yulang.GeneralRebaseRowOuterBoundary287
