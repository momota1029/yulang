import Yulang.GeneralDeclarativeWitnessSeparateAuthorModel362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 71000
set_option maxHeartbeats 78000000
namespace Yulang.GeneralDeclarativeWitnessSeparateAuthorOrder362
open GeneralDeclarativeWitnessSeparateEndpointAuthors362
  (Ordered run authority row checked target payload dryOwner)
open GeneralDeclarativeWitnessThreeNative362 (ctor)
open GeneralDeclarativeWitnessSeparateAuthorModel362 (every_fit_of_third_author_keeps_original_window actual_multi_owner_model)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits interpreted NativeViews)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease checkExactRelease checked_exact_written_value)
open GeneralDeclarativeWitnessNativeOrder362 (node leftAtom rightAtom holds_yields_typed_context)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralNominalCommonBridge (Assignment)

def lo {c} (x : Ordered c) := node x.before.native.write.code
def mid {c} (x : Ordered c) := node x.center.native.write.code
def hi {c} (x : Ordered c) := node x.after.native.write.code

structure Compared {contra : Bool} (x : Ordered contra) where
  openedLow : ExactRelease x.after.final.board authority x.before.native.write
  openedMid : ExactRelease x.after.final.board authority x.center.native.write
  openedHigh : ExactRelease x.after.final.board authority x.after.native.write
  left : Compiled x.env table false (lo x) (mid x)
  right : Compiled x.env table false (mid x) (hi x)

def compare {contra} (x : Ordered contra) : Option (Compared x) := do
  let lower ← checkExactRelease x.after.final.board authority x.before.native.write
  let center ← checkExactRelease x.after.final.board authority x.center.native.write
  let upper ← checkExactRelease x.after.final.board authority x.after.native.write
  let a ← GeneralDeclarativeWitnessSparseIntervals357.compile x.env table false (lo x) (mid x)
  let b ← GeneralDeclarativeWitnessSparseIntervals357.compile x.env table false (mid x) (hi x)
  pure ⟨lower,center,upper,a,b⟩

def checks {contra x} (k : @Compared contra x) : Bool :=
  decide (k.left.rows = [leftAtom contra] ∧ k.right.rows = [rightAtom contra])

theorem separate_actual_modes_emit_expected_directions (contra : Bool) :
    ((run contra).bind fun x => (compare x).map checks).getD false = true := by
  cases contra <;> decide +kernel

theorem all_claims_one_final_fit {contra} {x : Ordered contra} {k : Compared x}
    (made : run contra = some x) (cmp : compare x = some k) (m : Assignment) (v : NativeViews)
    (fit : Fits x.after.final m v) :
    ContextDerives table m false (lo x) (mid x) ∧ ContextDerives table m false (mid x) (hi x) ∧
    v 301 = some (.unary (ctor contra) (.leaf (m (payload contra 0)).1)) ∧
    v 302 = some (.unary (ctor contra) (.leaf (m (payload contra 1)).1)) ∧
    v 303 = some (.unary (ctor contra) (.leaf (m (payload contra 2)).1)) := by
  have h := separate_actual_modes_emit_expected_directions contra
  rw [made] at h
  change ((compare x).map checks).getD false = true at h
  rw [cmp] at h
  have comparisons := of_decide_eq_true (show checks k = true from h)
  obtain ⟨_,down,up⟩ := every_fit_of_third_author_keeps_original_window x m v fit
  have l : (leftAtom contra).Holds CommonNominalFullCarrier.model m := by cases contra; exact down; exact up
  have r : (rightAtom contra).Holds CommonNominalFullCarrier.model m := by cases contra; exact up; exact down
  have a := holds_yields_typed_context k.left m (by intro row seen; rw [comparisons.1] at seen; cases List.mem_singleton.mp seen; exact l)
  have b := holds_yields_typed_context k.right m (by intro row seen; rw [comparisons.2] at seen; cases List.mem_singleton.mp seen; exact r)
  have code := GeneralDeclarativeWitnessSeparateEndpointAuthors362.actual_three_independent_authors contra
  rw [made] at code
  change checked x = true at code
  have rows := (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp code).1).1).1).2
  have one := (List.cons.inj rows).1
  have two := (List.cons.inj (List.cons.inj rows).2).1
  have three := (List.cons.inj (List.cons.inj (List.cons.inj rows).2).2).1
  have seen1 := checked_exact_written_value (w := x.after.final) k.openedLow m v fit
  have seen2 := checked_exact_written_value (w := x.after.final) k.openedMid m v fit
  have seen3 := checked_exact_written_value (w := x.after.final) k.openedHigh m v fit
  rw [one] at seen1
  rw [two] at seen2
  rw [three] at seen3
  exact ⟨a.2.2,b.2.2,seen1,seen2,seen3⟩

def dried (w : World) : World := {w with board := dryOwner w.board 0}

theorem changing_just_lower_authorship_status_preserves_every_fit (w : World) (m : Assignment) (v : NativeViews) :
    Fits (dried w) m v ↔ Fits w m v := Iff.rfl

theorem actual_window_from_separate_authored_declarations (contra : Bool) :
    ∃ (x : Ordered contra) (k : Compared x), run contra = some x ∧ compare x = some k ∧
      ∀ u, Fits x.after.final (GeneralDeclarativeWitnessSeparateAuthorModel362.model contra u)
        (interpreted x.after.final.board (GeneralDeclarativeWitnessSeparateAuthorModel362.model contra u)) := by
  obtain ⟨x,started,fit⟩ := actual_multi_owner_model contra
  have seen := separate_actual_modes_emit_expected_directions contra
  rw [started] at seen
  change ((compare x).map checks).getD false = true at seen
  cases cand : compare x with
  | none => rw [cand] at seen; cases seen
  | some c => exact ⟨x,c,started,cand,fit⟩

end Yulang.GeneralDeclarativeWitnessSeparateAuthorOrder362
