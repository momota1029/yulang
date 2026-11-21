import Yulang.GeneralDeclarativeRecordResidual323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeVisibleRecord326
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeHead320 (environment)
open GeneralNominalCommonBridge (Assignment shadow swap)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm record_congr)
open CommonRoleCanonicalRows (Row residual normalize)

theorem erased_behind {m : Assignment} (label : Nat) (head terminal : Expr)
    (xs : Row Expr) :
    eqAt m (.record label head (withTail xs terminal))
      (.record label head (withTail (residual [label] xs) terminal)) := by
  induction xs with
  | nil => exact eqv_refl _
  | cons field rest ih =>
    obtain ⟨other,payload⟩ := field
    by_cases same : other = label
    · subst other
      have erased : residual [label] ((label,payload)::rest) = residual [label] rest := by
        simp [residual]
      rw [erased]
      exact eqv_trans (shadow label _ _ _) ih
    · have keeps : residual [label] ((other,payload)::rest) =
          (other,payload) :: residual [label] rest := by simp [residual,same]
      rw [keeps]
      exact eqv_trans (swap label other (Ne.symm same) _ _ _)
        (eqv_trans (record_congr other (eqv_refl _) ih)
          (eqv_symm (swap label other (Ne.symm same) _ _ _)))

/-- First visible field wins at each label. Payloads behind a first
field are removed before taking a residual. The terminal remains
unchanged; deciding that an unknown terminal is complete is separate. -/
theorem visible_spine (m : Assignment) (xs : Row Expr) (terminal : Expr) :
    eqAt m (withTail xs terminal) (withTail (normalize xs) terminal) := by
  induction xs with
  | nil => exact eqv_refl _
  | cons field rest ih =>
    obtain ⟨label,payload⟩ := field
    exact eqv_trans (record_congr label (eqv_refl _) ih)
      (erased_behind (m := m) label payload terminal (normalize rest))

end Yulang.GeneralDeclarativeVisibleRecord326
