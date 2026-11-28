import Yulang.GeneralDeclarativeI65I74SourceIndexPair478
import Yulang.GeneralDeclarativeI65I74ReadOldCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeHead320 (Equation)
private abbrev OldRawState478 := GeneralDeclarativeHead320.State
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open C466WrittenBinderCoordinates (OldCaptureReceipt readOldCaptureReceipt exact_old_capture_execution_has_data_only_receipt
  a_receipt_really_names_the_original_capture_and_the_appended_ordinary_row)

theorem actual_old_compiler_job_is_a_post_input_ordinal_not_a_same_phase_read478
    {s : OldRawState478} {done : Nat → Prop} {old : Supported s done}
    {auth : Sources (restriction old)} {c i arg kept pattern job} {emitted : OldCaptureReceipt}
    (checked : readOldCaptureReceipt s auth c i arg kept pattern job = some emitted) :
    s.equations[emitted.rawOrdinal]? = none ∧
    emitted.after.equations[emitted.rawOrdinal]? = some ⟨emitted.target,emitted.captured.term⟩ ∧
    (∀ (authors : List Equation) (idx : Nat),
      recoverOldStamp478 s.equations authors ⟨emitted.rawOrdinal,idx⟩ = none) := by
  obtain ⟨_,_,_,_,_,_,_,index⟩ := (exact_old_capture_execution_has_data_only_receipt ..).mp checked
  have lacks : s.equations[emitted.rawOrdinal]? = none := by
    apply List.getElem?_eq_none
    rw [index]
    omega
  exact ⟨lacks,(a_receipt_really_names_the_original_capture_and_the_appended_ordinary_row checked).1,
    fun authors idx => by simp [recoverOldStamp478,lacks]⟩

theorem same_exact_old_compiler_job_after_phase_still_needs_an_authored_position478
    {s : OldRawState478} {done : Nat → Prop} {old : Supported s done}
    {auth : Sources (restriction old)} {c i arg kept pattern job} {emitted : OldCaptureReceipt}
    (checked : readOldCaptureReceipt s auth c i arg kept pattern job = some emitted)
    (authors : List Equation) (idx : Nat) :
    recoverOldStamp478 emitted.after.equations authors ⟨emitted.rawOrdinal,idx⟩ =
      some ⟨emitted.rawOrdinal,idx,⟨emitted.target,emitted.captured.term⟩⟩ ↔
      authors[idx]? = some ⟨emitted.target,emitted.captured.term⟩ := by
  have post := (actual_old_compiler_job_is_a_post_input_ordinal_not_a_same_phase_read478 checked).2.1
  simp [recoverOldStamp478,post]

theorem exact_old_compiler_job_never_changes_its_before_phase_to_after478
    {s : OldRawState478} {done : Nat → Prop} {old : Supported s done}
    {auth : Sources (restriction old)} {c i arg kept pattern job} {emitted : OldCaptureReceipt}
    (checked : readOldCaptureReceipt s auth c i arg kept pattern job = some emitted) :
    s.equations ≠ emitted.after.equations := by
  intro eq
  obtain ⟨none,some,_⟩ := actual_old_compiler_job_is_a_post_input_ordinal_not_a_same_phase_read478 checked
  rw [eq,some] at none
  cases none

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
