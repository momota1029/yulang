import Yulang.GeneralWhereVersionStoredRow317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 52000000
namespace Yulang.GeneralWhereVersionRecordedReuse317
open GeneralLiveCompoundRegistry316 (registry declaration otherChild boundary_checked)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralWhereVersionRootReport317 (plan same)
open GeneralWhereVersionCase317 (expr lowerRow upperRow)
open GeneralWhereVersionInstall317 (fixed Models)
open GeneralWhereVersionStoredRow317 (Endpoint same_target_iff)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)

theorem stored_lower : Endpoint rootPlan .lower otherChild 0 lowerRow :=
  ⟨⟨List.mem_singleton_self _,⟨.variant 0 (.var 0),rfl,rfl⟩,rfl⟩,rfl⟩

theorem stored_upper : Endpoint rootPlan .upper otherChild 0 upperRow :=
  ⟨⟨List.mem_singleton_self _,⟨.variant 0 (.var 0),rfl,rfl⟩,rfl⟩,rfl⟩

theorem present_lower : Endpoint plan .lower otherChild 0 lowerRow :=
  ⟨⟨List.mem_singleton_self _,⟨.variant 0 (.var 0),rfl,rfl⟩,rfl⟩,
    GeneralWhereVersionReuse317.exact_addresses.1.symm⟩

theorem present_upper : Endpoint plan .upper otherChild 0 upperRow :=
  ⟨⟨List.mem_singleton_self _,⟨.variant 0 (.var 0),rfl,rfl⟩,rfl⟩,
    GeneralWhereVersionReuse317.exact_addresses.2.symm⟩

/-- Both obligations on re-read are witnessed by rows actually present in
the installed new-format journal, not just by slot presence or an
independently chosen satisfying assignment. -/
theorem from_recorded_rows (m : Assignment) (valid : Models fixed m) :
    lowerRow.Holds (variables plan m) m ∧ upperRow.Holds (variables plan m) m := by
  have stored := valid.2 rootPlan (List.mem_singleton_self _)
  have rows := GeneralWhereVersionCase317.rows
  have lower : lowerRow ∈ (GeneralWhereVersionCompiler317.schema rootPlan).equations :=
    rows.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have upper : upperRow ∈ (GeneralWhereVersionCompiler317.schema rootPlan).equations :=
    rows.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have checked : GeneralDeclarations.Checked registry :=
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled boundary_checked).2
  refine ⟨?_,?_⟩
  · exact (same_target_iff checked same.registry same.interpretation same.seed
      (List.mem_cons_self (a := declaration)) (List.mem_cons_self (a := declaration))
      stored_lower present_lower rfl m).mp (stored.1.rows _ lower)
  · exact (same_target_iff checked same.registry same.interpretation same.seed
      (List.mem_cons_self (a := declaration)) (List.mem_cons_self (a := declaration))
      stored_upper present_upper rfl m).mp (stored.1.rows _ upper)

end Yulang.GeneralWhereVersionRecordedReuse317
