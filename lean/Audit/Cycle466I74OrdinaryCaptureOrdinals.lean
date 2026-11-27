import Yulang.GeneralDeclarativeI65I74OrdinaryCaptureOrdinals466
import Yulang.GeneralDeclarativeNestedExample332
namespace Yulang.OrdinaryOccurrenceStamp466
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeNestedExample332 (state uses)
open GeneralDeclarativeOpaqueNominal328 (point)
private def keysAt (w : Option (Nat × Nat × Occurrence)) := w.map
  (fun o => (o.1,o.2.1,o.2.2.binder))
theorem real_two_row_allocation_identifies_the_literal_capture_indices :
    keysAt (existingCaptureJob state (point 0) [] (uses .actual) 0) = some (16,2,4) ∧
    keysAt (existingCaptureJob state (point 0) [] (uses .actual) 1) = some (17,3,1) ∧
    existingCaptureJob state (point 0) [] (uses .actual) 2 = none := ⟨rfl,rfl,rfl⟩

#print axioms job_ordinals_preserve_exact_existing_rhs_sequence
#print axioms tagged_job_is_the_literal_input_capture_and_not_a_variable
#print axioms actual_old_numbered_row_uses_its_consecutive_raw_target
#print axioms successful_ordinal_reads_original_capture_and_allocated_row
#print axioms no_created_ordinary_row_is_lost_by_the_ordinal_adapter
#print axioms real_two_row_allocation_identifies_the_literal_capture_indices
#print axioms actual_legacy_assembly_places_the_old_ordinary_inputs_before_named_jobs
#print axioms actual_allocation_receipt_links_exact_old_capture_to_exact_new_raw_ordinal
end Yulang.OrdinaryOccurrenceStamp466
