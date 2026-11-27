import Yulang.GeneralDeclarativeI65I74ReadOldCaptureReceipt466
import Yulang.GeneralDeclarativeNestedExample332
import Yulang.GeneralDeclarativeNestedIndex332
namespace Yulang.C466WrittenBinderCoordinates.OldCaptureActual466
open GeneralDeclarativeNestedExample332 (state pat interpretation indexed innerResidual outerResidual)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose)

private def tiny (r : OldCaptureReceipt) : Nat × Nat × Nat × List Pose × Nat :=
  (r.target,r.rawOrdinal,r.captureOrdinal,r.written,r.captured.binder)
private noncomputable def actual (job : Nat) :=
  (readOldCaptureReceipt state (indexed (fun _ => False)) constructors interpretation (point 0) [] pat job).map tiny

theorem checked_c332_run_generates_two_exact_capture_receipts :
    actual 0 = some (16,3,2,[.payload,.variant,.app 1,.tail],4) ∧
    actual 1 = some (17,4,3,[.tail],1) ∧
    actual 2 = none := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

private def sourceRows : GeneralDeclarativeNestedView332.Sources state :=
  GeneralDeclarativeNestedIndex332.ofRows state.equations (fun _ h => h)

private def runtime (job : Nat) :=
  (readOldCaptureReceipt state sourceRows constructors interpretation (point 0) [] pat job).map tiny

/-- info: [true, true, true] -/
#guard_msgs in
#eval [decide (runtime 0 = some (16,3,2,[.payload,.variant,.app 1,.tail],4)),
  decide (runtime 1 = some (17,4,3,[.tail],1)), (runtime 2).isNone]

#print axioms checked_c332_run_generates_two_exact_capture_receipts
end Yulang.C466WrittenBinderCoordinates.OldCaptureActual466
