import Yulang.GeneralDeclarativeI65I74OldCompilerPhaseBoundary478
import Yulang.GeneralDeclarativeNestedExample332
import Yulang.GeneralDeclarativeNestedIndex332
namespace Yulang.C466WrittenBinderCoordinates.OldCapturePhaseActual478
open GeneralDeclarativeNestedExample332 (state pat interpretation indexed innerResidual outerResidual)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose)


open GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeHead320 (Equation)

private noncomputable def originalRun478 :=
  readOldCaptureReceipt state (indexed (fun _ => False)) constructors interpretation (point 0) [] pat 0

private noncomputable def oldReceipt478 : OldCaptureReceipt := originalRun478.get (by decide +kernel)

theorem actual_old_compiler_job_has_no_before_snapshot_row_at_its_real_ordinal478 :
    oldReceipt478.rawOrdinal = 3 ∧ oldReceipt478.target = 16 ∧
    state.equations[3]? = none ∧
    oldReceipt478.after.equations[3]? = some ⟨16,oldReceipt478.captured.term⟩ ∧
    ∀ (authors : List Equation) (i : Nat), recoverOldStamp478 state.equations authors ⟨3,i⟩ = none := by
  have actual : originalRun478 = some oldReceipt478 := by apply Option.eq_some_of_isSome
  have exact := actual_old_compiler_job_is_a_post_input_ordinal_not_a_same_phase_read478 actual
  have ordinal : oldReceipt478.rawOrdinal = 3 := by decide +kernel
  have target : oldReceipt478.target = 16 := by decide +kernel
  simpa [ordinal,target] using And.intro ordinal (And.intro target exact)

private def sourceRows : GeneralDeclarativeNestedView332.Sources state :=
  GeneralDeclarativeNestedIndex332.ofRows state.equations (fun _ h => h)

private def phaseTests478 : Option (Nat × Nat × Bool × Bool × Option SourceIndexPair478) := do
  let emitted ← readOldCaptureReceipt state sourceRows constructors interpretation (point 0) [] pat 0
  let authors : List Equation := [⟨emitted.target,emitted.captured.term⟩]
  pure (emitted.rawOrdinal,emitted.target,
    (recoverOldStamp478 state.equations authors ⟨emitted.rawOrdinal,0⟩).isNone,
    (recoverOldStamp478 emitted.after.equations [] ⟨emitted.rawOrdinal,0⟩).isNone,
    (recoverOldStamp478 emitted.after.equations authors ⟨emitted.rawOrdinal,0⟩).map StampedRead.indexPair478)

/-- info: true -/
#guard_msgs in
#eval decide (phaseTests478 = some (3,16,true,true,some ⟨3,0⟩))

#print axioms actual_old_compiler_job_has_no_before_snapshot_row_at_its_real_ordinal478
end Yulang.C466WrittenBinderCoordinates.OldCapturePhaseActual478
