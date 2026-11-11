import Yulang.GeneralDictionaryEquationRecording
import Yulang.GeneralDictionaryEquationExamples
import Yulang.CommonRigidHeadInspection

/-!
# Non-vacuous recording and incompatible-output regressions

These are equation transaction tests, not a new restricted role classifier.
-/
namespace Yulang.GeneralDictionaryRecordingExamples
open GeneralSourceState (Models Assignment)
open GeneralDictionaryStateEquations
open GeneralDictionaryEquationRecording
open GeneralDictionaryEquationExamples

abbrev next := record located

theorem automatically_stored : Recorded (relocation located) := record_recorded located

theorem nonvacuous : Models next assignment :=
  (record_models located assignment).mpr ⟨models, recorded_holds located recorded assignment models⟩

theorem same_models (model : Assignment) : Models next model ↔ Models state model :=
  record_conservative located (recorded_holds located recorded) model

theorem source_ids_retained : next.source ⟨0, by decide⟩ = 10 ∧ next.rowSource ⟨0, by decide⟩ = 20 := ⟨rfl, rfl⟩

theorem repeated_outputs_retained : demand.outputs.length = 2 ∧ (atoms located).length = 6 :=
  ⟨rfl, rfl⟩

abbrev incompatible : Located state demand := { located with output := fun _ => .base .str }

/-- A contradictory associated RHS does not become a successful dictionary just
because its equations have been recorded. No assignment satisfies the update. -/
theorem incompatible_no_model : ¬ ∃ model, Models (record incompatible) model := by
  rintro ⟨model, valid⟩
  obtain ⟨old, added⟩ := (record_models incompatible model).mp valid
  have first := (recorded_holds located recorded model old).2 ⟨0, by decide⟩
  have last := added.2 ⟨0, by decide⟩
  change Common.Equivalent (model 10).1 (.base .int) at first
  change Common.Equivalent (model 10).1 (.base .str) at last
  have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp
    (Common.subtype_trans first.2 last.1)
  cases impossible

end Yulang.GeneralDictionaryRecordingExamples
