import Yulang.GeneralDictionaryFinishedEvidence
import Yulang.GeneralNominalNonpointInspectionExamples

/-! Finished nested nominal/scalar inspection can have an unoccupied descriptor
footprint. This nonpoint, nonempty-model example separates the new theorem from
the earlier sufficient occupancy condition. -/
namespace Yulang.GeneralDictionaryFinishedInspectionExamples
open GeneralDictionaryInspectionTransport GeneralDictionaryInspectionLocality
open GeneralDictionaryFinishedInspection
open GeneralNominalRecursiveInspection
open GeneralNominalNonpointInspectionExamples

abbrev query : GeneralNominalInspection.Query := .nominal 0 [.scalar .int]
abbrev bounds : GeneralNominalInspection.Bounds state := (0,0)

theorem nested_finished : Finished (inspect state query bounds none) := by
  unfold Finished
  decide +kernel

theorem footprint_not_occupied :
    ¬ (∀ slot ∈ footprint state query bounds, ∃ descriptor, state.nominals slot = some descriptor) := by
  intro occupied
  obtain ⟨descriptor,recorded⟩ := occupied (2 : Fin 4) (by decide +kernel)
  have absent : state.nominals (2 : Fin 4) = none := rfl
  rw [absent] at recorded
  cases recorded

theorem nested_survives (next : Observation state) (view : next.view = state.view)
    (refinement : GeneralNominalRefinements.Refines state (reobserve context next).state) :
    inspect (reobserve context next).state query bounds none =
      transferReport context next (inspect state query bounds none) :=
  inspect_finished context next view refinement query bounds none nested_finished

theorem nonvacuous_nested : GeneralNominalState.Models state model ∧
    Finished (inspect state query bounds none) ∧
    ¬ (∀ slot ∈ footprint state query bounds, ∃ descriptor, state.nominals slot = some descriptor) :=
  ⟨state_models,nested_finished,footprint_not_occupied⟩

end Yulang.GeneralDictionaryFinishedInspectionExamples
