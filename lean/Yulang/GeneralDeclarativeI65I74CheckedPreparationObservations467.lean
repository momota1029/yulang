import Yulang.GeneralDeclarativeI65I74CheckedPreparedRetraction467
import Yulang.GeneralDeclarativeI65I74PreparationTagScope467

namespace Yulang.GeneralDeclarativeI65.I72.CheckedPreparationObservations467
open GeneralDeclarativeI65.I72.CheckedPreparedRetraction467
open GeneralDeclarativeI65.I72.PreparationFootprint467
open GeneralDeclarativeI65.I72.PreparationTagScope467
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeLowerKnown321 (Knows)

private abbrev Raw := GeneralDeclarativeHead320.State

def checkOrdinaryObservationRetraction (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) : Bool :=
  checkPreparedRetraction s t wire root &&
    (tagFootprint s).all (fun n => decide (explicitProject wire n = n))

theorem same_phase_retention_wire_checks_both_original_footprints
    (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) :
    checkOrdinaryObservationRetraction s t wire root = true ↔
      ExactPreparedRetraction s t wire root ∧
      ∀ n ∈ tagFootprint s, explicitProject wire n = n := by
  simp only [checkOrdinaryObservationRetraction,Bool.and_eq_true,
    exact_finite_preparation_retraction_check,List.all_eq_true,decide_eq_true_eq]

theorem checked_original_query_preserves_raw_cycles_and_known_constructors
    {s t : Raw} {wire : List (Nat × Nat)} {root : Nat}
    (read : checkOrdinaryObservationRetraction s t wire root = true) :
    (AliasCycle s (observed s) root ↔ AliasCycle t (observed t) root) ∧
      (∀ tag, Knows s root tag ↔ Knows t root tag) := by
  have part := Bool.and_eq_true_iff.mp read
  obtain ⟨rows,retraction,pinned⟩ := finite_retraction_certificate_supplies_exact_generators part.1
  apply finite_combined_graph_and_tag_scope_preserves_K2_and_knowledge retraction rows
  exact List.all_eq_true.mpr (fun n present => by
    rw [List.mem_append] at present
    cases present with
    | inl live => exact List.all_eq_true.mp pinned _ live
    | inr tag => exact List.all_eq_true.mp part.2 _ tag)

end Yulang.GeneralDeclarativeI65.I72.CheckedPreparationObservations467
