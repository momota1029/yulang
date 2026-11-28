import Yulang.GeneralDeclarativeI65I74G04ProducerMeaning479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479

open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (StepWire)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)

theorem exact_single_visibility_forces_the_old_filtered_index_zero479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (event : TypedInput p gd pos rel) :
    event.head.orig.location.visibleOrdinal = 0 := by
  have h := event.head.orig.actualVisible
  rw [event.single] at h
  cases x : event.head.orig.location.visibleOrdinal <;> simp_all

theorem single_input_reifies_a_route_even_without_any_producer479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (event : TypedInput p gd pos rel) :
    ∃ w : RouteWire n, ExactSelectedRoute event w ∧
      readRoute p gd pos rel w = some event.report := by
  obtain ⟨w,h₁,h₂,h₃,h₄,h₅,replay⟩ :=
    materialize_independent_geometry_without_issuing_a_source479 event
      (exact_single_visibility_forces_the_old_filtered_index_zero479 event)
  exact ⟨w,⟨h₁,h₂,h₃,h₄,h₅⟩,replay⟩

end Yulang.GeneralDeclarativeI65.I72.Producer479
