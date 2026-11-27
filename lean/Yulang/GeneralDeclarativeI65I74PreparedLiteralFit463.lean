import Yulang.GeneralDeclarativeI65I74LiteralIndexedFit463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open EligibleFieldStart461 WrittenPattern460 PhysicalVisit463
open WrittenPattern460.PhysicalOrigin (Hit OriginalWalk route_occurrences_exact locateRoute atSource
  whole_route_is_literal_and_preserves_exact_coordinates)

theorem any_located_literal_candidate_zips_with_its_identical_native_rows
    {input : Input} {w : PreparedWire input} {l : LocatedReport}
    (read : readLocated w = some l) (m : I72.Model) (fit : I72.FitsFull input.problem.state m) :
    ∃ a : EligibleStart input.problem.old, PreparedSource input.checked a ∧
      exactReport a.anchor l.report.path l.report.terminal = l.report ∧
      l.literal ≠ [] ∧
      ∀ pos term, (pos,term) ∈ l.literal →
        atSource a.original pos = some term ∧
        LiteralIndexedFit input.problem.old.state.core m (fun _ => queryKeys input.problem.old.state.core)
          a.original a.argument.lower a.query l.report.path l.equations pos l.report.terminal term l.mark := by
  have actual := successful_located_witness_preserves_every_existing_authentic_origin read
  obtain ⟨a,last,ready,report,model,nonempty,source,_⟩ :=
    exact_located_original_paths_and_rows_hold_in_every_same_fit actual m fit
  refine ⟨a,ready,report,nonempty,?_⟩
  intro pos term inReport
  have hits := same_read_returns_every_literal_position_of_its_same_original_input read (a := a)
  have inRoute := inReport
  rw [hits] at inRoute
  have originals := route_occurrences_exact.mp inRoute
  rw [normalized_of_original] at model
  exact ⟨(source _ _ inReport).1,(coincide_hop_by_hop_in_the_same_raw_row_and_original originals model).1⟩

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
