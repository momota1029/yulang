import Yulang.GeneralDeclarativeWitnessNativeValue360
import Yulang.GeneralDeclarativeI65I74BeforeCaptureEvent475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Compiled compile)
open RetainedFull445 (FullProblem)

/-- The native producer's original output index is part of its
compiler receipt. It cannot be supplied by a different consumer
that made no associated output request. -/
theorem genuine_native_write_has_a_literal_requested_output478
    {e frame d layout modes wire version} {ready : Prepared e frame d layout}
    (issued : Compiled ready modes wire version) :
    ∃ out, d.outputs[wire.ordinal]? = some out ∧ out.target = wire.target :=
  ⟨issued.supplied.requested,issued.supplied.indexed,issued.supplied.fixed⟩

theorem native_write_cannot_be_issued_by_this_output_free_input_event478
    {p : FullProblem} {frame layout modes wire version}
    {ready : Prepared p.old.state.core.current.environment frame p.old.root.demand layout}
    (empty : p.old.root.demand.outputs = []) :
    compile ready modes wire version = none := by
  cases ran : compile ready modes wire version with
  | none => rfl
  | some built =>
    obtain ⟨out,exact,_⟩ := genuine_native_write_has_a_literal_requested_output478 built
    simp [empty] at exact

theorem any_successful_native_owner_of_an_output_free_consumer_is_not_its_requested_output478
    {p : FullProblem} {frame d layout modes wire version}
    {ready : Prepared p.old.state.core.current.environment frame d layout}
    (empty : p.old.root.demand.outputs = [])
    (compiled : Compiled ready modes wire version) :
    d ≠ p.old.root.demand := by
  intro same
  obtain ⟨out,atOut,_⟩ := genuine_native_write_has_a_literal_requested_output478 compiled
  have actualEmpty : d.outputs = [] := by simpa [same] using empty
  simp [actualEmpty] at atOut

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
