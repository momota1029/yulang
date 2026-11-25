import Yulang.GeneralDeclarativeI65I75EndpointHeadPremises423
import Yulang.GeneralDeclarativeI65I74ProjectedRetentionRead423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open RecordEndpoints422 (AuthoredRecord Read)
open Checker408 (Problem)

def lowerOriginal423 {p : Problem} (r : Read p) :
    EndpointHead423.Original p.state.core r.arg.lower r.low.label :=
  ⟨r.low.field,r.low.residual,r.low.original,r.low.owned,r.low.slotEq,r.low.writtenForm,r.low.row⟩

def upperOriginal423 {p : Problem} (r : Read p) :
    EndpointHead423.Original p.state.core r.arg.upper r.low.label := by
  rw [← r.sameLabel]
  exact ⟨r.high.field,r.high.residual,r.high.original,r.high.owned,r.high.slotEq,
    r.high.writtenForm,r.high.row⟩

def endpointInputs423 {p : Problem} (r : Read p) :
    EndpointHead423.Inputs p.state.core r.arg r.low.label :=
  ⟨lowerOriginal423 r,upperOriginal423 r,r.ranged⟩

/-- The actual original source reader supplies the premises for the
future SourceHead constructor, with unchanged target and same model.
This theorem is preparation, not a new classifier or check result. -/
theorem checked_preparation_supplies_I75_head_and_actual_target423 {p : Problem} {wire data}
    (read : readRetainedPickWrite423 p wire = some data)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    Nonempty (EndpointHead423.Inputs p.state.core data.original.arg data.original.low.label) ∧
    EndpointHead423.Meaning (endpointInputs423 data.original) m ∧
    (∃ value, data.typed.actualRightValue m =
        some (p.root.occurrence,data.original.ordinal,data.original.outIndex.val,
          p.root.demand.outputs[data.original.outIndex].target,value) ∧
      CommonNominalFullCarrier.Equivalent
        (m.assignment p.root.demand.outputs[data.original.outIndex].target).1 value) :=
  ⟨⟨endpointInputs423 data.original⟩,
    EndpointHead423.source_endpoints_have_projected_meaning423 (endpointInputs423 data.original) m fit,
    (read_retained_Pick_write_sound423 read).2 m fit⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
