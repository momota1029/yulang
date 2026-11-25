import Yulang.GeneralDeclarativeI65I74RecordEndpointsProjectedOutput422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open RecordEndpoints422 (Read AuthoredRecord Locator readAuthoredRecord ProjectedOutput)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open Checker408 (Problem)
open RepeatedCenters421 (retainedAt)

/-- Two independently recorded tightening bounds around the actual
root center. Their common field slot is not an endpoint replacement:
these constraints may narrow an originally strictly wider interval.
They place no equality on the recorded record tails. -/
structure Anchors {p : Problem} (r : Read p) where
  lowerName : Nat
  upperName : Nat
  lowerIsNotCenter : lowerName ≠ r.arg.center
  upperIsNotCenter : upperName ≠ r.arg.center
  lower : AuthoredRecord p.state lowerName
  upper : AuthoredRecord p.state upperName
  lowerLabel : lower.label = r.low.label
  upperLabel : upper.label = r.low.label
  sharedField : upper.field = lower.field
  belowCenter : Bound p.state.core.current.ordinary.normal lowerName r.arg.center
  aboveCenter : Bound p.state.core.current.ordinary.normal r.arg.center upperName

/-- Independent retention evidence for the already fixed output
address; this is a raw equation with exact operands, not new output
selection and not a record equation about the actual center. -/
structure Retained {p : Problem} (r : Read p) where
  anchors : Anchors r
  rowOrdinal : Nat
  atRow : p.state.core.current.ordinary.equations[rowOrdinal]? =
    some ⟨p.root.demand.outputs[r.outIndex].target,.variable anchors.lower.field⟩

structure Wire where
  lowerName : Nat
  upperName : Nat
  lower : Locator
  upper : Locator
  targetRow : Nat

def readAnchoredRetention423 {p : Problem} (r : Read p) (w : Wire) : Option (Retained r) := do
  let raw := p.state.core.current.ordinary
  if paths : (w.lowerName,r.arg.center) ∈ raw.normal.intervals ∧
      (r.arg.center,w.upperName) ∈ raw.normal.intervals ∧
      w.lowerName ≠ r.arg.center ∧ w.upperName ≠ r.arg.center then
    let lower ← readAuthoredRecord p.state w.lowerName w.lower
    let upper ← readAuthoredRecord p.state w.upperName w.upper
    if same : lower.label = r.low.label ∧ upper.label = r.low.label ∧ upper.field = lower.field then
      let kept ← retainedAt raw w.targetRow
        ⟨p.root.demand.outputs[r.outIndex].target,.variable lower.field⟩
      pure ⟨⟨w.lowerName,w.upperName,paths.2.2.1,paths.2.2.2,lower,upper,
        same.1,same.2.1,same.2.2,.interval paths.1,.interval paths.2.1⟩,
        w.targetRow,kept.down⟩
    else none
  else none

theorem retained_rhs_row_is_at_the_exact_original_target423 {p : Problem} {r : Read p}
    (kept : Retained r) :
    (⟨p.root.demand.outputs[r.outIndex].target,.variable kept.anchors.lower.field⟩ : Equation) ∈
      p.state.core.current.ordinary.equations :=
  List.mem_of_getElem? kept.atRow

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
