import Yulang.GeneralDeclarativeI65I74ProjectedRetentionChannel423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open RecordEndpoints422 (Read ProjectedOutput readEndpoints422 readProjectedOutput422)
open GeneralDeclarativeHead320 (Equation)
open CommonNominalFullCarrier (Ty Equivalent)
open Checker408 (Problem)

inductive ReceiptWire where
  | shared (w : Wire)
  | directed (w : Wire)
  | located (w : PathWire)
  | requiredChannel (w : ChannelWire)

inductive RetentionEvidence {p : Problem} (r : Read p) where
  | transported : TransportedRetained r → RetentionEvidence r
  | required : RequiredOnlyRetained r → RetentionEvidence r

def readReceipt423 {p : Problem} (r : Read p) : ReceiptWire → Option (RetentionEvidence r)
  | .shared w => (readAnchoredRetention423 r w).map (fun w => .transported w.asTransported423)
  | .directed w => (readTransportedRetention423 r w).map .transported
  | .located w => (readRetentionPaths423 r w).map .transported
  | .requiredChannel w => (readRequiredChannelRetention423 r w).map .required

structure PreparedWrite (p : Problem) where
  original : Read p
  typed : ProjectedOutput original
  retained : RetentionEvidence original

structure PrepareWire where
  authored : RecordEndpoints422.Wire
  retention : ReceiptWire

/-- This operation prepares a value-side retention fact, *not* a
checker accepting a Result. It cannot manufacture HeadMeaning,
classification or dictionary evidence. In particular there is no
argument containing a claimed verdict, desired result type or model. -/
def readRetainedPickWrite423 (p : Problem) (w : PrepareWire) :
    Option (PreparedWrite p) := do
  let original ← readEndpoints422 p w.authored
  let typed ← readProjectedOutput422 original
  let retained ← readReceipt423 original w.retention
  pure ⟨original,typed,retained⟩

def RetentionEvidence.rowAt {p} {r : Read p} (w : RetentionEvidence r) : Nat × Nat :=
  match w with
  | .transported c => (c.rowOrdinal,c.fieldAddress)
  | .required c => (c.targetOrdinal,c.field)

theorem exact_literal_target_row_of_prepared_write423 {p : Problem} (r : PreparedWrite p) :
    let position := r.retained.rowAt
    p.state.core.current.ordinary.equations[position.1]? =
      some ⟨p.root.demand.outputs[r.original.outIndex].target,.variable position.2⟩ := by
  cases r with
  | mk source value kept =>
    cases kept with
    | transported earlier => exact earlier.stored
    | required earlier => exact earlier.atTarget

theorem prepared_write_keeps_original_occurrence_ordinal_and_target423
    {p : Problem} (r : PreparedWrite p) (m : I72.Model) (fit : I72.Fits p.state m) :
    ∃ value : Ty,
      r.typed.actualRightValue m =
        some (p.root.occurrence,r.original.ordinal,r.original.outIndex.val,
          p.root.demand.outputs[r.original.outIndex].target,value) ∧
      Equivalent (m.assignment p.root.demand.outputs[r.original.outIndex].target).1 value := by
  cases r with
  | mk org rhs cert =>
    cases cert with
    | transported w => exact original_projected_B6_fixed_target_survives_distinct_logical_names423 rhs w m fit
    | required w => exact original_B6_projected_write_retained_even_without_optional_agreement423 rhs w m fit

theorem read_retained_Pick_write_sound423
    {p : Problem} {w : PrepareWire} {read : PreparedWrite p}
    (_ : readRetainedPickWrite423 p w = some read) :
    (let pos := read.retained.rowAt
     p.state.core.current.ordinary.equations[pos.1]? =
       some ⟨p.root.demand.outputs[read.original.outIndex].target,.variable pos.2⟩) ∧
    ∀ (m : I72.Model), I72.Fits p.state m → ∃ value : Ty,
      read.typed.actualRightValue m =
        some (p.root.occurrence,read.original.ordinal,read.original.outIndex.val,
          p.root.demand.outputs[read.original.outIndex].target,value) ∧
      Equivalent (m.assignment p.root.demand.outputs[read.original.outIndex].target).1 value :=
  ⟨exact_literal_target_row_of_prepared_write423 read,prepared_write_keeps_original_occurrence_ordinal_and_target423 read⟩

/-- End-to-end positive preparatory meaning keeps *all* original
capture coordinates and both semantic field/mask intervals as well
as the fixed write. In the required-only route, the optional value
remains independently observed rather than forced to equal it. -/
theorem prepared_write_preserves_full_projected_capture_and_actual_value423
    {p : Problem} (prepared : PreparedWrite p) (m : I72.Model) (fit : I72.Fits p.state m) :
    ∃ evidence : RecordEndpoints422.ProjectedRecordChannels prepared.original m,
      prepared.typed.actualRightValue m =
        some (p.root.occurrence,prepared.original.ordinal,prepared.original.outIndex.val,
          p.root.demand.outputs[prepared.original.outIndex].target,evidence.required) ∧
      Equivalent (m.assignment p.root.demand.outputs[prepared.original.outIndex].target).1 evidence.required := by
  obtain ⟨channels⟩ := RecordEndpoints422.same_model_endpoints_support_both_projected_channels422
    prepared.original m fit.1.1
  refine ⟨channels,RecordEndpoints422.original_B6_binder_yields_required_projection_and_exact_addresses422
    prepared.typed m channels,?_⟩
  cases held : prepared.retained with
  | transported r => exact (transported_target_agrees_with_actual_field_channels423 r m fit.1.1 channels).1
  | required r => exact retained_target_can_equal_required_projection_without_collapsing_optional423 r m fit.1.1 channels

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
