import Yulang.GeneralDeclarativeI65I74RecordEndpointsSource422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open GeneralDeclarativeDemand320 (bounds_sound)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeWhere319 (InInterval)
open CommonNominalFullCarrier (Ty Subtype Equivalent record mask subtype_trans)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (sandwich)
open GeneralDeclarativeEndpointRecord336 (mask_below)
open OpenTail414 (openRow)

theorem authored_endpoint_has_exact_record422 {s slot} (r : AuthoredRecord s slot)
    (m : I72.Model) (fit : Models s.core.current.ordinary m.assignment) :
    Equivalent (m.assignment slot).1
      (record r.label (m.assignment r.field).1 (m.assignment r.residual).1) :=
  fit.2 _ r.row

/-- The semantic center is bounded by the exact authored record values.
Neither an equation for the center nor an interpretation of a
not-yet-completed output is supplied as a premise. -/
theorem original_center_between_authored_record_endpoints422 {p} (r : Read p)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    InInterval
      (record r.low.label (m.assignment r.low.field).1 (m.assignment r.low.residual).1)
      (record r.low.label (m.assignment r.high.field).1 (m.assignment r.high.residual).1)
      (m.assignment r.arg.center).1 := by
  have lo := authored_endpoint_has_exact_record422 r.low m fit
  have hi := authored_endpoint_has_exact_record422 r.high m fit
  rw [r.sameLabel] at hi
  have bounds := bounds_sound r.ranged m.assignment fit
  exact ⟨subtype_trans lo.2 bounds.1,subtype_trans bounds.2 hi.1⟩

/-- Both actual interval projections use one and the same model. The
projected value is the true field of the original center value in
that model, not a replacement center or either endpoint. For residual
we claim the transported mask, not unrestricted exact deletion or a
stored symbolic center address absent from the source. -/
theorem actual_field_and_mask_keep_both_authored_record_bounds422 {p} (r : Read p)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    (∃ f, project r.low.label false [] (m.assignment r.arg.center).1 = some f ∧
        InInterval (m.assignment r.low.field).1 (m.assignment r.high.field).1 f) ∧
    InInterval
      (mask [r.low.label] (record r.low.label (m.assignment r.low.field).1 (m.assignment r.low.residual).1))
      (mask [r.low.label] (record r.low.label (m.assignment r.high.field).1 (m.assignment r.high.residual).1))
      (mask [r.low.label] (m.assignment r.arg.center).1) := by
  have b := original_center_between_authored_record_endpoints422 r m fit
  exact ⟨sandwich r.low.label false b.1 b.2,mask_below _ b.1,mask_below _ b.2⟩

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
