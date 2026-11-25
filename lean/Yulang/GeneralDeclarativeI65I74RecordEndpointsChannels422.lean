import Yulang.GeneralDeclarativeI65I74RecordEndpointsRelative422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeWhere319 (InInterval)
open CommonNominalFullCarrier (Ty Equivalent record mask)
open GeneralDeclarativeRecordIntervals330 (sandwich)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeEndpointRecord336 (mask_below)

/-- A model-local head certificate can keep the two typed channels
without manufacturing a record constructor or extra name at the
actual center. This is only an independent proposed evidence cut;
it is not a new constructor of the frozen SourceHead. -/
structure ProjectedRecordChannels {p} (r : Read p) (m : I72.Model) where
  required : Ty
  optional : Ty
  atRequired : project r.low.label false [] (m.assignment r.arg.center).1 = some required
  atOptional : project r.low.label true [] (m.assignment r.arg.center).1 = some optional
  requiredBounds : InInterval (m.assignment r.low.field).1 (m.assignment r.high.field).1 required
  optionalBounds : InInterval (m.assignment r.low.field).1 (m.assignment r.high.field).1 optional
  residualBounds : InInterval
    (mask [r.low.label] (record r.low.label (m.assignment r.low.field).1 (m.assignment r.low.residual).1))
    (mask [r.low.label] (record r.low.label (m.assignment r.high.field).1 (m.assignment r.high.residual).1))
    (mask [r.low.label] (m.assignment r.arg.center).1)

/-- Every fitting *unchanged* model admits the two-channel semantic
interval and masked residual, even when no equivalent literal full
record exists at the actual center. -/
theorem same_model_endpoints_support_both_projected_channels422 {p}
    (r : Read p) (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    Nonempty (ProjectedRecordChannels r m) := by
  have interval := original_center_between_authored_record_endpoints422 r m fit
  obtain ⟨field,req,lower,upper⟩ := sandwich r.low.label false interval.1 interval.2
  obtain ⟨other,opt,lower',upper'⟩ := sandwich r.low.label true interval.1 interval.2
  exact ⟨⟨field,other,req,opt,⟨lower,upper⟩,⟨lower',upper'⟩,
    ⟨mask_below _ interval.1,mask_below _ interval.2⟩⟩⟩

/-- The exact divide: channel-wise capture exists unconditionally
under the old fit; the stronger literal peel exists precisely where
the two projections coincide. -/
theorem projected_certificate_reassembles_exact_record_iff_its_channels_agree422 {p}
    (r : Read p) (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment)
    (a : ProjectedRecordChannels r m) :
    (∃ field tail, Equivalent (m.assignment r.arg.center).1 (record r.low.label field tail)) ↔
      Equivalent a.required a.optional := by
  have interval := original_center_between_authored_record_endpoints422 r m fit
  exact GeneralDeclarativeRecordReconstruct330.exact interval.1 interval.2 a.atRequired a.atOptional

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
