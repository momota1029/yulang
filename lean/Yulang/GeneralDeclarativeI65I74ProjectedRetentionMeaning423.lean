import Yulang.GeneralDeclarativeI65I74ProjectedRetentionSource423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open RecordEndpoints422 (Read ProjectedOutput ProjectedRecordChannels
  authored_endpoint_has_exact_record422 same_model_endpoints_support_both_projected_channels422
  original_B6_binder_yields_required_projection_and_exact_addresses422)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeBounds319 (bound_sound)
open CommonNominalFullCarrier (Ty record Equivalent subtype_trans)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open Checker408 (Problem)

theorem actual_root_is_sandwiched_by_retained_field_anchors423 {p : Problem} {r : Read p}
    (b : Anchors r) (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    InInterval
      (record r.low.label (m.assignment b.lower.field).1 (m.assignment b.lower.residual).1)
      (record r.low.label (m.assignment b.lower.field).1 (m.assignment b.upper.residual).1)
      (m.assignment r.arg.center).1 := by
  have lo := authored_endpoint_has_exact_record422 b.lower m fit
  have hi := authored_endpoint_has_exact_record422 b.upper m fit
  rw [b.lowerLabel] at lo
  rw [b.upperLabel,b.sharedField] at hi
  exact ⟨subtype_trans lo.2 (bound_sound m.assignment fit.1 b.belowCenter),
    subtype_trans (bound_sound m.assignment fit.1 b.aboveCenter) hi.1⟩

/-- Independent ordinary row soundness pins the *actual* output
projection in the original model. In contrast to freezing both
original authored endpoints, only these tighter anchors need a
common field. No equality of either pair of tails is used. -/
theorem retained_target_observes_both_actual_projection_channels423 {p : Problem} {r : Read p}
    (kept : Retained r) (m : I72.Model)
    (fit : Models p.state.core.current.ordinary m.assignment)
    (actual : ProjectedRecordChannels r m) :
    Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 actual.required ∧
    Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 actual.optional := by
  have center := actual_root_is_sandwiched_by_retained_field_anchors423 kept.anchors m fit
  have target : Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1
      (m.assignment kept.anchors.lower.field).1 :=
    fit.2 _ (retained_rhs_row_is_at_the_exact_original_target423 kept)
  exact ⟨eqv_trans target
      ⟨projected_below r.low.label false (direct ..) actual.atRequired center.1,
       projected_below r.low.label false actual.atRequired (direct ..) center.2⟩,
    eqv_trans target
      ⟨projected_below r.low.label true (direct ..) actual.atOptional center.1,
       projected_below r.low.label true actual.atOptional (direct ..) center.2⟩⟩

/-- The exact RHS evaluation and the separate fixed target equality
hold together for *every* fit of the same state. This is a fact
about the actual projected body and output address, not an Event,
SourceHead, or changed dictionary soundness theorem. -/
theorem original_projected_B6_write_is_retained_at_its_exact_target423 {p : Problem} {r : Read p}
    (rhs : ProjectedOutput r) (kept : Retained r) (m : I72.Model)
    (fit : I72.Fits p.state m) :
    ∃ value : Ty,
      rhs.actualRightValue m =
        some (p.root.occurrence,r.ordinal,r.outIndex.val,p.root.demand.outputs[r.outIndex].target,value) ∧
      Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 value := by
  obtain ⟨actual⟩ := same_model_endpoints_support_both_projected_channels422 r m fit.1.1
  exact ⟨actual.required,
    original_B6_binder_yields_required_projection_and_exact_addresses422 rhs m actual,
    (retained_target_observes_both_actual_projection_channels423 kept m fit.1.1 actual).1⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
