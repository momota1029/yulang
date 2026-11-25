import Yulang.GeneralDeclarativeI65I74ProjectedRetentionMeaning423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open RecordEndpoints422 (Read ProjectedOutput ProjectedRecordChannels AuthoredRecord Locator readAuthoredRecord
  authored_endpoint_has_exact_record422 same_model_endpoints_support_both_projected_channels422
  original_B6_binder_yields_required_projection_and_exact_addresses422)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeWhere319 (InInterval)
open CommonNominalFullCarrier (Ty Equivalent record subtype_trans)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open Checker408 (Problem)

structure RecordBracket {p : Problem} (r : Read p) where
  lowerName : Nat
  upperName : Nat
  lowerNotCenter : lowerName ≠ r.arg.center
  upperNotCenter : upperName ≠ r.arg.center
  lower : AuthoredRecord p.state lowerName
  upper : AuthoredRecord p.state upperName
  lowerLabel : lower.label = r.low.label
  upperLabel : upper.label = r.low.label
  belowCenter : Bound p.state.core.current.ordinary.normal lowerName r.arg.center
  aboveCenter : Bound p.state.core.current.ordinary.normal r.arg.center upperName

/-- The stored result expression can name a *different* original
coordinate from either known field. The two ordinary directional
witnesses, not name equality or a supplied model, prove retention. -/
structure TransportedRetained {p : Problem} (r : Read p) where
  bracket : RecordBracket r
  fieldAddress : Nat
  rowOrdinal : Nat
  stored : p.state.core.current.ordinary.equations[rowOrdinal]? =
    some ⟨p.root.demand.outputs[r.outIndex].target,.variable fieldAddress⟩
  toLower : Bound p.state.core.current.ordinary.normal fieldAddress bracket.lower.field
  fromUpper : Bound p.state.core.current.ordinary.normal bracket.upper.field fieldAddress

def readDirected {p : Problem} (a b : Nat) :
    Option (PLift (Bound p.state.core.current.ordinary.normal a b)) :=
  if same : a = b then some ⟨same ▸ .refl a⟩
  else if found : (a,b) ∈ p.state.core.current.ordinary.normal.intervals then
    some ⟨.interval found⟩
  else none

/-- Keep the earlier wire layout: the retained *row* determines its
RHS address. There is no slot in the locator for a caller-supplied
replacement field name or output target. -/
def readTransportedRetention423 {p : Problem} (r : Read p) (w : Wire) :
    Option (TransportedRetained r) := do
  if sep : w.lowerName ≠ r.arg.center ∧ w.upperName ≠ r.arg.center then
    let lower ← readAuthoredRecord p.state w.lowerName w.lower
    let upper ← readAuthoredRecord p.state w.upperName w.upper
    let lo ← readDirected (p := p) w.lowerName r.arg.center
    let hi ← readDirected (p := p) r.arg.center w.upperName
    if same : lower.label = r.low.label ∧ upper.label = r.low.label then
      match kept : p.state.core.current.ordinary.equations[w.targetRow]? with
      | some ⟨left,.variable right⟩ =>
        if original : left = p.root.demand.outputs[r.outIndex].target then
          let belowPayload ← readDirected (p := p) right lower.field
          let into ← readDirected (p := p) upper.field right
          have atRow : p.state.core.current.ordinary.equations[w.targetRow]? =
              some ⟨p.root.demand.outputs[r.outIndex].target,.variable right⟩ := by
            simpa only [original] using kept
          pure ⟨⟨w.lowerName,w.upperName,sep.1,sep.2,lower,upper,same.1,same.2,lo.down,hi.down⟩,
            right,w.targetRow,atRow,belowPayload.down,into.down⟩
        else none
      | _ => none
    else none
  else none

theorem actual_root_is_sandwiched_by_independent_names423 {p : Problem} {r : Read p}
    (b : RecordBracket r) (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    InInterval
      (record r.low.label (m.assignment b.lower.field).1 (m.assignment b.lower.residual).1)
      (record r.low.label (m.assignment b.upper.field).1 (m.assignment b.upper.residual).1)
      (m.assignment r.arg.center).1 := by
  have lo := authored_endpoint_has_exact_record422 b.lower m fit
  have hi := authored_endpoint_has_exact_record422 b.upper m fit
  rw [b.lowerLabel] at lo
  rw [b.upperLabel] at hi
  exact ⟨subtype_trans lo.2 (bound_sound m.assignment fit.1 b.belowCenter),
    subtype_trans (bound_sound m.assignment fit.1 b.aboveCenter) hi.1⟩

theorem transported_target_agrees_with_actual_field_channels423 {p : Problem} {r : Read p}
    (w : TransportedRetained r) (m : I72.Model)
    (fit : Models p.state.core.current.ordinary m.assignment) (observed : ProjectedRecordChannels r m) :
    Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 observed.required ∧
    Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 observed.optional := by
  have same : Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1
      (m.assignment w.fieldAddress).1 :=
    fit.2 _ (List.mem_of_getElem? w.stored)
  have below := subtype_trans same.1 (bound_sound m.assignment fit.1 w.toLower)
  have above := subtype_trans (bound_sound m.assignment fit.1 w.fromUpper) same.2
  have bracket := actual_root_is_sandwiched_by_independent_names423 w.bracket m fit
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact subtype_trans below (projected_below r.low.label false (direct ..) observed.atRequired bracket.1)
  · exact subtype_trans (projected_below r.low.label false observed.atRequired (direct ..) bracket.2) above
  · exact subtype_trans below (projected_below r.low.label true (direct ..) observed.atOptional bracket.1)
  · exact subtype_trans (projected_below r.low.label true observed.atOptional (direct ..) bracket.2) above

theorem original_projected_B6_fixed_target_survives_distinct_logical_names423 {p : Problem} {r : Read p}
    (rhs : ProjectedOutput r) (w : TransportedRetained r) (m : I72.Model) (fit : I72.Fits p.state m) :
    ∃ value : Ty,
      rhs.actualRightValue m =
        some (p.root.occurrence,r.ordinal,r.outIndex.val,p.root.demand.outputs[r.outIndex].target,value) ∧
      Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 value := by
  obtain ⟨seen⟩ := same_model_endpoints_support_both_projected_channels422 r m fit.1.1
  exact ⟨seen.required,original_B6_binder_yields_required_projection_and_exact_addresses422 rhs m seen,
    (transported_target_agrees_with_actual_field_channels423 w m fit.1.1 seen).1⟩

def Retained.asTransported423 {p : Problem} {r : Read p} (old : Retained r) :
    TransportedRetained r := by
  let a := old.anchors
  refine ⟨⟨a.lowerName,a.upperName,a.lowerIsNotCenter,a.upperIsNotCenter,a.lower,a.upper,
    a.lowerLabel,a.upperLabel,a.belowCenter,a.aboveCenter⟩,
    a.lower.field,old.rowOrdinal,old.atRow,.refl _,?_⟩
  exact a.sharedField.symm ▸ Bound.refl a.lower.field

/-- A verified target in this narrower fragment entails equality of
the two observed channels. It cannot cover the earlier split-channel
model just by renaming a slot. -/
theorem same_retained_target_forces_channel_agreement423 {p : Problem} {r : Read p}
    (retained : TransportedRetained r) (m : I72.Model)
    (fit : Models p.state.core.current.ordinary m.assignment) (observed : ProjectedRecordChannels r m) :
    Equivalent observed.required observed.optional := by
  have both := transported_target_agrees_with_actual_field_channels423 retained m fit observed
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans ⟨both.1.2,both.1.1⟩ both.2

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
