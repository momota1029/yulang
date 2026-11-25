import Yulang.GeneralDeclarativeI65I74ProjectedRetentionPath423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open RecordEndpoints422 (Read ProjectedRecordChannels ProjectedOutput
  same_model_endpoints_support_both_projected_channels422
  original_B6_binder_yields_required_projection_and_exact_addresses422)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open CommonNominalFullCarrier (Ty Subtype Equivalent record)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open Checker408 (Problem)

def fieldShape (label field : Nat) : TyTerm Nat :=
  .record label (.var field) .exactEmpty

def requiredLower (label field root : Nat) : Atom Nat :=
  .tyLe (.inter (fieldShape label field) .exactEmpty) (.var root)

def requiredUpper (label field root : Nat) : Atom Nat :=
  .tyLe (.var root) (fieldShape label field)

/-- A different retained ordinary proof for the *required* projection.
Its lower side may itself have unequal required/optional channels.
There is no necessity to impose optional-channel agreement merely
to certify an associated output that uses the required field. -/
structure RequiredOnlyRetained {p : Problem} (r : Read p) where
  field : Nat
  targetOrdinal : Nat
  lowerOrdinal : Nat
  upperOrdinal : Nat
  atTarget : p.state.core.current.ordinary.equations[targetOrdinal]? =
    some ⟨p.root.demand.outputs[r.outIndex].target,.variable field⟩
  atLower : p.state.core.current.ordinary.normal.ordinary[lowerOrdinal]? =
    some (requiredLower r.low.label field r.arg.center)
  atUpper : p.state.core.current.ordinary.normal.ordinary[upperOrdinal]? =
    some (requiredUpper r.low.label field r.arg.center)

structure ChannelWire where
  targetOrdinal : Nat
  lowerOrdinal : Nat
  upperOrdinal : Nat

/-- Locate, shape-check and align the actual original ordinary rows.
No predicate about a model's projected value is encoded in the wire. -/
def readRequiredChannelRetention423 {p : Problem} (r : Read p) (w : ChannelWire) :
    Option (RequiredOnlyRetained r) := do
  let raw := p.state.core.current.ordinary
  match target : raw.equations[w.targetOrdinal]? with
  | some ⟨lhs,.variable f⟩ =>
    match lo : raw.normal.ordinary[w.lowerOrdinal]? with
    | some (.tyLe (.inter (.record lowKey (.var lowField) .exactEmpty) .exactEmpty) (.var lowCenter)) =>
      match hi : raw.normal.ordinary[w.upperOrdinal]? with
      | some (.tyLe (.var highCenter) (.record highKey (.var highField) .exactEmpty)) =>
        if relation : lhs = p.root.demand.outputs[r.outIndex].target ∧
          lowKey = r.low.label ∧ highKey = r.low.label ∧ lowField = f ∧ highField = f ∧
          lowCenter = r.arg.center ∧ highCenter = r.arg.center then
          have foundTarget : raw.equations[w.targetOrdinal]? =
              some ⟨p.root.demand.outputs[r.outIndex].target,.variable f⟩ := by
            simpa only [relation.1] using target
          have foundLower : raw.normal.ordinary[w.lowerOrdinal]? =
              some (requiredLower r.low.label f r.arg.center) := by
            simpa only [requiredLower,fieldShape,relation.2.1,relation.2.2.2.1,
              relation.2.2.2.2.2.1] using lo
          have foundUpper : raw.normal.ordinary[w.upperOrdinal]? =
              some (requiredUpper r.low.label f r.arg.center) := by
            simpa only [requiredUpper,fieldShape,relation.2.2.1,relation.2.2.2.2.1,
              relation.2.2.2.2.2.2] using hi
          pure ⟨f,w.targetOrdinal,w.lowerOrdinal,w.upperOrdinal,foundTarget,foundLower,foundUpper⟩
        else none
      | _ => none
    | _ => none
  | _ => none

theorem tightened_required_lower_has_the_expected_real_projection423 (label : Nat) (v : Ty) :
    project label false [] (.inter (record label v .exactEmpty) .exactEmpty) = some v := by
  simp [project,direct,GeneralDeclarativeOpaqueChannel328.meet]

theorem retained_target_can_equal_required_projection_without_collapsing_optional423
    {p : Problem} {r : Read p} (w : RequiredOnlyRetained r) (m : I72.Model)
    (fit : Models p.state.core.current.ordinary m.assignment) (a : ProjectedRecordChannels r m) :
    Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 a.required := by
  have lo := fit.1.1 _ (List.mem_of_getElem? w.atLower)
  have hi := fit.1.1 _ (List.mem_of_getElem? w.atUpper)
  change Subtype (.inter (record r.low.label (m.assignment w.field).1 .exactEmpty) .exactEmpty)
    (m.assignment r.arg.center).1 at lo
  change Subtype (m.assignment r.arg.center).1 (record r.low.label (m.assignment w.field).1 .exactEmpty) at hi
  have stored : Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 (m.assignment w.field).1 :=
    fit.2 _ (List.mem_of_getElem? w.atTarget)
  exact eqv_trans stored
    ⟨projected_below r.low.label false (tightened_required_lower_has_the_expected_real_projection423 ..)
      a.atRequired lo,
      projected_below r.low.label false a.atRequired (direct ..) hi⟩

theorem original_B6_projected_write_retained_even_without_optional_agreement423
    {p : Problem} {r : Read p} (rhs : ProjectedOutput r) (w : RequiredOnlyRetained r)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    ∃ value : Ty,
      rhs.actualRightValue m =
        some (p.root.occurrence,r.ordinal,r.outIndex.val,p.root.demand.outputs[r.outIndex].target,value) ∧
      Equivalent (m.assignment p.root.demand.outputs[r.outIndex].target).1 value := by
  obtain ⟨a⟩ := same_model_endpoints_support_both_projected_channels422 r m fit.1.1
  exact ⟨a.required,original_B6_binder_yields_required_projection_and_exact_addresses422 rhs m a,
    retained_target_can_equal_required_projection_without_collapsing_optional423 w m fit.1.1 a⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
