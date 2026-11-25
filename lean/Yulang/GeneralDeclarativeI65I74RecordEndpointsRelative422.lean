import Yulang.GeneralDeclarativeI65I74RecordEndpointsControl422
import Yulang.GeneralDeclarativeRecordNames330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent mask)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (projected_below direct)
open GeneralDeclarativeOpaqueNames328 (kept first second extend left_value right_value unchanged)
open GeneralDeclarativeRecordNames330 (expose lifts Agreement model_exact)
open GeneralDeclarativeRecordReconstruct330 (reconstruct)

def Read.protected {p} (r : Read p) : List Nat :=
  [r.low.field,r.high.field,r.low.residual,r.high.residual] ++
    p.root.demand.outputs.map (·.target)

def Read.fieldNames {p} (r : Read p) : Capture :=
  ⟨r.low.field,first p.state.core.current.ordinary r.arg.center r.protected,r.high.field⟩

def Read.freshTail {p} (r : Read p) : Nat :=
  second p.state.core.current.ordinary r.arg.center r.protected

/-- Relative model extension has an exact agreement criterion. It is
*not* an evidence-producing operation on the original State: it adds
a row to a separate ordinary state and quantifies over a new assignment.
It preserves every original equation's footprint and fixed output names. -/
theorem fresh_record_model_extension_exactly_when_channels_agree422 {p}
    (r : Read p) (m : I72.Model) :
    (∃ next : Assignment,
      Models (expose p.state.core.current.ordinary r.arg.center r.low.label r.protected) next ∧
      (∀ n ∈ kept p.state.core.current.ordinary r.arg.center r.protected, next n = m.assignment n)) ↔
    Models p.state.core.current.ordinary m.assignment ∧
      Agreement r.low.label (m.assignment r.arg.center).1 := by
  apply model_exact r.low.label r.protected m.assignment r.ranged
    (lo := .variable r.low.field) (loRest := .variable r.low.residual)
    (hi := .variable r.high.field) (hiRest := .variable r.high.residual)
  · exact fun m fit => fit.2 _ r.low.row
  · intro m fit
    have high := fit.2 _ r.high.row
    rw [r.sameLabel] at high
    exact high

/-- Under separate channel agreement, a relative extension gives
the original low/high field names with a fresh *actual* projection
name, protects each original result target, and sets the fresh
residual to the actual mask. Neither fresh symbolic name is claimed
as present or authored in the old State. -/
theorem relative_extension_keeps_real_field_triple_and_fixed_addresses422 {p}
    (r : Read p) (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment)
    (matched : Agreement r.low.label (m.assignment r.arg.center).1) :
    ∃ next : Assignment,
      Models (expose p.state.core.current.ordinary r.arg.center r.low.label r.protected) next ∧
      project r.low.label false [] (m.assignment r.arg.center).1 =
        some (next r.fieldNames.center).1 ∧
      (next r.fieldNames.lower).1 = (m.assignment r.low.field).1 ∧
      (next r.fieldNames.upper).1 = (m.assignment r.high.field).1 ∧
      InInterval (next r.fieldNames.lower).1 (next r.fieldNames.upper).1
        (next r.fieldNames.center).1 ∧
      (next r.freshTail).1 = mask [r.low.label] (m.assignment r.arg.center).1 ∧
      (∀ out ∈ p.root.demand.outputs, next out.target = m.assignment out.target) := by
  obtain ⟨v,opt,required,optional,same⟩ := matched
  have interval := original_center_between_authored_record_endpoints422 r m fit
  let tail := mask [r.low.label] (m.assignment r.arg.center).1
  let raw := p.state.core.current.ordinary
  let next := extend raw r.arg.center r.protected m.assignment v tail
  have exactShape := reconstruct interval.1 interval.2 required optional same
  obtain ⟨model,unchangedAll⟩ := lifts r.arg.center r.low.label r.protected m.assignment fit exactShape
  have firstActual : (next r.fieldNames.center).1 = v := by apply left_value
  have lastActual : (next r.freshTail).1 = tail := by apply right_value
  have lowEq : next r.fieldNames.lower = m.assignment r.low.field := by
    apply unchangedAll
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
  have highEq : next r.fieldNames.upper = m.assignment r.high.field := by
    apply unchangedAll
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  refine ⟨next,model,firstActual.symm ▸ required,congrArg Prod.fst lowEq,congrArg Prod.fst highEq,?_,lastActual,?_⟩
  · rw [lowEq,highEq,firstActual]
    exact ⟨projected_below r.low.label false (direct ..) required interval.1,
      projected_below r.low.label false required (direct ..) interval.2⟩
  · intro out onList
    apply unchangedAll
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨out,onList,rfl⟩)))

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
