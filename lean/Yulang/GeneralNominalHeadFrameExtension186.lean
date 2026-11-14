import Yulang.GeneralNominalHeadEquationExtension186

/-! The whole-head extension criterion at the existing actual candidate Frame
interface. Frame supplies finished inspection and all structural alignment;
semantic compatibility remains a check, not a claimed consequence of selection. -/
namespace Yulang.GeneralNominalHeadFrameExtension186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalHeadEquationExtension186 (uses Compatible)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles} {candidate : Plan roles}

theorem frame_finished (frame : Frame registry state.core focus key candidate) :
    GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection candidate) := by
  have prepared := frame.prepared
  rw [← frame.context_eq] at prepared
  obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
  have equal : bounds = candidate.packet.bounds := Option.some.inj (found.symm.trans frame.located)
  subst bounds
  exact GeneralNominalInspectionAlignment.finished_origins candidate.packet.context.state _ candidate.packet.bounds _ _ 0 0 finished

theorem frame_aligned (frame : Frame registry state.core focus key candidate) :
    candidate.packet.declaration.role = candidate.input.occurrence.demand.role := by
  rw [candidate.input_exact,frame.occurrence_eq]
  exact frame.role_eq

theorem frame_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (frame : Frame registry state.core focus key candidate)
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = previous name) ∧
      HeadEquations candidate extended) ↔ Compatible candidate previous :=
  GeneralNominalHeadEquationExtension186.head_equations_extension_iff checked reachable candidate
    frame.center_recorded (frame_aligned frame) frame.context_eq frame.visible (frame_finished frame) previous valid

end Yulang.GeneralNominalHeadFrameExtension186
