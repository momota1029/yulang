import Yulang.GeneralNominalCaptureBounds187
import Yulang.GeneralNominalHeadRevisitExtension186
import Yulang.GeneralNominalCompleteNames183

/-! Exact raw capture criterion for a historical candidate's conservative
head extension. Merge equations are explicit; readiness is not universal validity. -/
namespace Yulang.GeneralNominalHeadRawBounds187
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalRecursiveInspection (Observes Finished)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadEquationExtension186 (uses uses_mem)
open GeneralNominalHeadRevisitExtension186 (BoundsFit)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalCaptureBounds187
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem frame_occurrences_nonempty (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate)
    (name : Nat) (declared : name ∈ candidate.packet.declaration.inputNames) :
    GeneralNominalAllocation.occurrences candidate.packet.bindings name ≠ [] := by
  have finished := GeneralNominalHeadFrameExtension186.frame_finished frame
  have raw := GeneralNominalInspectionAlignment.finished_origins candidate.packet.context.state _
    candidate.packet.bounds _ (fun _ => none) 0 0 finished
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    candidate.packet.context.state candidate.packet.context.interpretation candidate.packet.declaration
    candidate.packet.bounds (fun _ => none) 0 raw name declared
  subst name
  exact occurrence_nonempty candidate.packet.context.state
    (GeneralNominalPacketSupport.report candidate.packet) captured present

 def RawHistoricalFits (historical candidate : Plan roles) (model : Assignment) : Prop :=
  ∀ index, ∀ captured ∈ (GeneralNominalPacketSupport.report candidate.packet).captures,
    captured.name = (uses candidate index).name →
    GeneralNominalRecursiveInspection.Fits candidate.packet.context.state model captured.bounds
      (model (historical.binder (uses candidate index).name)).1

 theorem bounds_iff_raw (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    BoundsFit candidate model ↔ RawHistoricalFits historical candidate model := by
  have actual := fun index => GeneralNominalHeadCandidateSemantic186.candidate_actual checked reachable
    historical candidate member frame.center_recorded identity frame.context_eq declaration
    (uses candidate index) (uses_mem candidate index)
    (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate index)) model valid
  have expand := fun index => merged_iff_raw candidate.packet.context.state
    (GeneralNominalPacketSupport.report candidate.packet) candidate.packet.registry
    candidate.packet.site.occurrence.identity candidate.packet.declaration model merges
    (uses candidate index).name
    (GeneralNominalHeadSchemaNames186.head_input candidate _ (uses_mem candidate index))
    (frame_occurrences_nonempty candidate frame _
      (GeneralNominalHeadSchemaNames186.head_input candidate _ (uses_mem candidate index)))
    (model (historical.binder (uses candidate index).name)).1
  constructor
  · intro fits index
    obtain ⟨value,seen⟩ := (actual index).1
    apply (expand index).mp
    exact (fits_equivalent model _ value _
      ((actual index).2.2 value _ seen (.source _))).mp (fits index value seen)
  · intro raw index value seen
    exact (fits_equivalent model _ value _
      ((actual index).2.2 value _ seen (.source _))).mpr ((expand index).mpr (raw index))

 theorem revisit_extension_iff_raw (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended) ↔ RawHistoricalFits historical candidate model := by
  rw [GeneralNominalHeadRevisitExtension186.revisit_extension_iff_bounds checked reachable historical
    candidate member frame identity declaration model valid]
  exact bounds_iff_raw checked reachable historical candidate member frame identity declaration model valid merges

end Yulang.GeneralNominalHeadRawBounds187
