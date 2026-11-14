import Yulang.GeneralNominalCaptureOrigins187
import Yulang.GeneralNominalSchemaCapture187
import Yulang.GeneralNominalHeadRawBounds187

/-! The remaining Fits obligation follows from independent centered inspection
projections and recorded merge equations. These model premises are explicit. -/
namespace Yulang.GeneralNominalHeadProjectionBounds187
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalHeadEquationExtension186 (uses uses_mem)
open GeneralNominalHeadRevisitExtension186 (BoundsFit)
open GeneralNominalHeadConservativeExtension186 (support)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem head_bindings (candidate : Plan roles) :
    bindings candidate.packet.context.state (headInspection candidate) = candidate.packet.bindings :=
  GeneralNominalCaptureOrigins187.many_bindings candidate.packet.context.state _ candidate.packet.bounds _ _ 0 0

 theorem projection_bounds (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (model : Assignment)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    BoundsFit candidate model := by
  intro index value seen
  obtain ⟨captured,present,name,origin⟩ := GeneralNominalSchemaCapture187.schemas_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0
    (GeneralNominalHeadFrameExtension186.frame_finished frame) (uses candidate index) (uses_mem candidate index)
  have declared : captured.name ∈ candidate.packet.declaration.inputNames :=
    name ▸ GeneralNominalHeadSchemaNames186.head_input candidate _ (uses_mem candidate index)
  have recorded := merges
  rw [← head_bindings candidate] at recorded
  have fits := GeneralNominalCaptureBounds187.projected_merged candidate.packet.context.state
    (headInspection candidate) candidate.packet.registry candidate.packet.site.occurrence.identity
    candidate.packet.declaration model projection recorded captured present declared
    (uses candidate index).origin origin value seen
  simpa only [head_bindings,name] using fits

 theorem revisit_extension_of_projection (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    ∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended :=
  (GeneralNominalHeadRevisitExtension186.revisit_extension_iff_bounds checked reachable historical
    candidate member frame identity declaration model valid).mpr (projection_bounds candidate frame model projection merges)

end Yulang.GeneralNominalHeadProjectionBounds187
