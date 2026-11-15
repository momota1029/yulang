import Yulang.GeneralNominalCaptureBounds187
import Yulang.GeneralNominalCaptureOrigins187
import Yulang.GeneralNominalSchemaCapture187
import Yulang.GeneralDictionaryDefaultRevisit214
import Yulang.GeneralDictionaryDefaultRawBranch214

/-! The remaining Fits obligation follows from independent centered inspection
projections and recorded merge equations. These model premises are explicit. -/
namespace Yulang.GeneralDictionaryDefaultProjectionBounds215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralDictionaryDefaultHeadEquationExtension214 (uses uses_mem)
open GeneralDictionaryDefaultRevisit214 (BoundsFit)
open GeneralDictionaryDefaultConservative214 (support)
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
    (GeneralDictionaryDefaultRevisit214.frame_finished frame) (uses candidate index) (uses_mem candidate index)
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
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
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
  (GeneralDictionaryDefaultRevisit214.revisit_extension_iff_bounds checked source bound path historical
    candidate member frame identity declaration model valid).mpr (projection_bounds candidate frame model projection merges)

 theorem revisit_branch_of_projection (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    ∃ extended, (Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended) ∧
      (∀ name ∈ GeneralDictionaryDefaultRawBranch214.support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended := by
   apply (GeneralDictionaryDefaultRawBranch214.head_and_branch_extension_iff checked source bound path
     candidate frame (GeneralDictionaryDefaultRevisit214.frame_finished frame) model valid branch).mpr
   exact (GeneralDictionaryDefaultRevisit214.compatible_iff_bounds checked source bound path historical candidate
     member frame identity declaration model valid).mpr (projection_bounds candidate frame model projection merges)

end Yulang.GeneralDictionaryDefaultProjectionBounds215
