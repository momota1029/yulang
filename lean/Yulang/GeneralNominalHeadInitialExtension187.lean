import Yulang.GeneralNominalHeadProjectionBounds187
import Yulang.GeneralNominalSchemaTests187
import Yulang.GeneralNominalCaptureAnchors

/-! Arbitrary current candidates, including plans not previously installed,
have conservative head extensions from centered projection models and merge
constraints. No historical plan or previously installed binder is required. -/
namespace Yulang.GeneralNominalHeadInitialExtension187
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalHeadEquationExtension186 (uses uses_mem Compatible)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalHeadBinderCollisions186 (point_fits point_binder nonpoint_name)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem projection_compatible
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core focus key candidate)
    (model : Assignment)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    Compatible candidate model := by
  have finished := GeneralNominalHeadFrameExtension186.frame_finished frame
  have witness := fun index => GeneralNominalSchemaCapture187.schemas_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 finished (uses candidate index) (uses_mem candidate index)
  have bounds := GeneralNominalHeadProjectionBounds187.projection_bounds candidate frame model projection merges
  refine ⟨?_,?_,bounds,?_⟩
  · intro test member
    have found := GeneralNominalSchemaTests187.schemas_tests candidate.packet.context.state _
      candidate.packet.bounds _ 0 finished test member
    obtain ⟨interval,anchor⟩ := found.2
    exact ⟨(projection.1 _ anchor).1,projection.2.1 test found.1⟩
  · intro index
    obtain ⟨captured,present,_,origin⟩ := witness index
    exact (projection.1 _ (GeneralNominalCaptureAnchors.many_anchored candidate.packet.context.state _
      candidate.packet.bounds _ 0 captured present _ origin)).1
  · intro i j first last same one two
    have inputA := GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i)
    have inputB := GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate j)
    by_cases pointA : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate i).name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate i).name).2
    · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).2
      · have a := point_fits candidate _ inputA pointA model first (bounds i first one)
        have b := point_fits candidate _ inputB pointB model last (bounds j last two)
        rw [same] at a
        exact ⟨subtype_trans a.1 b.2,subtype_trans b.1 a.2⟩
      · exact False.elim ((GeneralNominalHeadCandidateSupport186.nonpoint_binder_endpoints_separate
          reachable candidate frame.context_eq _ inputB pointB (uses candidate i).name).1
          (same.symm.trans (point_binder candidate _ inputA pointA)))
    · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).2
      · exact False.elim ((GeneralNominalHeadCandidateSupport186.nonpoint_binder_endpoints_separate
          reachable candidate frame.context_eq _ inputA pointA (uses candidate j).name).1
          (same.trans (point_binder candidate _ inputB pointB)))
      · have names := nonpoint_name candidate _ _ inputA inputB pointA pointB same
        obtain ⟨a,ap,an,ao⟩ := witness i
        obtain ⟨b,bp,bn,bo⟩ := witness j
        exact projection.2.2.2 a ap b bp (an.trans (names.trans bn.symm))
          _ _ ao bo first last one two

 theorem frame_extension_of_projection (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    ∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended :=
  (GeneralNominalHeadFrameExtension186.frame_extension_iff checked reachable frame model valid).mpr
    (projection_compatible reachable candidate frame model projection merges)

end Yulang.GeneralNominalHeadInitialExtension187
