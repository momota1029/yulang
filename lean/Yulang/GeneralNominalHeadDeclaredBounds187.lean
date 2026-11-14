import Yulang.GeneralNominalHeadRawBounds187

/-! All declared input names, not only a selected use index, are covered.
The criterion remains conditional on actual recorded merge equations. -/
namespace Yulang.GeneralNominalHeadDeclaredBounds187
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadEquationExtension186 (uses uses_mem uses_cover)
open GeneralNominalHeadRawBounds187
open GeneralNominalHeadConservativeExtension186 (support)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem frame_name_use (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate)
    (name : Nat) (declared : name ∈ candidate.packet.declaration.inputNames) :
    ∃ index, (uses candidate index).name = name := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    candidate.packet.context.state candidate.packet.context.interpretation candidate.packet.declaration
    candidate.packet.bounds _ 0 (GeneralNominalHeadFrameExtension186.frame_finished frame) name declared
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 captured present
  obtain ⟨index,same⟩ := uses_cover candidate ⟨captured.name,origin,.actual⟩ used
  exact ⟨index,(congrArg GeneralNominalMaterialization.Use.name same).trans equal⟩

 def DeclaredRawFits (historical candidate : Plan roles) (model : Assignment) : Prop :=
  ∀ name ∈ candidate.packet.declaration.inputNames,
    ∀ captured ∈ (GeneralNominalPacketSupport.report candidate.packet).captures,
      captured.name = name →
      GeneralNominalRecursiveInspection.Fits candidate.packet.context.state model captured.bounds
        (model (historical.binder name)).1

 theorem raw_iff_declared (historical candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (model : Assignment) :
    RawHistoricalFits historical candidate model ↔ DeclaredRawFits historical candidate model := by
  constructor
  · intro raw name declared
    obtain ⟨index,equal⟩ := frame_name_use candidate frame name declared
    simpa only [equal] using raw index
  · intro raw index
    exact raw _ (GeneralNominalHeadSchemaNames186.head_input candidate _ (uses_mem candidate index))

 theorem revisit_extension_iff_declared (checked : Checked registry)
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
      HeadEquations candidate extended) ↔ DeclaredRawFits historical candidate model :=
  (revisit_extension_iff_raw checked reachable historical candidate member frame identity declaration model valid merges).trans
    (raw_iff_declared historical candidate frame model)

end Yulang.GeneralNominalHeadDeclaredBounds187
