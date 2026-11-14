import Yulang.GeneralNominalHeadMergeFrame187

/-! A finite extension can retain the existing candidate-private branch model.
This preserves a supplied branch model; existence from preparation is not
identified with an arbitrary current journal model. -/
namespace Yulang.GeneralNominalHeadBranchFrame187
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalHeadEquationExtension186 (uses)
open GeneralNominalHeadMergeFrame187
open GeneralNominalAllocationSupport
open GeneralNominalPacketSupport (Ordinary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem ordinary_iff (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (first last : Assignment)
    (same : ∀ name ∈ support state candidate (uses candidate), first name = last name) :
    Ordinary candidate.packet first ↔ Ordinary candidate.packet last := by
  have atoms (items : List (PresenceNormalForm.Atom Nat))
      (supported : ∀ atom ∈ items, GeneralNominalState.atomSources atom ⊆ support state candidate (uses candidate)) :
      PresenceNormalForm.All CommonNominalFullCarrier.model first items ↔
        PresenceNormalForm.All CommonNominalFullCarrier.model last items := by
    apply forall_congr'; intro atom
    apply forall_congr'; intro member
    exact GeneralNominalCenteredModelExtension.atom_same atom (fun name present => same name (supported atom member present))
  unfold Ordinary
  apply and_congr
  · rw [← GeneralNominalAllocation.cross_exact,← GeneralNominalAllocation.cross_exact]
    exact atoms _ (cross_sources (candidate_endpoints candidate frame))
  · apply and_congr
    · exact merges_iff candidate frame first last same
    · exact atoms _ (checks_sources candidate.packet.context.state _ (candidate_raw_sources candidate frame))

 theorem private_models_iff (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (first last : Assignment)
    (same : ∀ name ∈ support state candidate (uses candidate), first name = last name) :
    GeneralNominalState.Models candidate.packet.privateContext.state first ↔
      GeneralNominalState.Models candidate.packet.privateContext.state last := by
  rw [GeneralNominalPacketSupport.private_exact,GeneralNominalPacketSupport.private_exact]
  apply and_congr
  · exact ⟨GeneralNominalCenteredModelExtension.source_models_same candidate.packet.context.state
        (fun name member => same name (candidate_raw_sources candidate frame member)),
      GeneralNominalCenteredModelExtension.source_models_same candidate.packet.context.state
        (fun name member => (same name (candidate_raw_sources candidate frame member)).symm)⟩
  · exact ordinary_iff candidate frame first last same

 theorem raw_projection_iff (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (first last : Assignment)
    (same : ∀ name ∈ support state candidate (uses candidate), first name = last name) :
    GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
      (GeneralNominalPacketSupport.report candidate.packet) first ↔
    GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
      (GeneralNominalPacketSupport.report candidate.packet) last :=
  GeneralNominalRawFrame179.projection_iff _ _ (fun name member => same name
    (candidate_raw_sources candidate frame (GeneralNominalRawOrigin182.report_sources_subset
      candidate.packet.context candidate.packet.declaration candidate.packet.bounds member)))

 theorem branch_extension (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (branch : GeneralNominalState.Models candidate.packet.privateContext.state model ∧
      GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
        (GeneralNominalPacketSupport.report candidate.packet) model)
    (projection : GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
      (GeneralNominalQueryProvenance183.headInspection candidate) model) :
    ∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended ∧
      GeneralNominalState.Models candidate.packet.privateContext.state extended ∧
      GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
        (GeneralNominalPacketSupport.report candidate.packet) extended ∧
      GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
        (GeneralNominalQueryProvenance183.headInspection candidate) extended := by
  have ordinary := ((GeneralNominalPacketSupport.private_exact candidate.packet model).mp branch.1).2
  obtain ⟨extended,models,kept,head,projected,_⟩ := extension_retains_inspection checked reachable candidate
    frame model valid projection ordinary.2.1
  exact ⟨extended,models,kept,head,(private_models_iff candidate frame extended model kept).mpr branch.1,
    (raw_projection_iff candidate frame extended model kept).mpr branch.2,projected⟩

 theorem head_models_exact (candidate : Plan roles) (model : Assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ↔
    GeneralNominalState.Models candidate.packet.privateContext.state model ∧
      GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
        (GeneralNominalPacketSupport.report candidate.packet) model := Iff.rfl

 theorem head_models_extension (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model)
    (projection : GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
      (GeneralNominalQueryProvenance183.headInspection candidate) model) :
    ∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
        (GeneralNominalQueryProvenance183.headInspection candidate) extended := by
  obtain ⟨extended,models,kept,head,privateModels,raw,centered⟩ := branch_extension checked reachable candidate
    frame model valid ((head_models_exact candidate model).mp branch) projection
  exact ⟨extended,models,kept,head,(head_models_exact candidate extended).mpr ⟨privateModels,raw⟩,centered⟩

end Yulang.GeneralNominalHeadBranchFrame187
