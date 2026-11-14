import Yulang.GeneralNominalStructuralEnrichment188
import Yulang.GeneralNominalHeadInitialEffects188

/-! A single structural head argument may contain arbitrarily many mixed
variable/scalar/nominal queries. Nominal descendants are unrestricted. The
initial common model is constructed; output feasibility may use another
eligible frame and assignment, exactly as the selected-class judgment allows. -/
namespace Yulang.GeneralNominalHeadStructuralExtension188
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadCandidates (HeadModels Survivor)
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

def StructuralQuery (candidate : Plan roles) : Prop :=
  ∃ shape patterns, GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration =
      [GeneralNominalInspection.Query.node shape patterns] ∧
    ∀ query ∈ patterns, GeneralNominalMixedOriginEnrichment188.Supported query

theorem initial_projection (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (structural : StructuralQuery candidate) (model : Assignment)
    (branch : HeadModels candidate.packet.registry candidate.packet.context candidate.packet.site.occurrence
      candidate.packet.declaration candidate.packet.bounds model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  have privateModels := ((GeneralNominalHeadBranchFrame187.head_models_exact candidate model).mp branch).1
  have facts := (GeneralNominalPacketSupport.private_exact candidate.packet model).mp privateModels
  have raw := ((GeneralNominalHeadBranchFrame187.head_models_exact candidate model).mp branch).2
  have finished := GeneralNominalInspectionAlignment.finished_origins candidate.packet.context.state _
    candidate.packet.bounds _ (fun _ => none) 0 0
    (GeneralNominalHeadFrameExtension186.frame_finished frame)
  have compatible := facts.2.1
  change GeneralNominalAllocation.Compatible
    (bindings candidate.packet.context.state (inspectMany candidate.packet.context.state _ candidate.packet.bounds (fun _ => none) 0)) model at compatible
  change ProjectionModels candidate.packet.context.state
    (inspectMany candidate.packet.context.state _ candidate.packet.bounds (fun _ => none) 0) model at raw
  obtain ⟨shape,patterns,queries,supported⟩ := structural
  rw [queries] at raw finished compatible
  have length := GeneralNominalInspectionAlignment.finished_length candidate.packet.context.state _ _ _ 0 finished
  simp only [List.length_singleton] at length
  cases located : candidate.packet.bounds with
  | nil => simp [located] at length
  | cons interval rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [located,List.length_cons] at length; omega)
    subst rest
    have point := GeneralNominalHeadPointBounds188.boundary_initial_point_bounds state source candidate frame 0 interval
      (by simp [located])
    obtain ⟨slot,other⟩ := interval
    dsimp only at point
    have same := point.1
    subst other
    simp only [located,inspectMany,GeneralNominalSpineFacts.append_empty] at raw finished compatible
    have result := GeneralNominalStructuralEnrichment188.structural_point candidate.packet.context.state model facts.1
      slot shape patterns supported finished raw compatible
    unfold headInspection
    rw [queries,located]
    simp only [inspectMany,GeneralNominalSpineFacts.append_empty]
    rw [point.2]
    exact result

theorem initial_extension (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (structural : StructuralQuery candidate) :
    ∃ model, Models state model ∧ HeadEquations candidate model ∧
      HeadModels candidate.packet.registry candidate.packet.context candidate.packet.site.occurrence
        candidate.packet.declaration candidate.packet.bounds model ∧
      ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  obtain ⟨model,current,branch⟩ := GeneralNominalHeadInitialCommon188.boundary_initial_common_model state source candidate frame
  obtain ⟨extended,valid,_,head,privateModels,projection⟩ :=
    GeneralNominalHeadBranchFrame187.head_models_extension checked ⟨state,source,.refl⟩ candidate frame model current branch
      (initial_projection source candidate frame structural model branch)
  exact ⟨extended,valid,head,privateModels,projection⟩

theorem selected_effects (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (structural : ∀ candidate, Frame registry state.core root key candidate → StructuralQuery candidate)
    (ready : ∀ candidate, Frame registry state.core root key candidate → EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children := by
    cases old with
    | selected _ unique _ => exact unique
  obtain ⟨candidate,frame,_⟩ := GeneralNominalHeadInitialFrame188.initial_frame state source unique.1
  obtain ⟨model,valid,head,_,_⟩ := initial_extension checked source candidate frame (structural candidate frame)
  exact GeneralNominalCenteredHeadStepAvailability.selected_has_effects old
    ⟨model,valid,⟨children,unique⟩,candidate,frame,ready candidate frame,head⟩

theorem selected_without_outputs (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (structural : ∀ candidate, Frame registry state.core root key candidate → StructuralQuery candidate)
    (empty : root.demand.outputs = []) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  apply selected_effects checked source selected structural
  intro candidate _
  apply GeneralNominalHeadInitialEffects188.empty_effects_ready
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  rw [GeneralNominalHeadInitialEffects188.initial_requests,empty]

end Yulang.GeneralNominalHeadStructuralExtension188
