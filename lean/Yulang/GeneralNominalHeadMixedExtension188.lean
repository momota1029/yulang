import Yulang.GeneralNominalMixedOriginEnrichment188
import Yulang.GeneralNominalHeadInitialEffects188

/-! Initial mixed variable/scalar/nominal heads have a real common model.
Nominal descendants are unrestricted; repeated names across different root
forms retain their cross constraints. Structural top roots remain excluded. -/
namespace Yulang.GeneralNominalHeadMixedExtension188
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

def SupportedQueries (candidate : Plan roles) : Prop :=
  ∀ query ∈ GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration,
    GeneralNominalMixedOriginEnrichment188.Supported query

theorem initial_projection (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (supported : SupportedQueries candidate) (model : Assignment)
    (branch : HeadModels candidate.packet.registry candidate.packet.context candidate.packet.site.occurrence
      candidate.packet.declaration candidate.packet.bounds model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  have privateModels := ((GeneralNominalHeadBranchFrame187.head_models_exact candidate model).mp branch).1
  have sourceModel := ((GeneralNominalPacketSupport.private_exact candidate.packet model).mp privateModels).1
  have raw := ((GeneralNominalHeadBranchFrame187.head_models_exact candidate model).mp branch).2
  have finished := GeneralNominalInspectionAlignment.finished_origins candidate.packet.context.state _
    candidate.packet.bounds _ (fun _ => none) 0 0
    (GeneralNominalHeadFrameExtension186.frame_finished frame)
  change ProjectionModels candidate.packet.context.state
    (inspectMany candidate.packet.context.state _ candidate.packet.bounds (fun _ => none) 0) model at raw
  unfold headInspection
  have cross := ((GeneralNominalPacketSupport.private_exact candidate.packet model).mp privateModels).2.1
  apply GeneralNominalMixedOriginEnrichment188.mixed_many _ model sourceModel _ supported
    candidate.packet.bounds _ 0 ?_ finished raw cross
  intro index interval found
  simpa only [Nat.zero_add] using
    GeneralNominalHeadPointBounds188.boundary_initial_point_bounds state source candidate frame index interval found

theorem initial_extension (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (supported : SupportedQueries candidate) :
    ∃ model, Models state model ∧ HeadEquations candidate model ∧
      HeadModels candidate.packet.registry candidate.packet.context candidate.packet.site.occurrence
        candidate.packet.declaration candidate.packet.bounds model ∧
      ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  obtain ⟨model,current,branch⟩ := GeneralNominalHeadInitialCommon188.boundary_initial_common_model state source candidate frame
  obtain ⟨extended,valid,_,head,privateModels,projection⟩ :=
    GeneralNominalHeadBranchFrame187.head_models_extension checked ⟨state,source,.refl⟩ candidate frame model current branch
      (initial_projection source candidate frame supported model branch)
  exact ⟨extended,valid,head,privateModels,projection⟩

theorem selected_effects (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (supported : ∀ candidate, Frame registry state.core root key candidate → SupportedQueries candidate)
    (ready : ∀ candidate, Frame registry state.core root key candidate → EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children := by
    cases old with
    | selected _ unique _ => exact unique
  obtain ⟨candidate,frame,_⟩ := GeneralNominalHeadInitialFrame188.initial_frame state source unique.1
  obtain ⟨model,valid,head,_,_⟩ := initial_extension checked source candidate frame (supported candidate frame)
  exact GeneralNominalCenteredHeadStepAvailability.selected_has_effects old
    ⟨model,valid,⟨children,unique⟩,candidate,frame,ready candidate frame,head⟩

theorem selected_without_outputs (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (supported : ∀ candidate, Frame registry state.core root key candidate → SupportedQueries candidate)
    (empty : root.demand.outputs = []) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  apply selected_effects checked source selected supported
  intro candidate _
  apply GeneralNominalHeadInitialEffects188.empty_effects_ready
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  rw [GeneralNominalHeadInitialEffects188.initial_requests,empty]

/-- A syntactic condition on visible declarations, independent of frames,
assignments, selection, and successful installation. -/
def RegistrySupported (registry : Registry) (context : GeneralNominalCandidates.Context)
    (role : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.role = role →
    ∀ query ∈ GeneralNominalInspection.queries context.state context.interpretation declaration,
      GeneralNominalMixedOriginEnrichment188.Supported query

theorem selected_registry_effects (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (heads : RegistrySupported registry state.core.erased.current.context root.demand.role)
    (empty : root.demand.outputs = []) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  apply selected_without_outputs checked source selected ?_ empty
  intro candidate frame
  have supported := heads candidate.packet.declaration frame.visible frame.role_eq
  intro query member
  rw [frame.context_eq] at member
  exact supported query member

end Yulang.GeneralNominalHeadMixedExtension188
