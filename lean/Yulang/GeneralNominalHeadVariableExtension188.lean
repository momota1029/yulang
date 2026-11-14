import Yulang.GeneralNominalHeadPointBounds188
import Yulang.GeneralNominalPointProjection188
import Yulang.GeneralNominalHeadInitialFrame188

/-! Initial variable-only heads have a jointly valid current, private and
centered model, even with repeated names. Query shape is an explicit restriction;
this is not the arbitrary-head or generated-child EvidenceNode theorem. -/
namespace Yulang.GeneralNominalHeadVariableExtension188
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadCandidates (HeadModels Survivor)
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

def VariableQueries (candidate : Plan roles) : Prop :=
  ∃ names : List (List Nat),
    GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration =
      names.map GeneralNominalInspection.Query.variables

theorem initial_projection (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (variables : VariableQueries candidate) (model : Assignment)
    (branch : HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  have ordinary := ((GeneralNominalPacketSupport.private_exact candidate.packet model).mp
    ((GeneralNominalHeadBranchFrame187.head_models_exact candidate model).mp branch).1).2
  have cross := ordinary.1
  rw [← GeneralNominalHeadProjectionBounds187.head_bindings candidate] at cross
  apply GeneralNominalPointProjection188.point_projection _ _ ?_ model cross
  obtain ⟨names,queries⟩ := variables
  unfold headInspection
  rw [queries]
  apply GeneralNominalPointProjection188.point_many
  intro index interval found
  simpa only [Nat.zero_add] using
    GeneralNominalHeadPointBounds188.boundary_initial_point_bounds state source candidate frame index interval found

theorem initial_extension (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (variables : VariableQueries candidate) :
    ∃ model, Models state model ∧ HeadEquations candidate model ∧
      HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
      ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  obtain ⟨model,current,branch⟩ := GeneralNominalHeadInitialCommon188.boundary_initial_common_model
    state source candidate frame
  have reachable : B4TargetV6.Reachable (boundary roles) registry root state := ⟨state,source,.refl⟩
  obtain ⟨extended,valid,_,head,privateModels,projection⟩ :=
    GeneralNominalHeadBranchFrame187.head_models_extension checked reachable candidate frame model current branch
      (initial_projection source candidate frame variables model branch)
  exact ⟨extended,valid,head,privateModels,projection⟩

/-- Head shape is required for every eligible frame, but no frame or common
assignment is supplied. The real survivor constructs the frame itself. -/
theorem survivor_extension (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (survivor : Survivor registry state.core.erased.current.context root key children)
    (variables : ∀ candidate, Frame registry state.core root key candidate → VariableQueries candidate) :
    ∃ candidate : Plan roles, ∃ model,
      Frame registry state.core root key candidate ∧ candidate.packet.children = children ∧
      Models state model ∧ HeadEquations candidate model ∧
      HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
      ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  obtain ⟨candidate,frame,kids⟩ := GeneralNominalHeadInitialFrame188.initial_frame state source survivor
  obtain ⟨model,valid,head,branch,projection⟩ := initial_extension checked source candidate frame (variables candidate frame)
  exact ⟨candidate,model,frame,kids,valid,head,branch,projection⟩

end Yulang.GeneralNominalHeadVariableExtension188
